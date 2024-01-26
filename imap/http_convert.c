/* http_convert.c -- Routines for converting media types over HTTP
 *
 * Copyright (c) 1994-2023 Carnegie Mellon University.  All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in
 *    the documentation and/or other materials provided with the
 *    distribution.
 *
 * 3. The name "Carnegie Mellon University" must not be used to
 *    endorse or promote products derived from this software without
 *    prior written permission. For permission or any legal
 *    details, please contact
 *      Carnegie Mellon University
 *      Center for Technology Transfer and Enterprise Creation
 *      4615 Forbes Avenue
 *      Suite 302
 *      Pittsburgh, PA  15213
 *      (412) 268-7393, fax: (412) 268-7395
 *      innovation@andrew.cmu.edu
 *
 * 4. Redistributions of any form whatsoever must retain the following
 *    acknowledgment:
 *    "This product includes software developed by Computing Services
 *     at Carnegie Mellon University (http://www.cmu.edu/computing/)."
 *
 * CARNEGIE MELLON UNIVERSITY DISCLAIMS ALL WARRANTIES WITH REGARD TO
 * THIS SOFTWARE, INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY
 * AND FITNESS, IN NO EVENT SHALL CARNEGIE MELLON UNIVERSITY BE LIABLE
 * FOR ANY SPECIAL, INDIRECT OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN
 * AN ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING
 * OUT OF OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

#include <config.h>

#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif
#include <ctype.h>
#include <string.h>
#include <syslog.h>
#include <assert.h>

#include "acl.h"
#include "annotate.h"
#include "charset.h"
#include "global.h"
#include "httpd.h"
#include "http_proxy.h"
#include "jmap_ical.h"
#include "mailbox.h"
#include "map.h"
#include "mboxlist.h"
#include "message.h"
#include "parseaddr.h"
#include "proxy.h"
#include "times.h"
#include "seen.h"
#include "tok.h"
#include "util.h"
#include "version.h"
#include "wildmat.h"
#include "xmalloc.h"
#include "xstrlcpy.h"

/* generated headers are not necessarily in current directory */
#include "imap/http_err.h"
#include "imap/imap_err.h"

static void convert_init(struct buf *serverinfo);
static int meth_post(struct transaction_t *txn, void *params);

struct namespace_t namespace_convert = {
    URL_NS_DEFAULT, 0, "convert", "/convert", NULL,
    http_allow_noauth_get, /*authschemes*/0,
    /*mbtype*/0,
    ALLOW_POST,
    convert_init, NULL, NULL, NULL, NULL,
    {
        { NULL,                 NULL },                 /* ACL          */
        { NULL,                 NULL },                 /* BIND         */
        { NULL,                 NULL },                 /* CONNECT      */
        { NULL,                 NULL },                 /* COPY         */
        { NULL,                 NULL },                 /* DELETE       */
        { NULL,                 NULL },                 /* GET          */
        { NULL,                 NULL },                 /* HEAD         */
        { NULL,                 NULL },                 /* LOCK         */
        { NULL,                 NULL },                 /* MKCALENDAR   */
        { NULL,                 NULL },                 /* MKCOL        */
        { NULL,                 NULL },                 /* MOVE         */
        { NULL,                 NULL },                 /* OPTIONS      */
        { NULL,                 NULL },                 /* PATCH        */
        { &meth_post,           NULL },                 /* POST         */
        { NULL,                 NULL },                 /* PROPFIND     */
        { NULL,                 NULL },                 /* PROPPATCH    */
        { NULL,                 NULL },                 /* PUT          */
        { NULL,                 NULL },                 /* REPORT       */
        { NULL,                 NULL },                 /* SEARCH       */
        { NULL,                 NULL },                 /* TRACE        */
        { NULL,                 NULL },                 /* UNBIND       */
        { NULL,                 NULL }                  /* UNLOCK       */
    }
};


static void convert_init(struct buf *serverinfo __attribute__((unused)))
{
    namespace_convert.enabled = config_httpmodules & IMAP_ENUM_HTTPMODULES_CONVERT;
}

static int convert_parse_path(const char *path, struct request_target_t *tgt,
                              const char **resultstr)
{
    size_t len;
    char *p;

    if (*tgt->path) return 0;  /* Already parsed */

    /* Make a working copy of target path */
    strlcpy(tgt->path, path, sizeof(tgt->path));
    p = tgt->path;

    /* Sanity check namespace */
    len = strlen(namespace_convert.prefix);
    if (strlen(p) < len ||
        strncmp(namespace_convert.prefix, p, len) ||
        (path[len] && path[len] != '/')) {
        *resultstr = "Namespace mismatch request target path";
        return HTTP_FORBIDDEN;
    }

    /* Always allow read, even if no content */
    tgt->allow = ALLOW_READ;

    /* Skip namespace */
    p += len;

    /* Check for path after prefix */
    if (*p == '/') p++;
    if (*p) return HTTP_NOT_FOUND;

    tgt->allow |= ALLOW_POST;

    return 0;
}

/* Perform a POST request */
static int meth_post(struct transaction_t *txn,
                     void *params __attribute__((unused)))
{
    icalcomponent *ical = NULL;
    json_t *jval = NULL;
    struct buf buf = BUF_INITIALIZER;
    char *resp_payload = NULL;

    int ret = convert_parse_path(txn->req_uri->path,
            &txn->req_tgt, &txn->error.desc);
    if (ret) return ret;

    if (!(txn->req_tgt.allow & ALLOW_POST)) {
        ret = HTTP_NOT_ALLOWED;
        goto done;
    }

    /* Check Content-Type */
    const char **hdr = spool_getheader(txn->req_hdrs, "Content-Type");
    if (!hdr || !is_mediatype("text/calendar", hdr[0])) {
        txn->error.desc = "This method requires a text/calendar body";
        ret = HTTP_BAD_MEDIATYPE;
        goto done;
    }

    /* Read body */
    ret = http_read_req_body(txn);
    if (ret) {
        txn->flags.conn = CONN_CLOSE;
        goto done;
    }

    /* Parse the request body */
    ical = icalparser_parse_string(buf_cstring(&txn->req_body.payload));
    if (!ical) {
        txn->error.desc = "Could not parse iCalendar data";
        ret = HTTP_BAD_REQUEST;
        goto done;
    }

    /* Convert to JSCalendar */
    jval = jmapical_vcalendar_to_jsgroup(ical);
    if (!jval) {
        txn->error.desc = "Could not convert to JSCalendar";
        ret = HTTP_SERVER_ERROR;
        goto done;
    }

    /* Write the response */
    resp_payload = json_dumps(jval, JSON_PRESERVE_ORDER |
            (config_httpprettytelemetry ? JSON_INDENT(2) : JSON_COMPACT));
    if (!resp_payload) {
        txn->error.desc = "Error dumping JSON object";
        ret = HTTP_SERVER_ERROR;
        goto done;
    }
    txn->resp_body.type = "application/jscalendar+json;type=group";
    write_body(HTTP_OK, txn, resp_payload, strlen(resp_payload));

done:
    if (ical) icalcomponent_free(ical);
    json_decref(jval);
    buf_free(&buf);
    free(resp_payload);
    return ret;
}
