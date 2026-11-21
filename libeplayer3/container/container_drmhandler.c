/*
 * CENC/ClearKey key resolution support (PSSH based).
 *
 * Extracts pssh boxes from HLS playlists ('#EXT-X-KEY' data: URIs) or DASH
 * MPDs (cenc:pssh / kid attributes) and, if any widevine box is found,
 * resolves the decryption keys natively against the configured license
 * server. See include/container_drmhandler.h for the parameter format.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 */

#ifdef HAVE_CONFIG_H
#include <config.h>
#endif

/* ***************************** */
/* Includes                      */
/* ***************************** */
#include "debug.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <pthread.h>
#include <unistd.h>

#include <curl/curl.h>
#include <zlib.h>

#include <libavutil/base64.h>
#include <libavutil/bprint.h>

#include "container_drmhandler.h"
#include "container_drm.h"

/* ***************************** */
/* Makros/Constants              */
/* ***************************** */

#define CENC_MAX_PSSH           8    /* max. number of pssh entries handed to the API */
#define CENC_MAX_KIDS_PER       8    /* max. key ids per entry                        */
#define CENC_MAX_LOOSE_KIDS     16   /* KIDs without a pssh entry (e.g. DASH kids)    */

#define CENC_HTTP_USER_AGENT          "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36"
#define CENC_HTTP_CONNECT_TIMEOUT_MS  3000
#define CENC_GET_TIMEOUT_MS           10000
#define CENC_PLAYLIST_MAX_BYTES       (512 * 1024)
#define CENC_MPD_MAX_BYTES            (1024 * 1024)
#define CENC_FETCH_ATTEMPTS           3    /* retries for transient manifest/playlist failures */
#define CENC_FETCH_RETRY_DELAY_MS     1500
#define CENC_PSSH_RAW_MAX             (16 * 1024)          /* larger pssh boxes ignored */

/* ***************************** */
/* Types                         */
/* ***************************** */
typedef struct CencPssh_s
{
	char system_id[33];   /* lowercase hex, "" when unknown */
	char pssh_b64[CENC_PSSH_RAW_MAX * 4 / 3 + 16];
	int n_kids;
	char kids[CENC_MAX_KIDS_PER][33];
} CencPssh_t;

/* collected PSSH data of one input (may grow a synthetic entry for loose KIDs) */
typedef struct CencCollect_s
{
	CencPssh_t pssh[CENC_MAX_PSSH];
	int n_pssh;
	char loose_kids[CENC_MAX_LOOSE_KIDS][33]; /* KIDs without a pssh, hex (e.g. DASH) */
	int n_loose_kids;
} CencCollect_t;

typedef struct RespBuf_s
{
	uint8_t *data;
	size_t len;
	size_t cap_max;   /* bytes to store, excess is counted but discarded */
	int truncated;
} RespBuf_t;

/* minimal JSON: strings, arrays and objects; any other token (nulls,
 * booleans, numbers) is accepted but stored as null */
typedef enum { JV_NULL, JV_STR, JV_ARR, JV_OBJ } JsonType;
typedef struct JVal_s
{
	JsonType type;
	char *str;              /* decoded string content (JV_STR / object keys) */
	struct JVal_s **items;  /* children, objects are flat key,value pairs    */
	size_t n_items;         /* for JV_OBJ: number of KEYS                    */
} JVal;

typedef struct JsonDoc_s
{
	const char *s;
	size_t pos, len;
	int err;
} JsonDoc_t;

/* ***************************** */
/* Variables                     */
/* ***************************** */
static pthread_once_t curl_init_once = PTHREAD_ONCE_INIT;

/* ***************************** */
/* Small helpers                 */
/* ***************************** */
static uint32_t be32(const uint8_t *p)
{
	return ((uint32_t)p[0] << 24) | ((uint32_t)p[1] << 16) | ((uint32_t)p[2] << 8) | p[3];
}

static int hex_encode(const uint8_t *in, size_t len, char out_hex[2 * 16 + 1])
{
	static const char digits[] = "0123456789abcdef";
	size_t i;

	if (len > 16)
		return -1;
	for (i = 0; i < len; i++)
	{
		out_hex[2 * i] = digits[in[i] >> 4];
		out_hex[2 * i + 1] = digits[in[i] & 0x0f];
	}
	out_hex[2 * len] = '\0';
	return (int)len;
}

/* copy the last path extension of a uri into out (lowercase); 1 on success */
static int uri_ext_copy(const char *uri, char out[], size_t out_size)
{
	const char *path = strrchr(uri, '/');
	const char *dot = NULL;
	size_t i = 0;

	if (path == NULL)
		path = uri;

	for (; *path != '\0'; path++)
	{
		if (*path == '?' || *path == '#')
			break;
		if (*path == '.' && path[1] != '\0' && strchr("/?#", path[1]) == NULL)
			dot = path + 1;
	}
	if (dot == NULL)
		return 0;

	while (dot[i] != '\0' && i < out_size - 1)
	{
		char c = dot[i];
		if (!((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')))
			break;
		out[i] = (c >= 'A' && c <= 'Z') ? c + 'a' - 'A' : c;
		i++;
	}
	if (i == 0)
		return 0;
	out[i] = '\0';
	return 1;
}

static int uri_is_http(const char *uri)
{
	return strncmp(uri, "http://", 7) == 0 || strncmp(uri, "https://", 8) == 0;
}

/* resolve a (possibly relative) url against base; returns malloc'ed string */
static char *url_resolve(const char *base, const char *rel)
{
	char out[1024];

	if (strncmp(rel, "http://", 7) == 0 || strncmp(rel, "https://", 8) == 0)
		return strdup(rel);

	if (base != NULL && base[0] != '\0' && (uri_is_http(base)))
	{
		const char *host = strstr(base, "://") + 3; /* first '/' after the host */
		size_t prefix;

		while (*host != '/' && *host != '\0')
			host++;
		prefix = (size_t)(host - base);

		if (rel[0] == '/')
		{
			snprintf(out, sizeof(out), "%.*s%s", (int)prefix, base, rel);
			return strdup(out);
		}
		if (rel[0] == '/' && rel[1] == '/') /* protocol relative */
		{
			int scheme_len = (strncmp(base, "https:", 6) == 0) ? 5 : 4;
			snprintf(out, sizeof(out), "%.*s%s", scheme_len, base, rel);
			return strdup(out);
		}
		if (rel[0] != '\0' && *host == '/')
		{
			const char *dir = host + 1;           /* drop the last path segment */
			size_t dir_prefix;
			while (*dir != '\0')
				dir++;
			while (dir > host && *--dir != '/')
				;
			if (dir == host)
				dir = host;                        /* keep at least the leading '/' */
			else if (dir[-1] == '/')
				dir--;                             /* drop trailing slash */
			dir_prefix = (size_t)(dir - base);
			snprintf(out, sizeof(out), "%.*s/%s", (int)dir_prefix, base, rel);
			return strdup(out);
		}
	}

	return strdup(rel);
}

/* base64 / base64url decode, padding optional, @out_max caps the decoded size */
static int b64_decode_pad(const char *s, size_t len, uint8_t *out, size_t out_max)
{
	char *tmp;
	size_t i = 0, n = 0;

	if (len == 0 || s == NULL || out == NULL || out_max == 0)
		return -1;
	tmp = malloc(len + 8);
	if (tmp == NULL)
		return -1;

	while (i < len && s[i] != '"')
	{
		char ch = s[i];

		if (!((ch >= 'A' && ch <= 'Z') || (ch >= 'a' && ch <= 'z') ||
		      (ch >= '0' && ch <= '9') || ch == '+' || ch == '/' ||
		      ch == '-' || ch == '_' || ch == '='))
			break;
		if (ch == '-')
			ch = '+';
		else if (ch == '_')
			ch = '/';
		tmp[n++] = ch;
		i++;
	}
	while ((n & 3) != 0 && n < len + 7)
		tmp[n++] = '=';
	tmp[n] = '\0';

	if (n == 0)
	{
		free(tmp);
		return -1;
	}

	{
		int decoded = av_base64_decode(out, tmp, (int)out_max);
		free(tmp);
		return decoded; /* bytes decoded on success, < 0 otherwise */
	}
}


/* ***************************** */
/* PSSH collection               */
/* ***************************** */
/* add a key id to a pssh entry, deduplicated */
static int entry_add_kid(CencPssh_t *p, const uint8_t kid[16])
{
	char hex[33];
	int i;

	if (hex_encode(kid, 16, hex) < 0)
		return -1;
	for (i = 0; i < p->n_kids; i++)
		if (strcmp(p->kids[i], hex) == 0)
			return 0;
	if (p->n_kids >= CENC_MAX_KIDS_PER)
		return -1;
	strcpy(p->kids[p->n_kids], hex);
	p->n_kids++;
	return 0;
}

/* parse one 'pssh' box atom (starting at its size field) and append it to the collection */
static int collect_add_pssh(CencCollect_t *c, const uint8_t *box, size_t box_size)
{
	CencPssh_t *p;
	uint32_t version, kid_count, data_size;
	size_t pos = 8; /* skip size + 'pssh' */
	int i;

	if (c == NULL || c->n_pssh >= CENC_MAX_PSSH)
		return -1;

	p = &c->pssh[c->n_pssh];
	memset(p, 0, sizeof(CencPssh_t));

	if (box_size < pos + 4 + 16)
		return -1;

	version = box[pos] & 0x07;
	pos += 4; /* version + flags */
	hex_encode(box + pos, 16, p->system_id);
	pos += 16;

	if (version >= 1 && box_size >= pos + 4)
	{
		kid_count = be32(box + pos);
		pos += 4;
		while (kid_count > 0 && box_size >= pos + 16)
		{
			if (entry_add_kid(p, box + pos) < 0)
				return -1;
			kid_count--;
			pos += 16;
		}
		if (kid_count > 0)
			return -1; /* truncated kid list */
	}

	if (box_size < pos + 4)
		return -1;
	data_size = be32(box + pos);
	pos += 4;
	if (data_size > box_size - pos)
		return -1;

	/* the whole atom is what license servers expect */
	if (box_size > CENC_PSSH_RAW_MAX)
	{
		ffmpeg_printf(2, "container drmhandler: pssh box too large (%zu), ignoring\n", box_size);
		return -1;
	}
	if (av_base64_encode(p->pssh_b64, AV_BASE64_SIZE((int)box_size), box, (int)box_size) == NULL)
	{
		ffmpeg_printf(2, "container drmhandler: failed to base64 encode pssh box\n");
		return -1;
	}

	for (i = 0; i < c->n_pssh; i++)
		if (strcmp(c->pssh[i].pssh_b64, p->pssh_b64) == 0)
			return 0;   /* same box already collected (repeated per adaptation set) */

	c->n_pssh++;
	ffmpeg_printf(2, "container drmhandler: pssh %d: system_id=%s kids=%d\n",
	              c->n_pssh - 1, p->system_id[0] ? p->system_id : "(none)", p->n_kids);
	return 0;
}


/* finalize: fold loose KIDs into a synthetic entry when there are none from pssh */
static void collect_finalize(CencCollect_t *c)
{
	CencPssh_t *p;
	int i;

	if (c->n_loose_kids == 0 || c->n_pssh >= CENC_MAX_PSSH)
		return;

	p = &c->pssh[c->n_pssh];
	memset(p, 0, sizeof(CencPssh_t));
	for (i = 0; i < c->n_loose_kids && p->n_kids < CENC_MAX_KIDS_PER; i++)
		strcpy(p->kids[p->n_kids++], c->loose_kids[i]);
	c->n_pssh++;
}

/* ***************************** */
/* HTTP (libcurl)                */
/* ***************************** */
static void curl_init_once_cb(void)
{
	curl_global_init(CURL_GLOBAL_DEFAULT);
}

static size_t resp_write_cb(char *ptr, size_t sz, size_t nm, void *ud)
{
	RespBuf_t *b = (RespBuf_t *)ud;
	size_t add = sz * nm;
	size_t take;

	if (add == 0)
		return 0;
	if (b->len < b->cap_max)
	{
		take = add;
		if (b->len + take > b->cap_max)
			take = b->cap_max - b->len;
		memcpy(b->data + b->len, ptr, take);
		b->len += take;
	}
	else
	{
		b->truncated = 1;
	}
	return add; /* keep the transfer going even if we stop storing */
}

/*
 * GET (body == NULL) or POST (NUL-terminated body as the request payload),
 * @range optional extra header line, e.g. "Range: bytes=0-123456"
 * returns 0 and fills out/http_code on success, < 0 otherwise
 */
static int http_request(const char *url, const char *body, long timeout_ms,
                        size_t max_bytes, const char *range, RespBuf_t *out, long *http_code)
{
	CURL *e;
	CURLcode rc;
	struct curl_slist *hdrs = NULL;

	if (url == NULL || out == NULL || http_code == NULL)
		return -1;

	pthread_once(&curl_init_once, curl_init_once_cb);

	out->data = malloc(max_bytes ? max_bytes : 65536);
	if (out->data == NULL)
	{
		ffmpeg_printf(2, "container drmhandler: out of memory\n");
		return -1;
	}
	out->len = 0;
	out->cap_max = max_bytes ? max_bytes : 65536;
	out->truncated = 0;

	e = curl_easy_init();
	if (e == NULL)
	{
		free(out->data);
		out->data = NULL;
		return -1;
	}

	hdrs = curl_slist_append(hdrs, "User-Agent: " CENC_HTTP_USER_AGENT);
	if (body != NULL)
		hdrs = curl_slist_append(hdrs, "Content-Type: application/json");
	else
		/* some manifest servers (CDN edges) reject requests that do not
		 * declare gzip support with HTTP 406; the response is inflated in
		 * http_fetch_text if it actually arrives compressed */
		hdrs = curl_slist_append(hdrs, "Accept-Encoding: gzip");
	if (range != NULL && range[0] != '\0')
		hdrs = curl_slist_append(hdrs, range);

	curl_easy_setopt(e, CURLOPT_URL, url);
	curl_easy_setopt(e, CURLOPT_NOSIGNAL, 1L);
	curl_easy_setopt(e, CURLOPT_SSL_VERIFYPEER, 0L);   /* box CA store may not verify the CDN chain */
	curl_easy_setopt(e, CURLOPT_SSL_VERIFYHOST, 0L);
	curl_easy_setopt(e, CURLOPT_CONNECTTIMEOUT_MS, (long)CENC_HTTP_CONNECT_TIMEOUT_MS);
	curl_easy_setopt(e, CURLOPT_TIMEOUT_MS, timeout_ms);
	if (body != NULL)
	{
		curl_easy_setopt(e, CURLOPT_POST, 1L);
	}
	else
	{
		curl_easy_setopt(e, CURLOPT_HTTPGET, 1L);
	}
	if (hdrs != NULL)
		curl_easy_setopt(e, CURLOPT_HTTPHEADER, hdrs);
	curl_easy_setopt(e, CURLOPT_WRITEFUNCTION, resp_write_cb);
	curl_easy_setopt(e, CURLOPT_WRITEDATA, out);
	if (body != NULL)
	{
		curl_easy_setopt(e, CURLOPT_POSTFIELDS, body);
	}

	rc = curl_easy_perform(e);
	if (rc == CURLE_OK)
	{
		long code = 0;
		curl_easy_getinfo(e, CURLINFO_RESPONSE_CODE, &code);
		*http_code = code;
	}

	if (hdrs != NULL)
		curl_slist_free_all(hdrs);
	curl_easy_cleanup(e);

	if (rc != CURLE_OK)
	{
		ffmpeg_printf(2, "container drmhandler: request to %s failed: %s\n", url, curl_easy_strerror(rc));
		free(out->data);
		out->data = NULL;
		return -1;
	}
	return 0;
}

/* Decompress a gzip'ed response body; the result is NUL terminated */
static char *gunzip_buf(const uint8_t *src, size_t src_len, size_t *out_len)
{
	z_stream zs;
	char *dst = NULL;
	size_t dst_cap = 0, dst_off = 0;

	memset(&zs, 0, sizeof(zs));
	/* 16+15: accept a gzip container as well as plain zlib/deflate streams */
	if (inflateInit2(&zs, 16 + 15) != Z_OK)
		return NULL;

	zs.next_in = (Bytef *)src;
	zs.avail_in = (uInt)src_len;

	while (1) {
		int ret;
		size_t room;

		if (dst_off == dst_cap) {
			char *nd = realloc(dst, dst_cap ? dst_cap * 2 : 65536);

			if (nd == NULL)
				break;
			dst = nd;
			dst_cap = dst_cap ? dst_cap * 2 : 65536;
		}

		room = dst_cap - dst_off;
		zs.next_out = (Bytef *)dst + dst_off;
		zs.avail_out = (uInt)room;
		ret = inflate(&zs, Z_NO_FLUSH);
		dst_off += room - zs.avail_out;

		if (ret == Z_STREAM_END) {
			char *final = realloc(dst, dst_off + 1);   /* room for the terminator */

			inflateEnd(&zs);
			if (final == NULL) {
				free(dst);
				return NULL;
			}
			final[dst_off] = '\0';
			*out_len = dst_off;
			return final;
		}
		if ((ret != Z_OK && ret != Z_BUF_ERROR) || (ret == Z_BUF_ERROR && room - zs.avail_out == 0))
			break;   /* hard error or truncated stream */
	}

	inflateEnd(&zs);
	free(dst);
	return NULL;
}

/* GET a small text document (playlist / MPD); the result is NUL terminated.
 * Some CDNs flip between 406 and 5xx on their nodes while an upstream is
 * degraded, so transient status codes are retried a few times */
static int http_fetch_retryable(long code)
{
	return code == 406 || code == 408 || code == 429 || (code >= 500 && code <= 599);
}

static int http_fetch_text(const char *url, size_t max_bytes, char **text_out, size_t *len_out)
{
	char range[64];
	int attempt;

	if (max_bytes == 0)
		max_bytes = 65536;

	snprintf(range, sizeof(range), "Range: bytes=0-%zu", max_bytes - 1);
	for (attempt = 1; attempt <= CENC_FETCH_ATTEMPTS; attempt++) {
		RespBuf_t out = {NULL, 0, 0, 0};
		long code = 0;

		if (http_request(url, NULL, CENC_GET_TIMEOUT_MS, max_bytes + 8, range, &out, &code) < 0)
			code = 0;   /* transport failure: nothing to free, retry below */
		else if (code >= 200 && code <= 299) {
			char *tdata = (char *)out.data;
			size_t tlen = out.len;

			if (tlen >= 2 && (uint8_t)tdata[0] == 0x1f && (uint8_t)tdata[1] == 0x8b) {
				char *plain = gunzip_buf(out.data, tlen, &tlen);

				free(tdata);
				if (plain == NULL) {
					ffmpeg_printf(2, "container drmhandler: failed to inflate response of %s\n", url);
					return -1;
				}
				tdata = plain;   /* NUL terminated by gunzip_buf */
			} else {
				tdata[tlen] = '\0';   /* buffer was malloc'ed with room for the terminator */
			}

			if (out.truncated)
				ffmpeg_printf(2, "container drmhandler: response of %s truncated at %zu bytes\n", url, out.cap_max);

			*text_out = tdata;   /* NUL terminated (see above) */
			*len_out = tlen;
			return 0;
		}

		if (attempt < CENC_FETCH_ATTEMPTS && (code == 0 || http_fetch_retryable(code))) {
			ffmpeg_printf(2, "container drmhandler: %s -> HTTP %ld%s, retrying\n", url, code, code ? "" : " (connection failed)");
			free(out.data);
			usleep(CENC_FETCH_RETRY_DELAY_MS * 1000);
		}
		else {
			ffmpeg_printf(2, "container drmhandler: %s -> HTTP %ld%s\n", url, code, code ? "" : " (connection failed)");
			free(out.data);
			return -1;
		}
	}

	return -1;   /* unreachable */
}

/* ***************************** */
/* Input scanning per format     */
/* ***************************** */

static int hexdig(char c)
{
	return (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F');
}

/* normalize a KID attribute value: plain 32-char hex or dashed UUID form
 * (e.g. "302f80dd-411e-4886-bca5-bb1f8018a024") into dashless lowercase hex */
static char *kid_normalize(const char *in)
{
	char out[33];
	size_t n = 0;

	if (in == NULL)
		return NULL;
	while (*in != '\0')
	{
		char c = *in++;

		if (c == '-')
			continue;   /* dashed UUID form */
		if (!hexdig(c))
			return NULL;
		if (n >= 32)
			return NULL;
		out[n++] = (c >= 'A' && c <= 'F') ? (char)(c + ('a' - 'A')) : c;
	}
	if (n != 32)
		return NULL;
	out[32] = '\0';

	char *res = malloc(33);
	if (res == NULL)
		return NULL;
	memcpy(res, out, 33);
	return res;
}

static void collect_add_kid_hexstr(CencCollect_t *c, const char *hex)
{
	char *norm = kid_normalize(hex);
	int i;

	if (c == NULL || norm == NULL)
		return;
	for (i = 0; i < c->n_loose_kids; i++)
		if (strcmp(c->loose_kids[i], norm) == 0)
			break;
	if (i < c->n_loose_kids || c->n_loose_kids >= CENC_MAX_LOOSE_KIDS)
	{
		free(norm);
		return;
	}
	strcpy(c->loose_kids[c->n_loose_kids], norm);
	c->n_loose_kids++;
	free(norm);
}

static const char *find_text(const char *hay, size_t len, const char *needle)
{
	size_t n = strlen(needle);
	size_t i;

	if (len < n)
		return NULL;
	for (i = 0; i + n <= len; i++)
		if (!memcmp(hay + i, needle, n))
			return hay + i;
	return NULL;
}



#define CENC_MAX_CANDIDATES 6
#define CENC_HLS_URL_SIZE   512

static int add_candidate(char cands[][CENC_HLS_URL_SIZE], int *n_cands, const char *base_url, const char *rel)
{
	char *abs;
	int i;

	if (rel == NULL || rel[0] == '\0' || n_cands == NULL || *n_cands >= CENC_MAX_CANDIDATES)
		return -1;
	for (i = 0; i < *n_cands && i < CENC_MAX_CANDIDATES; i++)
		if (strcmp(cands[i], rel) == 0)
			return 0;
	abs = url_resolve(base_url, rel);
	if (abs == NULL)
		return -1;
	snprintf(cands[*n_cands], CENC_HLS_URL_SIZE, "%s", abs);
	free(abs);
	(*n_cands)++;
	return 0;
}

/* extract pssh boxes and KIDs from '#EXT-X-KEY' lines of an HLS playlist.
 * The pssh box arrives as URI="data:text/plain;base64,<pssh-box>", a ClearKey
 * key id may additionally be given as the unquoted 'KID=<hex32>' attribute. */
static void hls_extract_pssh(const char *text, CencCollect_t *c)
{
	const char *p = text;

	if (text == NULL)
		return;

	while (*p != '\0')
	{
		const char *eol = strchr(p, '\n');
		size_t len = (eol != NULL) ? (size_t)(eol - p) : strlen(p);

		if (len > 0 && strncmp(p, "#EXT-X-KEY", 10) == 0)
		{
			const char *lim = (eol != NULL) ? eol : p + len;
			const char *u = strstr(p, "URI=\"");

			if (u != NULL && u < lim)
			{
				const char *v = u + 5; /* after 'URI="' */
				const char *q = strchr(v, '"');

				if (q == NULL || q >= lim || q <= v)
					goto next_line;
				if (strncmp(v, "data:", 5) == 0)
				{
					/* strip the data: URI prefix up to 'base64,' */
					const char *b = strstr(v, "base64,");

					if (b != NULL && b < q)
						v = b + 7; /* after 'base64,' */
				}
				if ((size_t)(q - v) <= CENC_PSSH_RAW_MAX * 2 + 16)
				{
					uint8_t box[CENC_PSSH_RAW_MAX];
					int dlen = b64_decode_pad(v, (size_t)(q - v), box, sizeof(box));

					if (dlen >= 16 && (uint32_t)dlen == be32(box) && memcmp(box + 4, "pssh", 4) == 0)
						collect_add_pssh(c, box, (size_t)dlen);
				}
			}

			{ /* optional KID=<hex32> attribute */
				const char *k = strstr(p, "KID=");

				if (k != NULL && k < lim)
				{
					const char *e = k + 4;
					char hex[33];
					size_t n = 0;

					while (e < lim && hexdig(*e) == 1)
						hex[n++] = *e++;
					if (n == 32)
					{
						hex[32] = '\0';
						collect_add_kid_hexstr(c, hex);
					}
				}
			}
		}

next_line:
		if (eol == NULL)
			break;
		p = eol + 1;
	}
}

static int collect_from_hls(const char *uri, CencCollect_t *c)
{
	char *pl_text = NULL;
	size_t pl_len = 0;
	int i, rc = -1;

	if (http_fetch_text(uri, CENC_PLAYLIST_MAX_BYTES, &pl_text, &pl_len) < 0)
		return -1;

	hls_extract_pssh(pl_text, c);

	if (c->n_pssh == 0 && strstr(pl_text, "#EXT-X-STREAM-INF") != NULL)
	{
		/* master playlist: the pssh boxes live in the variant playlists */
		char variants[4][CENC_HLS_URL_SIZE];
		int n_var = 0;
		const char *p = pl_text;

		while (*p != '\0' && n_var < 4)
		{
			const char *eol = strchr(p, '\n');
			size_t len = (eol != NULL) ? (size_t)(eol - p) : strlen(p);
			char line[CENC_HLS_URL_SIZE];

			if (len < sizeof(line))
			{
				memcpy(line, p, len);
				line[len] = '\0';
				if (len > 0 && line[len - 1] == '\r')
					line[len - 1] = '\0';
				if (line[0] != '#' && line[0] != '\0')
					add_candidate(variants, &n_var, uri, line);
			}
			if (eol == NULL)
				break;
			p = eol + 1;
		}

		for (i = 0; i < n_var && c->n_pssh == 0; i++)
		{
			char *vt = NULL;
			size_t vl = 0;

			if (http_fetch_text(variants[i], CENC_PLAYLIST_MAX_BYTES, &vt, &vl) == 0)
			{
				hls_extract_pssh(vt, c);
				free(vt);
			}
		}
	}

	free(pl_text);
	if (c->n_pssh > 0 || c->n_loose_kids > 0)
		rc = 0;
	return rc;
}

/* capture pssh boxes carried as element content, e.g. <cenc:pssh>BASE64</cenc:pssh>
 * (any namespace prefix), in addition to the 'pssh="..."' attribute form */
static void dash_collect_pssh_elements(const char *mpd, size_t mpd_len, CencCollect_t *c)
{
	const char *p = mpd;

	while ((p = find_text(p, (size_t)(mpd + mpd_len - p), "pssh>")) != NULL)
	{
		size_t i = (size_t)(p - mpd);      /* index of 'p' in "pssh>" */
		size_t lt;
		int closing = 0;

		for (lt = i; lt > 0 && mpd[lt - 1] != '<'; lt--)
			;
		if (lt == 0 || mpd[lt - 1] != '<')
			break;                        /* no opening bracket: not a tag */
		while (lt < i)                    /* a '/' between '<' and the name = closing tag */
		{
			if (mpd[lt] == '/')
				closing = 1;
			lt++;
		}
		if (!closing)
		{
			const char *v = p + 5;        /* after 'pssh>' */

			while (*v == ' ' || *v == '\t' || *v == '\n' || *v == '\r')
				v++;
			{
				const char *end = find_text(v, (size_t)(mpd + mpd_len - v), "<");
				size_t clen;

				if (end == NULL)
					end = mpd + mpd_len;
				clen = (size_t)(end - v);
				if (clen > 0 && clen <= CENC_PSSH_RAW_MAX * 2 + 16)
				{
					uint8_t box[CENC_PSSH_RAW_MAX];
					int dlen = b64_decode_pad(v, clen, box, sizeof(box));

					if (dlen >= 16 && memcmp(box + 4, "pssh", 4) == 0)
						collect_add_pssh(c, box, (size_t)dlen);
				}
			}
		}
		p += 5;
	}
}

/* find a case-insensitive 'kid' occurrence in bounded text */
static const char *find_kid_ci(const char *hay, size_t len)
{
	size_t i;

	if (len < 3)
		return NULL;
	for (i = 0; i + 3 <= len; i++)
	{
		char a = hay[i], b = hay[i + 1], d = hay[i + 2];

		if ((a == 'k' || a == 'K') && (b == 'i' || b == 'I') && (d == 'd' || d == 'D'))
			return hay + i;
	}
	return NULL;
}

/* capture KID attribute values in any case ('kid=', 'KID=', 'default_KID=' ...);
 * the value must be 32 hex digits, optionally dashed UUID form */
static void dash_collect_kids(const char *mpd, size_t mpd_len, CencCollect_t *c)
{
	size_t pos = 0;

	while (pos + 4 <= mpd_len)
	{
		const char *p = find_kid_ci(mpd + pos, mpd_len - pos);

		if (p == NULL)
			break;
		pos = (size_t)(p - mpd) + 3;
		if (mpd[pos] != '=' || mpd[pos + 1] != '"')
			continue;
		{
			const char *v = p + 4;         /* after 'kid="' */
			const char *q = find_text(v, (size_t)(mpd + mpd_len - v), "\"");

			if (q == NULL)
				q = mpd + mpd_len;
			{
				char val[64];
				size_t k = 0;

				while (v < q && k < sizeof(val) - 1)
					val[k++] = *v++;
				val[k] = '\0';
				collect_add_kid_hexstr(c, val);   /* validates and dedupes */
			}
		}
	}
}

static int collect_from_dash(const char *uri, CencCollect_t *c)
{
	int attempt;

	/* A degraded edge node may answer a manifest request with HTTP 200 and an
	 * error stub instead of the protected MPD, so "no pssh/KID" gets the same
	 * bounded retries as transient status codes */
	for (attempt = 1; attempt <= CENC_FETCH_ATTEMPTS; attempt++) {
		char *mpd = NULL;
		size_t mpd_len = 0;
		const char *p;

		if (http_fetch_text(uri, CENC_MPD_MAX_BYTES, &mpd, &mpd_len) < 0) {
			/* already logged by http_fetch_text; a definitive refusal is not retried here */
			return -1;
		}

		p = find_text(mpd, mpd_len, "pssh=\"");
		while (p != NULL)
		{
			const char *v = p + 6; /* after 'pssh="' */
			const char *end = strchr(v, '"');
			size_t off;

			if (end != NULL && end > v && (size_t)(end - v) <= CENC_PSSH_RAW_MAX * 2)
			{
				uint8_t box[CENC_PSSH_RAW_MAX];
				int dlen = b64_decode_pad(v, (size_t)(end - v), box, sizeof(box));

				if (dlen >= 16 && memcmp(box + 4, "pssh", 4) == 0)
					collect_add_pssh(c, box, (size_t)dlen);
			}

			if (end == NULL || end == v || (size_t)(end - mpd) >= mpd_len)
				break;

			off = (size_t)(end - mpd) + 1;
			if (off >= mpd_len)
				break;
			p = find_text(mpd + off, mpd_len - off, "pssh=\"");
		}

		dash_collect_pssh_elements(mpd, mpd_len, c);
		dash_collect_kids(mpd, mpd_len, c);

		if (c->n_pssh > 0 || c->n_loose_kids > 0) {
			free(mpd);
			return 0;
		}

		if (attempt < CENC_FETCH_ATTEMPTS) {
			ffmpeg_printf(2, "container drmhandler: manifest of %s has no pssh/KID (%zu bytes), retrying\n", uri, mpd_len);
			free(mpd);
			usleep(CENC_FETCH_RETRY_DELAY_MS * 1000);
			continue;
		}

		/* final failure: show what the edge actually served */
		{
			char head[193];
			size_t n = mpd_len < sizeof(head) - 1 ? mpd_len : sizeof(head) - 1;
			unsigned j;

			for (j = 0; j < n; j++) {
				char ch = mpd[j];
				head[j] = (ch >= 32 && ch <= 126) ? ch : '.';
			}
			head[n] = '\0';
			ffmpeg_printf(2, "container drmhandler: manifest of %s has no pssh/KID (%zu bytes): %.192s\n", uri, mpd_len, head);
		}
		free(mpd);
		return -1;
	}

	return -1;   /* unreachable */
}

/* ***************************** */
/* Minimal JSON parsing          */
/* ***************************** */
static void json_free(JVal *v);

static int jskip_ws(JsonDoc_t *d)
{
	while (d->pos < d->len && (d->s[d->pos] == ' ' || d->s[d->pos] == '\t' ||
	                          d->s[d->pos] == '\n' || d->s[d->pos] == '\r'))
		d->pos++;
	return 0;
}

static char jpeek(JsonDoc_t *d)
{
	if (d->err || d->pos >= d->len)
	{
		d->err = 1;
		return '\0';
	}
	return d->s[d->pos];
}

static int hex_nibble(char c, int *v)
{
	if (c >= '0' && c <= '9') { *v = c - '0'; return 1; }
	if (c >= 'a' && c <= 'f') { *v = c - 'a' + 10; return 1; }
	if (c >= 'A' && c <= 'F') { *v = c - 'A' + 10; return 1; }
	return 0;
}

static char *parse_string_raw(JsonDoc_t *d)
{
	char *out = malloc(64);
	size_t cap = 64, len = 0;
	unsigned int cp;
	int k;

	if (out == NULL)
	{
		d->err = 1;
		return NULL;
	}
	if (jpeek(d) != '"')
		goto fail;
	d->pos++;

	for (;;)
	{
		char c = jpeek(d);

		if (d->err || c == '\0')
			break;
		if (c == '"')
		{
			d->pos++;
			out[len] = '\0';
			return out;
		}
		if ((unsigned char)c < 0x20)
			break; /* raw control chars are invalid in JSON strings */

		if (len + 4 >= cap)
		{
			cap *= 2;
			out = realloc(out, cap);
			if (out == NULL)
				goto fail;
		}

		if (c != '\\')
		{
			out[len++] = c;
			d->pos++;
			continue;
		}

		d->pos++; /* backslash */
		c = jpeek(d);
		switch ((unsigned char)c)
		{
		case '"': case '\\': case '/': out[len++] = c; d->pos++; break;
		case 'b': out[len++] = '\b'; d->pos++; break;
		case 'f': out[len++] = '\f'; d->pos++; break;
		case 'n': out[len++] = '\n'; d->pos++; break;
		case 'r': out[len++] = '\r'; d->pos++; break;
		case 't': out[len++] = '\t'; d->pos++; break;
		case 'u':
			if ((size_t)(d->pos + 5) > d->len)
				goto fail;
			cp = 0;
			for (k = 0; k < 4; k++)
			{
				int v = 0;

				if (!hex_nibble(d->s[d->pos + 1 + k], &v)) /* digits follow the 'u' */
					goto fail;
				cp = cp * 16 + (unsigned int)v;
			}
			d->pos += 5;
			if (cp < 0x80)
			{
				out[len++] = (char)cp;
			}
			else if (cp < 0x800)
			{
				out[len++] = (char)(0xC0 | (cp >> 6));
				out[len++] = (char)(0x80 | (cp & 0x3F));
			}
			else if (cp <= 0xD7FF || cp >= 0xE000)
			{
				out[len++] = (char)(0xE0 | (cp >> 12));
				out[len++] = (char)(0x80 | ((cp >> 6) & 0x3F));
				out[len++] = (char)(0x80 | (cp & 0x3F));
			}
			else
			{
				out[len++] = '?'; /* lone surrogate */
			}
			break;
		default:
			goto fail;
		}
	}

fail:
	free(out);
	d->err = 1;
	return NULL;
}

static JVal *parse_value(JsonDoc_t *d, int depth)
{
	JVal *v;

	if (depth > 32 || d->err)
	{
		d->err = 1;
		return NULL;
	}
	jskip_ws(d);
	v = malloc(sizeof(JVal));
	if (v == NULL)
	{
		d->err = 1;
		return NULL;
	}
	memset(v, 0, sizeof(*v));

	switch ((unsigned char)jpeek(d))
	{
	case '"':
	{
		char *s = parse_string_raw(d);

		if (s == NULL)
			goto fail;
		v->type = JV_STR;
		v->str = s;
		return v;
	}
	case 't':
		if ((size_t)(d->pos + 4) <= d->len && !memcmp(d->s + d->pos, "true", 4))
		{
			d->pos += 4;
			v->type = JV_NULL; /* accepted, not stored */
			return v;
		}
		goto fail;
	case 'f':
		if ((size_t)(d->pos + 5) <= d->len && !memcmp(d->s + d->pos, "false", 5))
		{
			d->pos += 5;
			v->type = JV_NULL; /* accepted, not stored */
			return v;
		}
		goto fail;
	case 'n':
		if ((size_t)(d->pos + 4) <= d->len && !memcmp(d->s + d->pos, "null", 4))
		{
			d->pos += 4;
			v->type = JV_NULL;
			return v;
		}
		goto fail;
	case '[':
	{
		size_t cap = 8, n = 0;

		v->type = JV_ARR;
		d->pos++; /* [ */
		for (;;)
		{
			JVal *item;

			jskip_ws(d);
			if (d->err)
				goto fail;
			if (jpeek(d) == ']')
			{
				d->pos++;
				break;
			}
			item = parse_value(d, depth + 1);
			if (item == NULL)
				goto fail;
			if (v->items == NULL || n >= cap)
			{
				if (v->items != NULL)
					cap *= 2;
				v->items = realloc(v->items, cap * sizeof(JVal *));
				if (v->items == NULL)
					goto fail;
			}
			v->items[n] = item;
			n++;
			v->n_items = n; /* keep current so json_free releases stored children on failure */

			jskip_ws(d);
			if (d->err)
				goto fail;
			if (jpeek(d) == ',')
				d->pos++; /* separator; next iteration handles ']' or the next item */
		}
		v->n_items = n;
		return v;
	}
	case '{':
	{
		size_t cap = 8, nkv = 0; /* number of keys */

		v->type = JV_OBJ;
		d->pos++; /* { */
		for (;;)
		{
			char *key;
			JVal *item;

			jskip_ws(d);
			if (d->err)
				goto fail;
			if (jpeek(d) == '}')
			{
				d->pos++;
				break;
			}
			key = parse_string_raw(d);
			if (key == NULL)
				goto fail;
			jskip_ws(d);
			if (d->err || jpeek(d) != ':')
			{
				free(key);
				goto fail;
			}
			d->pos++;
			item = parse_value(d, depth + 1);
			if (item == NULL)
			{
				free(key);
				goto fail;
			}
			if (v->items == NULL || (size_t)(nkv + 1) * 2 > cap)
			{
				cap = (cap < 8 ? 8 : cap * 2);
				v->items = realloc(v->items, cap * sizeof(JVal *));
				if (v->items == NULL)
				{
					free(key);
					goto fail;
				}
			}
			{
				JVal *kv = malloc(sizeof(JVal));

				if (kv == NULL)
				{
					free(key);
					goto fail;
				}
				memset(kv, 0, sizeof(*kv));
				kv->type = JV_STR;
				kv->str = key; /* ownership moved */
				key = NULL;
				v->items[nkv * 2] = kv;
			}
			v->items[nkv * 2 + 1] = item;
			nkv++;
			v->n_items = nkv; /* keep current so json_free releases stored children on failure */

			jskip_ws(d);
			if (d->err)
				goto fail;
			if (jpeek(d) == ',')
				d->pos++; /* separator; next iteration handles '}' or the next key */
		}
		v->n_items = nkv;
		return v;
	}
	default:
	{
		char c0, *endptr;

		c0 = jpeek(d);
		if (c0 == '\0' || !(c0 == '-' || (c0 >= '0' && c0 <= '9')))
			goto fail;
		strtod(d->s + d->pos, &endptr); /* validate the number and find its end */
		if (endptr == NULL || endptr == d->s + d->pos)
			goto fail;
		d->pos = (size_t)(endptr - d->s);
		v->type = JV_NULL; /* accepted, not stored */
		return v;
	}
	}

fail:
	json_free(v);
	d->err = 1;
	return NULL;
}

static void json_free(JVal *v)
{
	size_t i, total;

	if (v == NULL)
		return;
	total = (v->type == JV_OBJ) ? v->n_items * 2 : v->n_items;
	for (i = 0; i < total && v->items != NULL; i++)
		json_free(v->items[i]);
	if (v->str != NULL)
		free(v->str);
	free(v->items);
	free(v);
}

static JVal *json_parse(const char *s, size_t len)
{
	JsonDoc_t d = { s, 0, len, 0 };
	JVal *root;

	if (s == NULL || len == 0)
		return NULL;
	root = parse_value(&d, 0);
	if (root == NULL || d.err)
	{
		json_free(root);
		return NULL;
	}
	jskip_ws(&d);
	if (d.pos != d.len || d.err)
	{
		json_free(root);
		return NULL;
	}
	return root;
}

static const JVal *jobj_get(const JVal *obj, const char *key)
{
	size_t i;

	if (obj == NULL || obj->type != JV_OBJ)
		return NULL;
	for (i = 0; i < obj->n_items; i++)
	{
		const JVal *k = obj->items[2 * i];

		if (k != NULL && k->type == JV_STR && k->str != NULL && strcmp(k->str, key) == 0)
			return obj->items[2 * i + 1];
	}
	return NULL;
}

/* ***************************** */
/* Key resolution                */
/* ***************************** */

/* resolved key pairs, lowercase hex without dashes; the final output string is
 * "KIDHEX:KEYHEX[,...][,DEFAULT]" */
typedef struct ResolvedKey_s
{
	char kid[33];   /* 32 hex chars + NUL */
	char key[33];   /* content key as 32 hex chars + NUL (AES-128) */
} ResolvedKey_t;

#define CENC_MAX_RESOLVED 16

static int kid_eq(const char *a, const char *b)
{
	size_t i;

	if (a == NULL || b == NULL)
		return 0;
	for (i = 0;; i++)
	{
		char x = a[i], y = b[i];

		if (x >= 'A' && x <= 'F')
			x += 'a' - 'A';
		if (y >= 'A' && y <= 'F')
			y += 'a' - 'A';
		if (x != y)
			return 0;
		if (x == '\0')
			return 1;
	}
}

static void resolve_add(ResolvedKey_t *keys, int *n_keys, const char *kid, const char *key)
{
	int i;

	if (keys == NULL || n_keys == NULL || *n_keys >= CENC_MAX_RESOLVED)
		return;
	for (i = 0; i < *n_keys; i++)
		if (kid_eq(keys[i].kid, kid))
			return;
	snprintf(keys[*n_keys].kid, sizeof(keys[0].kid), "%s", kid);
	snprintf(keys[*n_keys].key, sizeof(keys[0].key), "%s", key);
	(*n_keys)++;
}

/* build "Name: value" license server headers from the drmhandler parameters'
 * "license_headers" (JSON object, or an array of single-key objects);
 * returns a malloc'ed string array plus its count, NULL when not configured */
static char **build_license_header_lines(const JVal *params, size_t *n_out)
{
	const JVal *lh = jobj_get(params, "license_headers");
	size_t cap = 4, n = 0, h;
	char **lines;

	*n_out = 0;
	if (params == NULL || lh == NULL || (lh->type != JV_OBJ && lh->type != JV_ARR))
		return NULL;

	lines = malloc(cap * sizeof(*lines));
	if (lines == NULL)
		return NULL;

	for (h = 0; h < lh->n_items; h++) {
		const char *name = NULL, *value = "";
		size_t l;

		if (lh->type == JV_OBJ) {
			const JVal *kv = lh->items[2*h], *vv = lh->items[2*h+1];

			if (kv != NULL && kv->type == JV_STR && kv->str != NULL && kv->str[0] != '\0')
				name = kv->str;
			if (vv != NULL && vv->type == JV_STR && vv->str != NULL)
				value = vv->str;
		} else {
			const JVal *item = lh->items[h];

			/* object entries are stored as [key, value] pairs with n_items counting keys */
			if (item != NULL && item->type == JV_OBJ && item->n_items >= 1 &&
			    item->items[0] != NULL && item->items[0]->type == JV_STR &&
			    item->items[0]->str != NULL && item->items[0]->str[0] != '\0') {
				name = item->items[0]->str;
				if (item->items[1] != NULL && item->items[1]->type == JV_STR &&
				    item->items[1]->str != NULL)
					value = item->items[1]->str;
			}
		}
		if (name == NULL)
			continue;

		l = strlen(name) + 3 + strlen(value);   /* "Name: value" */
		lines[n] = malloc(l + 1);
		if (lines[n] == NULL)
			break;
		snprintf(lines[n], l + 1, "%s: %s", name, value);
		n++;

		if (n >= cap) {   /* room for the next entry */
			char **nl = realloc(lines, (cap *= 2) * sizeof(*lines));

			if (nl == NULL)
				break;
			lines = nl;
		}
	}

	if (n == 0) {
		free(lines);
		return NULL;
	}
	*n_out = n;
	return lines;
}

/* public entry point */
int32_t container_drmhandler_resolve(const char *source_uri, const char *drmhandler_parameters,
                               char *keys_out, size_t keys_out_size)
{
	CencCollect_t collect;
	char ext[8];
	int have_ext = 0;
	AVBPrint req;
	char *keys = NULL;
	JVal *params = NULL;
	const char *wv_device = NULL, *license_url = NULL;
	int n_usable = 0, i;
	size_t klen;

	if (keys_out == NULL || keys_out_size == 0)
		return -1;
	keys_out[0] = '\0';

	if (source_uri == NULL || source_uri[0] == '\0')
	{
		ffmpeg_printf(2, "container drmhandler: no input uri given\n");
		return 0;
	}

	memset(&collect, 0, sizeof(collect));
	if (uri_ext_copy(source_uri, ext, sizeof(ext)))
		have_ext = 1;
	if (!have_ext ||
	    (strcmp(ext, "m3u") != 0 && strcmp(ext, "m3u8") != 0 && strcmp(ext, "mpd") != 0))
	{
		ffmpeg_printf(2, "container drmhandler: %s is not an m3u/m3u8/mpd input\n", source_uri);
		return 0;
	}
	/* ---- parse the drmhandler parameters (JSON object, see container_drmhandler.h) ---- */
	if (drmhandler_parameters == NULL || drmhandler_parameters[0] == '\0')
	{
		ffmpeg_printf(2, "container drmhandler: no drmhandler parameters given\n");
		return -1;
	}
	params = json_parse(drmhandler_parameters, strlen(drmhandler_parameters));
	if (params == NULL || params->type != JV_OBJ)
	{
		json_free(params);
		ffmpeg_printf(2, "container drmhandler: the drmhandler parameters are not a JSON object\n");
		return -1;
	}
	{
		const JVal *dv = jobj_get(params, "wv_device");

		if (dv == NULL || dv->type != JV_STR || dv->str == NULL || dv->str[0] == '\0')
		{
			json_free(params);
			ffmpeg_printf(2, "container drmhandler: no wv_device in the drmhandler parameters\n");
			return -1;
		}
		wv_device = dv->str;
	}
	{
		const JVal *lu = jobj_get(params, "license_url");

		if (lu == NULL || lu->type != JV_STR || lu->str == NULL || lu->str[0] == '\0')
		{
			json_free(params);
			ffmpeg_printf(2, "container drmhandler: no license_url in the drmhandler parameters\n");
			return -1;
		}
		license_url = lu->str;
	}

	/* ---- collect the pssh data from the playlist / manifest text ---- */
	if (strcmp(ext, "mpd") == 0)
		collect_from_dash(source_uri, &collect);
	else
		collect_from_hls(source_uri, &collect);

	collect_finalize(&collect);
	if (collect.n_pssh == 0)
	{
		json_free(params);
		ffmpeg_printf(2, "container drmhandler: no pssh or KID found in %s\n", source_uri);
		return 0;
	}

	/* ---- acquire the keys through the widevine license server ------------ */
	{
		char **hdrs = NULL;
		size_t n_hdrs = 0;
		int saw_error = 0;
		ResolvedKey_t resolved[CENC_MAX_RESOLVED];
		int n_resolved = 0;

		hdrs = build_license_header_lines(params, &n_hdrs);
		ffmpeg_printf(2, "container drmhandler: %zu custom license header(s) configured\n", n_hdrs);

		/* try each collected box in turn until one yields keys: multi-DRM manifests
		 * carry one pssh per DRM system and only the widevine one can be licensed */
		for (i = 0; i < collect.n_pssh && n_resolved == 0; i++)
		{
			const CencPssh_t *e = &collect.pssh[i];
			drm_wv_key_t *wkeys = NULL;
			size_t n_keys = 0, k;

			if (strcmp(e->system_id, "edef8ba979d64acea3c827dcd51d21ed") != 0)
				continue;   /* not a widevine box */

			if (container_drm_resolve(wv_device, e->pssh_b64, license_url,
			                          (const char *const *)hdrs, n_hdrs,
			                          &wkeys, &n_keys) < 0)
			{
				saw_error = 1;
				continue;   /* container_drm logged the reason */
			}

			for (k = 0; k < n_keys && wkeys != NULL && n_resolved < CENC_MAX_RESOLVED; k++)
			{
				char kid[33], key[33];

				if (hex_encode(wkeys[k].kid, 16, kid) >= 0 && hex_encode(wkeys[k].key, 16, key) >= 0)
					resolve_add(resolved, &n_resolved, kid, key);
			}
			container_drm_free(wkeys);
		}

		if (hdrs != NULL)
		{
			for (i = 0; i < (int)n_hdrs; i++)
				free(hdrs[i]);
			free(hdrs);
		}

		json_free(params);
		if (n_resolved <= 0)
		{
			ffmpeg_printf(2, "container drmhandler: no keys resolved for %s\n", source_uri);
			return saw_error ? -1 : 0;
		}

		n_usable = n_resolved;
		av_bprint_init(&req, 0, AV_BPRINT_SIZE_UNLIMITED);
		for (i = 0; i < n_usable; i++)
			av_bprintf(&req, "%s%s:%s", (i ? "," : ""), resolved[i].kid, resolved[i].key);

		if (av_bprint_finalize(&req, &keys) < 0 || keys == NULL)
		{
			free(keys);
			ffmpeg_printf(2, "container drmhandler: failed to build the key list\n");
			return -1;
		}
	}

	klen = strlen(keys);
	ffmpeg_printf(2, "container drmhandler: resolved %d key(s) for %s\n", n_usable, source_uri);
	if (klen >= keys_out_size)
	{
		ffmpeg_printf(2, "container drmhandler: key list truncated to %zu chars\n", keys_out_size - 1);
		klen = keys_out_size - 1;
	}
	memcpy(keys_out, keys, klen);
	keys_out[klen] = '\0';
	free(keys);
	return n_usable > 0 ? n_usable : 1;
}
