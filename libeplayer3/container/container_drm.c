/*
 * Widevine CENC license handling (PSSH based, self-contained).
 *
 * Implements the whole license round-trip natively: loads a device file
 * (.wvd), builds and RSA-signs a license request for a PSSH box, posts it
 * to the configured license server, verifies the signed response and
 * derives the content keys from it. See include/container_drm.h for the
 * API contract.
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
#include <strings.h>
#include <stdint.h>
#include <time.h>
#include <fcntl.h>
#include <unistd.h>
#include <pthread.h>

#include <curl/curl.h>

#include <openssl/evp.h>
#include <openssl/rsa.h>
#include <openssl/pem.h>
#include <openssl/bio.h>
#include <openssl/crypto.h>

#include "container_drm.h"

/* ***************************** */
/* Makros/Constants              */
/* ***************************** */

#define DRM_CONNECT_TIMEOUT_MS   10000
#define DRM_LICENSE_TIMEOUT_MS   60000    /* license round-trips can be slow */
#define DRM_RESPONSE_MAX_BYTES   (8 * 1024 * 1024)
#define WVD_FILE_MAX             (512 * 1024)

/* Widevine PSSH system id: edef8ba9-79d6-4ace-a3c8-27dcd51d21ed */
static const uint8_t WV_SYSTEM_ID[16] = {
	0xed, 0xef, 0x8b, 0xa9, 0x79, 0xd6, 0x4a, 0xce,
	0xa3, 0xc8, 0x27, 0xdc, 0xd5, 0x1d, 0x21, 0xed
};

static pthread_once_t curl_init_once = PTHREAD_ONCE_INIT;

/* ***************************** */
/* Small helpers                 */
/* ***************************** */

static void curl_init_once_cb(void)
{
	curl_global_init(CURL_GLOBAL_ALL);
}

static uint32_t be32_get(const uint8_t *p)
{
	return ((uint32_t)p[0] << 24) | ((uint32_t)p[1] << 16) |
	       ((uint32_t)p[2] << 8) | (uint32_t)p[3];
}

static int rand_bytes(uint8_t *out, size_t n)
{
	int fd = open("/dev/urandom", O_RDONLY);
	ssize_t r;

	if (fd < 0)
		return -1;
	while (n > 0) {
		r = read(fd, out, n);
		if (r <= 0) {
			close(fd);
			return -1;
		}
		out += r;
		n -= (size_t)r;
	}
	close(fd);
	return 0;
}

/* base64 alphabet value, also accepts the url-safe variants */
static int b64_value(char c)
{
	if (c >= 'A' && c <= 'Z')
		return c - 'A';
	if (c >= 'a' && c <= 'z')
		return c - 'a' + 26;
	if (c >= '0' && c <= '9')
		return c - '0' + 52;
	if (c == '+' || c == '-')
		return 62;
	if (c == '/' || c == '_')
		return 63;
	return -1;
}

/*
 * Decode @src/@len into a malloc'd buffer, NULL on error. Padding and
 * whitespace are tolerated, url-safe alphabet too.
 */
static uint8_t *b64_decode(const char *src, size_t len, size_t *out_len)
{
	uint8_t *out;
	size_t n = 0;
	uint32_t acc = 0;
	int bits = 0;

	if (out_len != NULL)
		*out_len = 0;
	if (src == NULL || len == 0)
		return NULL;
	out = malloc(len / 4 * 3 + 4);
	if (out == NULL)
		return NULL;

	while (len-- > 0) {
		char c = *src++;
		int v;

		if (c == '=' || c == '\n' || c == '\r' || c == ' ' || c == '\t')
			continue;
		v = b64_value(c);
		if (v < 0) {
			free(out);
			return NULL;
		}
		acc = (acc << 6) | (uint32_t)v;
		bits += 6;
		if (bits >= 8) {
			bits -= 8;
			out[n++] = (uint8_t)((acc >> bits) & 0xff);
		}
	}

	if (n == 0) {
		free(out);
		return NULL;
	}
	if (out_len != NULL)
		*out_len = n;
	return out;
}

static const char b64_encode_tab[] = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

/* base64 body between BEGIN/END lines, NUL terminated */
static char *b64_wrap(const uint8_t *in, size_t len);
static char *pem_wrap(const char *label, const uint8_t *in, size_t len)
{
	char *body = b64_wrap(in, len);
	size_t blen;
	size_t cap;
	char *out;
	int w;

	if (body == NULL)
		return NULL;
	blen = strlen(body);
	cap = strlen(label) * 2 + blen + 64;
	out = malloc(cap);
	if (out == NULL) {
		free(body);
		return NULL;
	}
	w = snprintf(out, cap, "-----BEGIN %s-----\n%s\n-----END %s-----\n", label, body, label);
	free(body);
	if (w < 0 || (size_t)w >= cap) {
		free(out);
		return NULL;
	}
	return out;
}

/* encode @len bytes, 76 characters per line, NUL terminated */
static char *b64_wrap(const uint8_t *in, size_t len)
{
	char *out;
	size_t groups = (len + 2) / 3;      /* base64 groups of input triplets */
	size_t lines = (groups + 18) / 19;  /* 76 chars per line = 19 groups   */
	size_t n = 0, i = 0, group = 0;

	if (len == 0)
		return NULL;
	out = malloc(groups * 4 + lines * 2 + 2);
	if (out == NULL)
		return NULL;

	while (i < len) {
		uint32_t b1 = in[i];
		uint32_t b2 = (i + 1 < len) ? in[i + 1] : 0;
		uint32_t b3 = (i + 2 < len) ? in[i + 2] : 0;
		uint32_t v = (b1 << 16) | (b2 << 8) | b3;

		out[n++] = b64_encode_tab[(v >> 18) & 0x3f];
		out[n++] = b64_encode_tab[(v >> 12) & 0x3f];
		out[n++] = (i + 1 < len) ? b64_encode_tab[(v >> 6) & 0x3f] : '=';
		out[n++] = (i + 2 < len) ? b64_encode_tab[v & 0x3f] : '=';

		i += 3;
		if (++group == 19 && i < len) {
			group = 0;
			out[n++] = '\n';
		}
	}
	out[n] = '\0';
	return out;
}

/*
 * Growable byte buffer.
 */
typedef struct DBuf_s
{
	uint8_t *data;
	size_t len, cap;
} DBuf_t;

static int dbuf_reserve(DBuf_t *b, size_t extra)
{
	size_t need = b->len + extra;
	size_t ncap;

	if (need <= b->cap)
		return 0;
	ncap = b->cap ? b->cap : 256;
	while (ncap < need)
		ncap *= 2;
	b->data = realloc(b->data, ncap);
	if (b->data == NULL)
		return -1;
	b->cap = ncap;
	return 0;
}

static int dbuf_append(DBuf_t *b, const void *src, size_t len)
{
	if (dbuf_reserve(b, len) < 0 || b->len > SIZE_MAX - len)
		return -1;
	memcpy(b->data + b->len, src, len);
	b->len += len;
	return 0;
}

static int dbuf_put_u8(DBuf_t *b, uint8_t v)
{
	return dbuf_append(b, &v, 1);
}

/*
 * Minimal protobuf wire-format codec (just what the license protocol needs:
 * varints and length-delimited fields, tolerant of unknown fields).
 */
static int pb_put_varint(DBuf_t *b, uint64_t v)
{
	uint8_t tmp[10];
	int n = 0;
	int i;

	do {
		tmp[n++] = (uint8_t)(v & 0x7f);
		v >>= 7;
	} while (v != 0 && n < 10);
	if (v != 0)
		return -1;
	for (i = 0; i < n; i++) {
		uint8_t octet = tmp[i];

		if (i + 1 < n)      /* more groups follow: continuation bit */
			octet |= 0x80;
		if (dbuf_put_u8(b, octet) < 0)
			return -1;
	}
	return 0;
}

static int pb_field(DBuf_t *b, uint32_t field, int wire)
{
	return pb_put_varint(b, ((uint64_t)field << 3) | (uint64_t)wire);
}

/* length-delimited field: tag + u32be size + payload */
static int pb_put_bytes(DBuf_t *b, uint32_t field, const void *data, size_t len)
{
	if (pb_field(b, field, 2) < 0 ||
	    pb_put_varint(b, len) < 0 ||
	    dbuf_append(b, data, len) < 0)
		return -1;
	return 0;
}

typedef struct PBRead_s
{
	const uint8_t *p;
	size_t len, pos;
} PBRead_t;

static int pb_read_varint(PBRead_t *r, uint64_t *out)
{
	uint64_t v = 0;
	int shift = 0;

	while (r->pos < r->len && shift <= 63) {
		uint8_t octet = r->p[r->pos++];

		v |= (uint64_t)(octet & 0x7f) << shift;
		if ((octet & 0x80) == 0) {
			*out = v;
			return 0;
		}
		shift += 7;
	}
	return -1; /* truncated or more than 64 bits */
}

/* next (field, wire) pair; < 0 when the message is exhausted or malformed */
static int pb_next(PBRead_t *r, uint32_t *field, int *wire)
{
	uint64_t tag;

	if (pb_read_varint(r, &tag) < 0 || tag == 0)
		return -1;
	*field = (uint32_t)(tag >> 3);
	*wire = (int)(tag & 7);
	if (*field == 0)
		return -1;
	switch (*wire) {
	case 0:
	case 1:
	case 2:
	case 5:
		return 0;
	default:
		return -1; /* deprecated group wire types */
	}
}

static int pb_skip(PBRead_t *r, int wire)
{
	uint64_t v;

	switch (wire) {
	case 0:
		return pb_read_varint(r, &v);
	case 1:
		if (r->pos + 8 > r->len)
			return -1;
		r->pos += 8;
		return 0;
	case 5:
		if (r->pos + 4 > r->len)
			return -1;
		r->pos += 4;
		return 0;
	case 2: {
		uint64_t n;

		if (pb_read_varint(r, &n) < 0 || n > r->len - r->pos)
			return -1;
		r->pos += n;
		return 0;
	}
	}
	return -1;
}

/*
 * Fetch the @nth (1-based) length-delimited field @field.
 * Returns 0 on success, -2 when the message ends without it, < 0 otherwise.
 */
static int pb_get_bytes(PBRead_t *r, uint32_t field, uint64_t nth,
                        const uint8_t **out, size_t *outlen)
{
	uint64_t count = 0;

	while (1) {
		uint32_t f;
		int w;

		if (r->pos == r->len)
			return -2;
		if (pb_next(r, &f, &w) < 0)
			return -1;
		if (w != 2) {
			if (pb_skip(r, w) < 0)
				return -1;
			continue;
		}
		{
			uint64_t n;

			if (pb_read_varint(r, &n) < 0 || n > r->len - r->pos)
				return -1;
			if (f == field && ++count >= nth) {
				*out = r->p + r->pos;
				r->pos += n;
				if (outlen != NULL)
					*outlen = (size_t)n;
				return 0;
			}
			r->pos += n;
		}
	}
}

/* ***************************** */
/* Device file (.wvd)            */
/* ***************************** */

typedef struct WvDevice_s
{
	EVP_PKEY *pkey;         /* private RSA key from the device file */
	int is_android;         /* device type byte == 2              */
	uint8_t *client_id;     /* serialized client id, owned        */
	size_t client_id_len;
} WvDevice_t;

static void wv_device_free(WvDevice_t *d)
{
	if (d->pkey != NULL)
		EVP_PKEY_free(d->pkey);
	free((void *)d->client_id);
	memset(d, 0, sizeof(*d));
}

/*
 * Layout: "WVD" | version(1) | type_(1: 1=chrome, 2=android) | sec_level(1)
 *         flags(1) | key_len(u16be) | private_key (PKCS#8 DER)
 *         cid_len(u16be) | client_id   [v1 adds a trailing vmp blob]
 */
static int load_wv_device(const char *path, WvDevice_t *out)
{
	FILE *f;
	long size = -1;
	uint8_t *file = NULL;
	const unsigned char *kp;
	size_t pos = 0;
	size_t key_len, cid_len;
	int rc = -1;

	memset(out, 0, sizeof(*out));
	if (path == NULL || out == NULL)
		return -1;

	f = fopen(path, "rb");
	if (f == NULL) {
		ffmpeg_printf(2, "container drm: device file '%s' not found\n", path);
		return -1;
	}
	if (fseek(f, 0, SEEK_END) != 0 ||
	    (size = ftell(f)) <= 0 || size > WVD_FILE_MAX ||
	    fseek(f, 0, SEEK_SET) != 0) {
		ffmpeg_printf(2, "container drm: device file '%s' unreadable\n", path);
		fclose(f);
		return -1;
	}

	file = malloc((size_t)size);
	if (file == NULL || fread(file, 1, (size_t)size, f) != (size_t)size) {
		ffmpeg_printf(2, "container drm: failed to read device file\n");
		free(file);
		fclose(f);
		return -1;
	}
	fclose(f);

	if ((size_t)size < 3 + 5 + 2 || memcmp(file, "WVD", 3) != 0) {
		ffmpeg_printf(2, "container drm: '%s' is not a valid device file\n", path);
		goto done;
	}
	pos = 3;
	{
		uint8_t version = file[pos++];

		if (version != 1 && version != 2) {
			ffmpeg_printf(2, "container drm: unsupported device file version %u\n", version);
			goto done;
		}
	}
	out->is_android = (file[pos] == 2); /* type_ */
	pos += 3;                          /* type_, security_level, flags */

	if ((size_t)size < pos + 2)
		goto done;
	key_len = ((size_t)file[pos] << 8) | file[pos + 1];
	pos += 2;
	if (key_len == 0 || key_len > (size_t)size - pos)
		goto done;
	kp = file + pos;
	pos += key_len;

	if ((size_t)size < pos + 2)
		goto done;
	cid_len = ((size_t)file[pos] << 8) | file[pos + 1];
	pos += 2;
	if (cid_len == 0 || cid_len > (size_t)size - pos) {
		ffmpeg_printf(2, "container drm: device file has no client id\n");
		goto done;
	}

	/* PKCS#8 first, plain RSA PRIVATE KEY DER as a fallback */
	out->pkey = d2i_AutoPrivateKey(NULL, &kp, (long)key_len);
	if (out->pkey == NULL) {
		char *pem = pem_wrap("RSA PRIVATE KEY", file + pos - key_len, key_len);

		if (pem != NULL) {
			BIO *bio = BIO_new_mem_buf(pem, -1);

			if (bio != NULL) {
				out->pkey = PEM_read_bio_PrivateKey(bio, NULL, NULL, NULL);
				BIO_free(bio);
			}
			free(pem);
		}
	}
	if (out->pkey == NULL || EVP_PKEY_base_id(out->pkey) != EVP_PKEY_RSA) {
		ffmpeg_printf(2, "container drm: failed to load the RSA private key\n");
		wv_device_free(out);
		out->pkey = NULL;
		goto done;
	}

	out->client_id = malloc(cid_len);
	if (out->client_id == NULL)
		goto done;
	memcpy(out->client_id, file + pos, cid_len);
	out->client_id_len = cid_len;
	rc = 0;

done:
	free(file);
	if (rc < 0 && out->pkey != NULL) {
		EVP_PKEY_free(out->pkey);
		out->pkey = NULL;
	}
	return rc;
}

/* ***************************** */
/* PSSH box                      */
/* ***************************** */

/*
 * Validate a full Widevine PSSH box and locate its init_data payload:
 * everything after the system id (and, for v1 boxes, the key id array),
 * without the 4-byte length prefix. The leading u32 size field is optional;
 * when present it must match the amount of data given.
 */
static int pssh_init_data(const uint8_t *box, size_t len, const uint8_t **init, size_t *init_len)
{
	size_t pos = 0;
	uint8_t version;

	if (len < 4 + 1 + 3 + 16 + 4)      /* type ver/flags sid u32 data */
		return -1;

	if (memcmp(box, "pssh", 4) != 0) { /* box with a leading size field */
		uint64_t declared = be32_get(box);

		if (declared < 1 + 3 + 16 + 4 || declared > len)
			return -1;
		len = (size_t)declared;         /* ignore anything past the box */
		pos = 4;
	}
	if (memcmp(box + pos, "pssh", 4) != 0)
		return -1;
	pos += 4;

	version = box[pos];                 /* version byte */
	if (version > 1 || box[pos + 1] != 0 || box[pos + 2] != 0 || box[pos + 3] != 0)
		return -1; /* flags must be zero */
	pos += 4;
	if (memcmp(box + pos, WV_SYSTEM_ID, 16) != 0)
		return -1;
	pos += 16;

	if (version == 1) { /* v1: key id array in front of the init data */
		uint32_t count = be32_get(box + pos);

		if (count > 8 || (size_t)count * 16 + 4 > len - pos)
			return -1;
		pos += 4 + (size_t)count * 16;
	}

	if (len - pos < 4)
		return -1;
	if ((uint64_t)be32_get(box + pos) + 4 != len - pos)
		return -1; /* length prefix must span the rest of the box */
	pos += 4;
	if (pos == len)
		return -1;

	*init = box + pos;
	*init_len = len - pos;
	return 0;
}

/* ***************************** */
/* Crypto (OpenSSL, session key and derived keys) */
/* ***************************** */

/* RSASSA-PSS over a SHA-1 digest: MGF1-SHA1, salt length 20 */
static int rsa_pss_sign_sha1(EVP_PKEY *pk, const uint8_t *digest, size_t diglen, DBuf_t *out)
{
	EVP_PKEY_CTX *ctx;
	size_t siglen = 0;
	int rc;

	ctx = EVP_PKEY_CTX_new(pk, NULL);   /* 1.0.x .. 3.x; _new_from_pkey is 3.0 only */
	if (ctx == NULL)
		return -1;
	rc = -1;
	if (EVP_PKEY_sign_init(ctx) > 0 &&
	    EVP_PKEY_CTX_set_rsa_padding(ctx, RSA_PKCS1_PSS_PADDING) > 0 &&
	    EVP_PKEY_CTX_set_signature_md(ctx, EVP_sha1()) > 0 &&
	    EVP_PKEY_CTX_set_rsa_mgf1_md(ctx, EVP_sha1()) > 0 &&
	    EVP_PKEY_CTX_set_rsa_pss_saltlen(ctx, (int)diglen) > 0 &&
	    EVP_PKEY_sign(ctx, NULL, &siglen, digest, diglen) > 0 &&
	    dbuf_reserve(out, siglen) == 0 &&
	    EVP_PKEY_sign(ctx, out->data + out->len, &siglen, digest, diglen) > 0) {
		out->len += siglen;
		rc = 0;
	}
	EVP_PKEY_CTX_free(ctx);
	return rc;
}

/* RSA-OAEP (SHA-1, MGF1-SHA1) decryption with the device private key */
static int rsa_oaep_decrypt_sha1(EVP_PKEY *pk, const uint8_t *ct, size_t ctlen, DBuf_t *out)
{
	EVP_PKEY_CTX *ctx;
	size_t plen = 0;
	int rc;

	ctx = EVP_PKEY_CTX_new(pk, NULL);   /* 1.0.x .. 3.x; _new_from_pkey is 3.0 only */
	if (ctx == NULL)
		return -1;
	rc = -1;
	if (EVP_PKEY_decrypt_init(ctx) > 0 &&
	    EVP_PKEY_CTX_set_rsa_padding(ctx, RSA_PKCS1_OAEP_PADDING) > 0 &&
	    EVP_PKEY_CTX_set_rsa_oaep_md(ctx, EVP_sha1()) > 0 &&
	    EVP_PKEY_CTX_set_rsa_mgf1_md(ctx, EVP_sha1()) > 0 &&
	    EVP_PKEY_decrypt(ctx, NULL, &plen, ct, ctlen) > 0 &&
	    dbuf_reserve(out, plen) == 0 &&
	    EVP_PKEY_decrypt(ctx, out->data + out->len, &plen, ct, ctlen) > 0) {
		out->len += plen;
		rc = 0;
	}
	EVP_PKEY_CTX_free(ctx);
	return rc;
}

/* single-shot AES-128-CBC decryption with PKCS#7 unpadding */
static int aes_cbc_decrypt(const uint8_t *key, const uint8_t *iv, const uint8_t *in, size_t inlen, DBuf_t *out)
{
	EVP_CIPHER_CTX *ctx;
	int len = 0, final_len = 0, rc;

	if (inlen == 0 || inlen % 16 != 0)
		return -1;
	ctx = EVP_CIPHER_CTX_new();
	if (ctx == NULL)
		return -1;
	rc = -1;
	if (EVP_DecryptInit_ex(ctx, EVP_aes_128_cbc(), NULL, key, iv) > 0 &&
	    dbuf_reserve(out, inlen + 16) == 0 &&
	    EVP_DecryptUpdate(ctx, out->data + out->len, &len, in, (int)inlen) > 0 &&
	    EVP_DecryptFinal_ex(ctx, out->data + out->len + len, &final_len) > 0) {
		out->len += (size_t)len + (size_t)final_len;
		rc = 0; /* DecryptFinal enforces the padding */
	} else {
		ffmpeg_printf(2, "container drm: key material unwrap failed\n");
	}
	EVP_CIPHER_CTX_free(ctx);
	return rc;
}

/* left shift by one bit of a 16-byte block, xor 0x87 on overflow */
static void cmac_dbl(uint8_t b[16])
{
	int i;
	uint8_t carry = (uint8_t)(b[0] >> 7);

	for (i = 0; i < 15; i++)
		b[i] = (uint8_t)((b[i] << 1) | (b[i + 1] >> 7));
	b[15] = (uint8_t)(b[15] << 1);
	if (carry)
		b[15] ^= 0x87;
}

static int aes_ecb_encrypt_block(const uint8_t *key, const uint8_t *in, uint8_t out[16])
{
	EVP_CIPHER_CTX *ctx = EVP_CIPHER_CTX_new();
	int len = 0, finlen = 0, rc = -1;

	if (ctx == NULL)
		return -1;
	if (EVP_EncryptInit_ex(ctx, EVP_aes_128_ecb(), NULL, key, NULL) > 0 &&
	    EVP_CIPHER_CTX_set_padding(ctx, 0) > 0 &&
	    EVP_EncryptUpdate(ctx, out, &len, in, 16) > 0 && len == 16 &&
	    EVP_EncryptFinal_ex(ctx, out + len, &finlen) == 1)
		rc = 0;
	EVP_CIPHER_CTX_free(ctx);
	return rc;
}

static void xor_block(uint8_t a[16], const uint8_t b[16])
{
	int i;

	for (i = 0; i < 16; i++)
		a[i] ^= b[i];
}

/* AES-CMAC (NIST SP 800-38B), 128-bit result */
static int aes_cmac(const uint8_t *key, const uint8_t *msg, size_t len, uint8_t out[16])
{
	uint8_t subk[16];
	uint8_t x[16] = { 0 };
	uint8_t m[16];
	size_t nblocks;
	int complete, i;

	if (len == 0)
		return -1;
	nblocks = (len + 15) / 16;
	complete = (int)(len % 16 == 0);

	/* subkey: dbl(E_k(0^128)) for a full final block, dbl(dbl(...)) otherwise */
	if (aes_ecb_encrypt_block(key, x, subk) < 0)     /* E_k(0^128)      */
		return -1;
	cmac_dbl(subk);                                    /* now: dbl(E_k(0))   */
	if (!complete)
		cmac_dbl(subk);                                /* now: dbl(dbl(E_k(0))) */

	for (i = 0; i < (int)nblocks; i++) {
		size_t off = (size_t)i * 16;
		int last = (i == (int)nblocks - 1);

		if (!last) {
			memcpy(m, msg + off, 16);
		} else if (complete) {
			memcpy(m, msg + off, 16);
			xor_block(m, subk);
		} else {
			size_t rem = len - off;

			memset(m, 0, 16);
			memcpy(m, msg + off, rem);
			m[rem] ^= 0x80;
			xor_block(m, subk);
		}

		xor_block(x, m);                              /* X_i = x xor M'_i */
		if (aes_ecb_encrypt_block(key, x, x) < 0)      /* AES_k(...)       */
			return -1;
		if (last)
			memcpy(out, x, 16);                      /* T = AES_k(X_{n-1} xor M'_n) */
	}

	return 0;
}

/* varint field: tag + value */
static int pb_put_vfield(DBuf_t *b, uint32_t field, uint64_t v)
{
	if (pb_field(b, field, 0) < 0 || pb_put_varint(b, v) < 0)
		return -1;
	return 0;
}

/* HMAC-SHA256 over two concatenated message parts (either may be empty) */
static int hmac_sha256(const uint8_t *key, size_t klen, const uint8_t *m1, size_t l1,
                       const uint8_t *m2, size_t l2, uint8_t out[32])
{
	EVP_MD_CTX *ctx;
	uint8_t block[64];
	uint8_t hashed[32];
	uint8_t inner[32];
	const uint8_t *k = key;
	size_t kl = klen;
	unsigned int dl = 0;
	int i, rc = -1;

	if (key == NULL || klen == 0)
		return -1;

	ctx = EVP_MD_CTX_new();
	if (ctx == NULL)
		return -1;

	if (kl > sizeof(hashed)) {
		unsigned int hl = 0;

		if (EVP_Digest(key, klen, hashed, &hl, EVP_sha256(), NULL) != 1 || hl != sizeof(hashed))
			goto done;
		k = hashed;
		kl = sizeof(hashed);
	}

	for (i = 0; i < 64; i++)
		block[i] = (uint8_t)((((size_t)i < kl) ? k[i] : 0x00) ^ 0x36);   /* ipad, zero-padded */
	if (EVP_DigestInit_ex(ctx, EVP_sha256(), NULL) <= 0 ||
	    EVP_DigestUpdate(ctx, block, sizeof(block)) <= 0 ||
	    (l1 > 0 && EVP_DigestUpdate(ctx, m1, l1) <= 0) ||
	    (l2 > 0 && EVP_DigestUpdate(ctx, m2, l2) <= 0) ||
	    EVP_DigestFinal_ex(ctx, inner, &dl) <= 0 || dl != sizeof(inner))
		goto done;

	for (i = 0; i < 64; i++)
		block[i] = (uint8_t)((((size_t)i < kl) ? k[i] : 0x00) ^ 0x5c);   /* opad, zero-padded */
	if (EVP_DigestInit_ex(ctx, EVP_sha256(), NULL) <= 0 ||
	    EVP_DigestUpdate(ctx, block, sizeof(block)) <= 0 ||
	    EVP_DigestUpdate(ctx, inner, sizeof(inner)) <= 0 ||
	    EVP_DigestFinal_ex(ctx, out, &dl) <= 0 || dl != 32)
		goto done;

	rc = 0;
done:
	EVP_MD_CTX_free(ctx);
	return rc;
}

/* one CMAC block with a counter byte in front of the context */
static int cmac_derive(const uint8_t *session_key, int counter, const uint8_t *ctx, size_t ctxlen, uint8_t out[16])
{
	uint8_t *in;
	int rc = -1;

	if (ctxlen > SIZE_MAX - 1)
		return -1;
	in = malloc(ctxlen + 1);
	if (in == NULL)
		return -1;
	in[0] = (uint8_t)counter;
	memcpy(in + 1, ctx, ctxlen);
	rc = aes_cmac(session_key, in, ctxlen + 1, out);
	free(in);
	return rc;
}

/*
 * Key derivation of the license protocol:
 *   enc_key        = CMAC(context "ENCRYPTION"    + key size 128)
 *   mac_key_server = CMAC("AUTHENTICATION" + 512, counter 1..2)
 */
static int derive_keys(const uint8_t *session_key, const uint8_t *lr_bytes, size_t lr_len,
                       uint8_t enc_key[16], uint8_t mac_server[32])
{
	uint8_t *enc_ctx = NULL;
	uint8_t *mac_ctx = NULL;
	size_t enclen = 10 + 1 + lr_len + 4;
	size_t maclen = 14 + 1 + lr_len + 4;
	int rc = -1;

	if (lr_bytes == NULL || lr_len == 0)
		return -1;
	enc_ctx = malloc(enclen);
	mac_ctx = malloc(maclen);
	if (enc_ctx == NULL || mac_ctx == NULL) {
		free(enc_ctx);
		free(mac_ctx);
		return -1;
	}

	memcpy(enc_ctx, "ENCRYPTION", 10);
	enc_ctx[10] = 0x00;
	memcpy(enc_ctx + 11, lr_bytes, lr_len);
	enc_ctx[enclen - 4] = (uint8_t)(128u >> 24); enc_ctx[enclen - 3] = (uint8_t)(128u >> 16);
	enc_ctx[enclen - 2] = (uint8_t)(128u >> 8);  enc_ctx[enclen - 1] = (uint8_t)128u;

	memcpy(mac_ctx, "AUTHENTICATION", 14);
	mac_ctx[14] = 0x00;
	memcpy(mac_ctx + 15, lr_bytes, lr_len);
	mac_ctx[maclen - 4] = (uint8_t)(512u >> 24); mac_ctx[maclen - 3] = (uint8_t)(512u >> 16);
	mac_ctx[maclen - 2] = (uint8_t)(512u >> 8);  mac_ctx[maclen - 1] = (uint8_t)512u;

	if (cmac_derive(session_key, 1, enc_ctx, enclen, enc_key) == 0 &&
	    cmac_derive(session_key, 1, mac_ctx, maclen, mac_server) == 0 &&
	    cmac_derive(session_key, 2, mac_ctx, maclen, mac_server + 16) == 0)
		rc = 0;

	free(enc_ctx);
	free(mac_ctx);
	return rc;
}

/* ***************************** */
/* License server transport      */
/* ***************************** */

typedef struct RespBuf_s
{
	uint8_t *data;
	size_t len, cap_max;
	int truncated;
} RespBuf_t;

static size_t resp_write_cb(void *ptr, size_t size, size_t nmemb, void *ud)
{
	RespBuf_t *b = ud;
	size_t add = size * nmemb;

	if (add == 0)
		return 0;
	if (b->len < b->cap_max) {
		size_t take = add;

		if (b->len + take > b->cap_max)
			take = b->cap_max - b->len;
		memcpy(b->data + b->len, ptr, take);
		b->len += take;
	} else {
		b->truncated = 1;
	}
	return add; /* keep the transfer going even if we stop storing */
}

/* POST a binary body with optional extra "Name: value" header lines */
static int http_post_binary(const char *url, const uint8_t *body, size_t body_len, long timeout_ms,
                            size_t max_bytes, const char *const *headers, size_t n_headers,
                            RespBuf_t *out, long *http_code)
{
	CURL *e;
	CURLcode rc;
	struct curl_slist *hdrs = NULL;
	size_t i;

	if (url == NULL || body == NULL || out == NULL || http_code == NULL)
		return -1;

	pthread_once(&curl_init_once, curl_init_once_cb);

	out->data = malloc(max_bytes ? max_bytes : 65536);
	if (out->data == NULL) {
		ffmpeg_printf(2, "container drm: out of memory\n");
		return -1;
	}
	out->len = 0;
	out->cap_max = max_bytes ? max_bytes : 65536;
	out->truncated = 0;

	e = curl_easy_init();
	if (e == NULL) {
		free(out->data);
		out->data = NULL;
		return -1;
	}

	/* some license services (e.g. DRMtoday) reject the request when a Content-Type is
	 * present at all, so suppress libcurl's default form type unless one was explicitly
	 * requested through "license_headers" */
	for (i = 0; i < n_headers && headers != NULL; i++) {
		if (headers[i] == NULL || headers[i][0] == '\0')
			continue;
		hdrs = curl_slist_append(hdrs, headers[i]);   /* keeps the head on success */
	}
	{
		int have_ct = 0;

		for (i = 0; i < n_headers && headers != NULL; i++) {
			if (headers[i] != NULL && strncasecmp(headers[i], "Content-Type", 12) == 0) {
				have_ct = 1;
				break;
			}
		}
		if (!have_ct)
			hdrs = curl_slist_append(hdrs, "Content-Type:");   /* empty value suppresses the default */
	}

	curl_easy_setopt(e, CURLOPT_URL, url);
	curl_easy_setopt(e, CURLOPT_NOSIGNAL, 1L);
	curl_easy_setopt(e, CURLOPT_SSL_VERIFYPEER, 0L);   /* box CA store may not verify the CDN chain */
	curl_easy_setopt(e, CURLOPT_SSL_VERIFYHOST, 0L);
	curl_easy_setopt(e, CURLOPT_CONNECTTIMEOUT_MS, (long)DRM_CONNECT_TIMEOUT_MS);
	curl_easy_setopt(e, CURLOPT_TIMEOUT_MS, timeout_ms);
	curl_easy_setopt(e, CURLOPT_POST, 1L);
	if (hdrs != NULL)
		curl_easy_setopt(e, CURLOPT_HTTPHEADER, hdrs);
	curl_easy_setopt(e, CURLOPT_WRITEFUNCTION, resp_write_cb);
	curl_easy_setopt(e, CURLOPT_WRITEDATA, out);
	curl_easy_setopt(e, CURLOPT_POSTFIELDS, body);
	curl_easy_setopt(e, CURLOPT_POSTFIELDSIZE, (long)body_len);

	rc = curl_easy_perform(e);
	if (rc == CURLE_OK) {
		long code = 0;

		curl_easy_getinfo(e, CURLINFO_RESPONSE_CODE, &code);
		*http_code = code;
	} else {
		ffmpeg_printf(2, "container drm: request to %s failed: %s\n", url, curl_easy_strerror(rc));
	}

	if (hdrs != NULL)
		curl_slist_free_all(hdrs);
	curl_easy_cleanup(e);

	if (rc != CURLE_OK || out->truncated) {
		free(out->data);
		out->data = NULL;
		return -1;
	}
	return 0;
}

/* ***************************** */
/* License response handling     */
/* ***************************** */

typedef struct SignedMsg_s
{
	uint64_t type;      /* LICENSE_REQUEST=1, LICENSE=2   */
	const uint8_t *msg;
	size_t msg_len;
	const uint8_t *signature;
	size_t sig_len;
	const uint8_t *session_key;
	size_t sk_len;
	const uint8_t *core_msg;     /* oemcrypto_core_message, may be empty */
	size_t core_len;
} SignedMsg_t;

/* single pass, field order on the wire does not matter (last one wins) */
static int parse_signed_message(const uint8_t *buf, size_t len, SignedMsg_t *out)
{
	PBRead_t r = { buf, len, 0 };

	memset(out, 0, sizeof(*out));

	while (r.pos < len) {
		uint32_t f;
		int w;

		if (pb_next(&r, &f, &w) != 0)
			return -1;
		switch (w) {
		case 0: {
			uint64_t v;

			if (pb_read_varint(&r, &v) < 0)
				return -1;
			if (f == 1)      /* MessageType */
				out->type = v;
			break;
		}
		case 2: {
			uint64_t n;

			if (pb_read_varint(&r, &n) < 0 || n > len - r.pos)
				return -1;
			switch (f) {
			case 2: out->msg = buf + r.pos;             out->msg_len = (size_t)n; break;
			case 3: out->signature = buf + r.pos;       out->sig_len = (size_t)n; break;
			case 4: out->session_key = buf + r.pos;     out->sk_len = (size_t)n; break;
			case 9: out->core_msg = buf + r.pos;        out->core_len = (size_t)n; break;
			default: break;                             /* attestation/metrics/version */
			}
			r.pos += n;
			break;
		}
		default:
			if (pb_skip(&r, w) < 0)      /* fixed32/64 and the like */
				return -1;
		}
	}

	if (out->type == 0 || out->msg == NULL)   /* type and msg are required */
		return -1;
	return 0;
}

/* one KeyContainer decoded in a single pass; field order on the wire does not matter */
typedef struct KeyCont_s
{
	const uint8_t *id;      /* key id (kid)         */
	size_t idlen;
	const uint8_t *iv;      /* CBC iv               */
	size_t ivlen;
	const uint8_t *kmat;    /* wrapped key material */
	size_t kmatlen;
	uint64_t type;          /* KeyType, 0 when absent */
} KeyCont_t;

static int parse_key_container(const uint8_t *buf, size_t len, KeyCont_t *out)
{
	PBRead_t r = { buf, len, 0 };

	memset(out, 0, sizeof(*out));

	while (r.pos < len) {
		uint32_t f;
		int w;

		if (pb_next(&r, &f, &w) != 0)
			return -1;
		switch (w) {
		case 0: {
			uint64_t v;

			if (pb_read_varint(&r, &v) < 0)
				return -1;
			if (f == 4)      /* KeyType */
				out->type = v;
			break;
		}
		case 2: {
			uint64_t n;

			if (pb_read_varint(&r, &n) < 0 || n > len - r.pos)
				return -1;
			switch (f) {
			case 1: out->id = buf + r.pos;   out->idlen = (size_t)n; break;
			case 2: out->iv = buf + r.pos;   out->ivlen = (size_t)n; break;
			case 3: out->kmat = buf + r.pos; out->kmatlen = (size_t)n; break;
			default: break;                  /* level / key_control / permissions */
			}
			r.pos += n;
			break;
		}
		default:
			if (pb_skip(&r, w) < 0)
				return -1;
		}
	}
	return 0;
}

/* walk License.key[] (repeated KeyContainer) and unwrap the content keys.
 *
 * The wrapped material is a PKCS#7 padded AES-128 key in CBC mode;
 * aes_cbc_decrypt() enforces the padding, so on success it yields the
 * 16-byte key directly:
 *   key = aes_cbc_decrypt(enc_key, kc.iv, kc.kmat)
 */
static int extract_license_keys(const uint8_t *license, size_t len, const uint8_t enc_key[16],
                                drm_wv_key_t **keys_out, size_t *n_keys)
{
	PBRead_t r = { license, len, 0 };
	drm_wv_key_t *arr = NULL;
	size_t cap = 0, count = 0;
	int rc_final = -1;

	*keys_out = NULL;
	*n_keys = 0;

	while (1) {
		const uint8_t *cont;
		size_t cont_len;
		KeyCont_t kc;
		DBuf_t dec = { NULL, 0, 0 };
		int rc;

		rc = pb_get_bytes(&r, 3, 1, &cont, &cont_len); /* next KeyContainer (repeated) */
		if (rc == -2) { rc_final = 0; break; }          /* clean end of the license */
		if (rc != 0 || parse_key_container(cont, cont_len, &kc) < 0)
			break;

		if (kc.type == 1 /* SIGNING */) {
			ffmpeg_printf(2, "container drm: skipping signing key\n");
			continue;
		}
		if (kc.idlen != 16 || kc.ivlen != 16 || kc.kmatlen % 16 != 0 || kc.kmatlen == 0) {
			ffmpeg_printf(2, "container drm: skipping unusable key entry (type=%llu)\n",
			             (unsigned long long)kc.type);
			continue;
		}

		if (aes_cbc_decrypt(enc_key, kc.iv, kc.kmat, kc.kmatlen, &dec) < 0 || dec.len != 16) {
			ffmpeg_printf(2, "container drm: key material is not a padded AES-128 key\n");
			free(dec.data);
			continue;
		}

		if (count == cap) {
			size_t ncap = cap ? cap * 2 : 4;
			drm_wv_key_t *na = realloc(arr, ncap * sizeof(*arr));

			if (na == NULL) {
				free(dec.data);
				break;
			}
			arr = na;
			cap = ncap;
		}
		memcpy(arr[count].kid, kc.id, 16);
		memcpy(arr[count].key, dec.data + dec.len - 16, 16);
		count++;
		free(dec.data);
	}

	if (rc_final == 0) {
		*keys_out = arr;   /* may stay NULL when no usable key was found */
		*n_keys = count;
		return 0;          /* round-trip ok, the caller checks *n_keys */
	}
	free(arr);
	return -1;
}

static int try_license_binary(const uint8_t *body, size_t len, WvDevice_t *dev,
                              const uint8_t *lr_bytes, size_t lr_len,
                              drm_wv_key_t **keys_out, size_t *n_keys)
{
	SignedMsg_t sm;
	uint8_t enc_key[16];
	uint8_t mac_server[32];
	DBuf_t skey = { NULL, 0, 0 };
	int rc = -1;

	*keys_out = NULL;
	*n_keys = 0;
	if (len == 0)
		return -1;

	if (parse_signed_message(body, len, &sm) < 0 || sm.type != 2 /* LICENSE */) {
		ffmpeg_printf(2, "container drm: response is not a license message\n");
		return -1;
	}
	if (sm.signature == NULL || sm.session_key == NULL) {
		ffmpeg_printf(2, "container drm: license message is incomplete\n");
		return -1;
	}

	/* unwrap the session key with the device private key */
	if (rsa_oaep_decrypt_sha1(dev->pkey, sm.session_key, sm.sk_len, &skey) < 0 || skey.len != 16) {
		ffmpeg_printf(2, "container drm: failed to decrypt the license session key\n");
		goto done;
	}

	/* derive the enc/mac keys from the request we sent */
	if (derive_keys(skey.data, lr_bytes, lr_len, enc_key, mac_server) < 0) {
		ffmpeg_printf(2, "container drm: key derivation failed\n");
		goto done;
	}

	/* verify: HMAC-SHA256(mac_key_server, oemcrypto_core_message || msg) == signature */
	if (sm.sig_len != 32) {
		ffmpeg_printf(2, "container drm: unexpected license signature size %zu\n", sm.sig_len);
		goto done;
	}
	{
		uint8_t computed[32];

		if (hmac_sha256(mac_server, sizeof(mac_server),
		                sm.core_msg, sm.core_len, sm.msg, sm.msg_len, computed) < 0 ||
		    CRYPTO_memcmp(computed, sm.signature, 32) != 0) {
			ffmpeg_printf(2, "container drm: license signature verification failed\n");
			goto done;
		}
	}

	rc = extract_license_keys(sm.msg, sm.msg_len, enc_key, keys_out, n_keys);
	if (rc == 0 && *n_keys > 0)
		ffmpeg_printf(2, "container drm: license holds %zu usable key(s)\n", *n_keys);

done:
	free(skey.data);
	return rc;
}

/* advance past the JSON value starting at body[*pi] */
static int json_skip_value(const char *body, size_t len, size_t *pi)
{
	size_t i = *pi;

	if (i >= len)
		return -1;
	switch (body[i]) {
	case '"':
		i++;
		while (i < len && body[i] != '"') {
			if (body[i] == '\\' && i + 1 < len)
				i++;
			i++;
		}
		if (i >= len)
			return -1;
		*pi = i + 1;
		return 0;
	case '{':
	case '[': {
		char open = body[i];
		char close_c = (open == '{') ? '}' : ']';
		int depth = 0;

		i++;
		while (i < len) {
			if (body[i] == '"') {
				i++;
				while (i < len && body[i] != '"') {
					if (body[i] == '\\' && i + 1 < len)
						i++;
					i++;
				}
				if (i >= len)
					return -1;
			} else if (body[i] == open) {
				depth++;
			} else if (body[i] == close_c && --depth == 0) {
				*pi = i + 1;
				return 0;
			}
			i++;
		}
		return -1; /* unbalanced */
	}
	default: /* number, true, false, null */
		while (i < len && body[i] != ',' && body[i] != '}' && body[i] != ']' &&
		       body[i] != ' ' && body[i] != '\t' && body[i] != '\r' && body[i] != '\n')
			i++;
		*pi = i;
		return 0;
	}
}

typedef struct B64Cand_s
{
	uint8_t *data;
	size_t len;
} B64Cand_t;

/*
 * Collect the base64 string values of all keys whose name contains
 * "license" (any nesting depth, document order).
 */
static int json_find_license_candidates(const char *body, size_t len, B64Cand_t **list_out, size_t *n_out)
{
	B64Cand_t *list = NULL;
	size_t n = 0, cap = 8;
	size_t i = 0;

	*list_out = NULL;
	*n_out = 0;
	if (body == NULL || len == 0)
		return -1;

	list = calloc(cap, sizeof(*list));
	if (list == NULL)
		return -1;

	while (i < len && body[i] != '"')
		i++;

	while (i < len) {
		size_t kstart = i + 1;
		size_t kend = kstart;
		char name[96];
		size_t nl, j;
		int is_candidate = 0;

		while (i < len && (body[i] == ' ' || body[i] == '\t' || body[i] == '\r' || body[i] == '\n' || body[i] == ','))
			i++;
		if (i >= len || body[i] != '"')
			break;

		while (kend < len && body[kend] != '"' && body[kend] != '\\')
			kend++;
		if (kend >= len)      /* unterminated key: stop */
			break;

		nl = kend - kstart;
		if (nl < sizeof(name)) {
			memcpy(name, body + kstart, nl);
			name[nl] = '\0';
			for (j = 0; name[j]; j++)
				if (name[j] >= 'A' && name[j] <= 'Z')
					name[j] += 32;

			is_candidate = strstr(name, "license") != NULL;
		}

		i = kend + 1;         /* after the closing quote of the key */
		while (i < len && (body[i] == ' ' || body[i] == '\t' || body[i] == '\r' || body[i] == '\n'))
			i++;
		if (i >= len || body[i] != ':') {   /* not a key:value pair */
			while (i < len && body[i] != '"')
				i++;
			continue;
		}
		i++;                   /* past the colon */
		while (i < len && (body[i] == ' ' || body[i] == '\t' || body[i] == '\r' || body[i] == '\n'))
			i++;

		if (!is_candidate) {
			(void)json_skip_value(body, len, &i); /* discard the value */
			continue;
		}

		if (i >= len || body[i] != '"') {       /* value is not a string: skip it */
			(void)json_skip_value(body, len, &i);
			continue;
		}
		{
			size_t vstart = i + 1;
			size_t vend = vstart;

			while (vend < len && body[vend] != '"' && body[vend] != '\\')
				vend++;
			if (vend >= len) {
				i = len;
				break;
			}

			{
				uint8_t *dec;
				size_t dlen = 0;

				dec = b64_decode(body + vstart, vend - vstart, &dlen);
				if (dec != NULL && n < cap) {
					list[n].data = dec;
					list[n].len = dlen;
					n++;
				} else if (dec == NULL) {
					ffmpeg_printf(2, "container drm: candidate license value is not base64\n");
				}
			}
			i = vend + 1;
		}
	}

	if (n > 0) {
		*list_out = list;
		*n_out = n;
		return 0;
	}
	free(list);
	return -1; /* no usable candidates */
}

/* binary first, then an embedded base64 license in text/JSON bodies */
static int license_body_to_keys(const uint8_t *body, size_t body_len, WvDevice_t *dev,
                                const uint8_t *lr_bytes, size_t lr_len,
                                drm_wv_key_t **keys_out, size_t *n_keys)
{
	const uint8_t *p = body;
	size_t l = body_len;

	*keys_out = NULL;
	*n_keys = 0;
	if (body == NULL || body_len == 0) {
		ffmpeg_printf(2, "container drm: empty license response\n");
		return -1;
	}

	if (try_license_binary(body, body_len, dev, lr_bytes, lr_len, keys_out, n_keys) == 0)
		return 0; /* round-trip ok, even with zero usable content keys */

	while (l > 0 && (*p == ' ' || *p == '\t' || *p == '\r' || *p == '\n')) { p++; l--; }
	if (l == 0 || (*p != '{' && *p != '[')) {
		ffmpeg_printf(2, "container drm: unrecognized license response format\n");
		return -1;
	}

	ffmpeg_printf(2, "container drm: response is not a binary license, scanning for an embedded one\n");
	{
		B64Cand_t *list = NULL;
		size_t n = 0;
		int rc = -1;

		if (json_find_license_candidates((const char *)p, l, &list, &n) == 0) {
			size_t k;
			int ok = -1;

			for (k = 0; k < n && ok != 0; k++)
				ok = try_license_binary(list[k].data, list[k].len, dev, lr_bytes, lr_len, keys_out, n_keys);
			rc = ok;

			for (k = 0; k < n; k++)
				free(list[k].data);
			free(list);
		} else {
			ffmpeg_printf(2, "container drm: no usable license value found in the response\n");
		}
		return rc;
	}
}

/* ***************************** */
/* License request               */
/* ***************************** */

static int build_license_request(WvDevice_t *dev, const uint8_t *init_data, size_t init_len, DBuf_t *lr)
{
	DBuf_t wvpsd = { NULL, 0, 0 };
	DBuf_t cid = { NULL, 0, 0 };
	DBuf_t rid = { NULL, 0, 0 };
	uint64_t nonce;
	int rc = -1;

	/* request id: android devices expect a hex-encoded counter block */
	if (dev->is_android) {
		char hex[33];
		uint8_t raw[16];
		int i;

		if (rand_bytes(raw, 4) < 0)
			goto done;
		memset(raw + 4, 0, sizeof(raw) - 4);
		raw[8] = 1;   /* session number (first request), little endian */
		for (i = 0; i < 16; i++)
			snprintf(hex + 2 * i, 3, "%02X", raw[i]);
		if (dbuf_append(&rid, hex, sizeof(hex) - 1) < 0)
			goto done;
	} else {
		uint8_t rnd[16];

		if (rand_bytes(rnd, sizeof(rnd)) < 0 || dbuf_append(&rid, rnd, sizeof(rnd)) < 0)
			goto done;
	}

	/* nonce in [1, 2^31 - 1] */
	{
		uint8_t nb[4];

		if (rand_bytes(nb, sizeof(nb)) < 0)
			goto done;
		nonce = (((uint64_t)nb[0] << 24) | ((uint64_t)nb[1] << 16) |
		         ((uint64_t)nb[2] << 8) | (uint64_t)nb[3]) & 0x7fffffffULL;
		if (nonce == 0)
			nonce = 1;
	}

	if (pb_put_bytes(&wvpsd, 1, init_data, init_len) < 0 ||    /* pssh_data */
	    pb_put_vfield(&wvpsd, 2, 1) < 0 ||                     /* license_type STREAMING */
	    pb_put_bytes(&wvpsd, 3, rid.data, rid.len) < 0 ||       /* request_id */
	    pb_put_bytes(&cid, 1, wvpsd.data, wvpsd.len) < 0 ||     /* widevine_pssh_data */
	    pb_put_bytes(lr, 1, dev->client_id, dev->client_id_len) < 0 ||
	    pb_put_bytes(lr, 2, cid.data, cid.len) < 0 ||
	    pb_put_vfield(lr, 3, 1) < 0 ||                          /* type NEW */
	    pb_put_vfield(lr, 4, (uint64_t)time(NULL)) < 0 ||       /* request_time */
	    pb_put_vfield(lr, 6, 21) < 0 ||                         /* protocol VERSION_2_1 */
	    pb_put_vfield(lr, 7, nonce) < 0)                        /* key_control_nonce */
		goto done;

	rc = 0;

done:
	free(rid.data);
	free(wvpsd.data);
	free(cid.data);
	if (rc != 0 && lr->data != NULL) {
		free(lr->data);
		memset(lr, 0, sizeof(*lr));
	}
	return rc;
}

static int build_challenge(WvDevice_t *dev, const DBuf_t *lr, DBuf_t *out)
{
	uint8_t digest[EVP_MAX_MD_SIZE];
	unsigned int dlen = 0;
	DBuf_t sig = { NULL, 0, 0 };
	int rc = -1;

	if (EVP_Digest(lr->data, lr->len, digest, &dlen, EVP_sha1(), NULL) != 1 || dlen != 20)
		return -1;
	if (rsa_pss_sign_sha1(dev->pkey, digest, dlen, &sig) < 0)
		goto done;

	if (pb_put_vfield(out, 1, 1 /* LICENSE_REQUEST */) < 0 ||
	    pb_put_bytes(out, 2, lr->data, lr->len) < 0 ||
	    pb_put_bytes(out, 3, sig.data, sig.len) < 0)
		goto done;

	rc = 0;
done:
	free(sig.data);
	return rc;
}

/* ***************************** */
/* Public API                    */
/* ***************************** */

int32_t container_drm_resolve(const char *wvd_path, const char *pssh_b64,
                              const char *license_url,
                              const char *const *headers, size_t n_headers,
                              drm_wv_key_t **keys_out, size_t *n_keys)
{
	WvDevice_t dev = { NULL, 0, NULL, 0 };
	uint8_t *box = NULL;
	size_t box_len = 0;
	const uint8_t *init_data = NULL;
	size_t init_len = 0;
	DBuf_t lr = { NULL, 0, 0 };
	DBuf_t challenge = { NULL, 0, 0 };
	RespBuf_t resp = { NULL, 0, 0, 0 };
	long http_code = 0;
	drm_wv_key_t *keys = NULL;
	size_t nkeys = 0;
	int32_t result = -1;

	if (wvd_path == NULL || pssh_b64 == NULL || license_url == NULL ||
	    keys_out == NULL || n_keys == NULL)
		return -1;
	*keys_out = NULL;
	*n_keys = 0;

	/* hard gate: only usable when a valid device file is present */
	if (load_wv_device(wvd_path, &dev) < 0)
		goto cleanup;

	box = b64_decode(pssh_b64, strlen(pssh_b64), &box_len);
	if (box == NULL || pssh_init_data(box, box_len, &init_data, &init_len) < 0) {
		ffmpeg_printf(2, "container drm: no valid widevine pssh box given\n");
		goto cleanup;
	}

	if (build_license_request(&dev, init_data, init_len, &lr) < 0 ||
	    build_challenge(&dev, &lr, &challenge) < 0) {
		ffmpeg_printf(2, "container drm: failed to build the license request\n");
		goto cleanup;
	}

	/* debug hook: dump the exact bytes we are about to POST */
	{
		const char *dump = getenv("DRM_CHALLENGE_DUMP");

		if (dump != NULL && dump[0] != '\0') {
			FILE *f = fopen(dump, "wb");

			if (f == NULL) {
				ffmpeg_printf(2, "container drm: cannot write %s\n", dump);
			} else {
				fwrite(challenge.data, 1, challenge.len, f);
				fclose(f);
			}
		}
	}

	if (http_post_binary(license_url, challenge.data, challenge.len, (long)DRM_LICENSE_TIMEOUT_MS,
	                     DRM_RESPONSE_MAX_BYTES, headers, n_headers, &resp, &http_code) < 0) {
		ffmpeg_printf(2, "container drm: license server request failed\n");
		goto cleanup;
	}
	if (resp.truncated)
		ffmpeg_printf(2, "container drm: license response truncated at %zu bytes\n", resp.cap_max);
	ffmpeg_printf(2, "container drm: %s -> HTTP %ld (%zu bytes)\n", license_url, http_code, resp.len);

	if ((http_code < 200 || http_code >= 300) && resp.data != NULL) {
		size_t n = resp.len > 512 ? 512 : resp.len;
		char *peek = malloc(n + 1);

		if (peek != NULL) {
			memcpy(peek, resp.data, n);
			peek[n] = '\0';
			ffmpeg_printf(2, "container drm: license server error body (%zu bytes): %s\n", resp.len, peek);
			free(peek);
		}
	}

	if (license_body_to_keys(resp.data, resp.len, &dev, lr.data, lr.len, &keys, &nkeys) < 0)
		goto cleanup;

	*keys_out = keys;
	*n_keys = nkeys;
	keys = NULL; /* ownership moved to the caller */
	if (nkeys == 0) {
		ffmpeg_printf(2, "container drm: license accepted but no content key found\n");
		result = 0;
	} else {
		result = (int32_t)nkeys;
	}

cleanup:
	free(keys);
	free(box);
	free(lr.data);
	free(challenge.data);
	free(resp.data);
	wv_device_free(&dev);
	return result;
}

void container_drm_free(drm_wv_key_t *keys)
{
	free(keys);
}
