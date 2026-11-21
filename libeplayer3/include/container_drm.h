#ifndef CONTAINER_DRM_H_
#define CONTAINER_DRM_H_

#include <stddef.h>
#include <stdint.h>

/*
 * Widevine CENC key acquisition without an external key-resolving server.
 *
 * The module implements the license round-trip directly: it loads a Widevine
 * device file (.wvd), builds and RSA-signs a license request for a PSSH box,
 * exchanges it with the configured license server and extracts the content
 * keys from the signed license response (including its integrity check).
 *
 * container_drm_resolve() performs one complete round-trip:
 *
 *   @wvd_path      path to the device file; the function is only usable when
 *                  this file exists and holds a valid device
 *   @pssh_b64      base64 of a full Widevine PSSH box (as found in m3u/mpd)
 *   @license_url   license server url, challenge posted there as-is
 *   @headers       optional array of "Name: value" lines sent with the
 *                  request, or NULL
 *   @n_headers     number of header lines
 *   @keys_out      receives an array of resolved keys (caller frees it with
 *                  container_drm_free())
 *   @n_keys        receives the number of usable content keys
 *
 * Returns > 0 when at least one key was extracted, 0 when the round-trip
 * succeeded but no content key could be found, < 0 on error (missing or
 * invalid device file, bad PSSH, license server failure, signature check).
 */

typedef struct
{
	uint8_t kid[16];
	uint8_t key[16];
} drm_wv_key_t;

int32_t container_drm_resolve(const char *wvd_path, const char *pssh_b64,
                              const char *license_url,
                              const char *const *headers, size_t n_headers,
                              drm_wv_key_t **keys_out, size_t *n_keys);
void container_drm_free(drm_wv_key_t *keys);

#endif
