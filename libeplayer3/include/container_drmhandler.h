#ifndef CONTAINER_DRMHANDLER_H_
#define CONTAINER_DRMHANDLER_H_

#include <stddef.h>
#include <stdint.h>

/*
 * CENC/ClearKey key resolution support (PSSH based) for widevine.
 *
 * When the input is an HLS playlist (.m3u/.m3u8) or a DASH manifest
 * (.mpd), libeplayer3 reads it, extracts the PSSH data - key ids and the
 * full PSSH box(es) - and resolves clear keys natively: for each widevine
 * PSSH box a signed license request is built from the device certificate
 * (a .wvd file), posted to the configured license server, and the returned
 * SignedMessage is verified (key derivation via AES-CMAC, signature check
 * with HMAC-SHA256) before its KeyContainer entries are decrypted. No key
 * resolving server of any kind is involved - the only network peer is the
 * license url itself.
 *
 * The resolution parameters come from PlaybackHandler_t.drmhandlerParameters (or
 * the environment variable LIBEPLAYER3_DRMHANDLER_PARAMETERS), a single JSON
 * string:
 *
 *   { "wv_device": "<path to the .wvd device file>",
 *     "license_url": "<widevine license server url>",
 *     "license_headers": [ {"User-Agent":"<agent>"}, ... ] }
 *
 * wv_device and license_url are required, license_headers is optional.
 */

/*
 * Read source_uri (.m3u/.m3u8 playlist or .mpd manifest) for PSSH data and
 * resolve the widevine keys against the license server named by
 * drmhandler_parameters. Any other kind of input yields 0 without contacting the
 * network.
 *
 * @keys_out      receives "KID:KEY[,KID2:KEY2...]" (lowercase hex), ready
 *                for set_decryption_keys()
 *
 * Returns the number of usable keys on success, 0 if no widevine PSSH data
 * was found in the input or the license yielded none, < 0 on error
 * (unusable parameters, device file unreadable, license server failure).
 */
int32_t container_drmhandler_resolve(const char *source_uri, const char *drmhandler_parameters,
                                    char *keys_out, size_t keys_out_size);

#endif
