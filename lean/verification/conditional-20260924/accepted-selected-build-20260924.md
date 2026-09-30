# Accepted selected Lean 4.35 source build

On 2026-09-24, selected build pass 50 completed successfully: 6,832 Lake jobs
with Lean `v4.35.0-rc2` and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Its selected source
inventory contains 2,163 Lean modules. The source digest under the
`sha256(sorted UTF-8 lines: POSIX relative path<TAB>lowercase source sha256<LF>)`
scheme is `b9df7ce22302591dd30d3b4f255194e14eb67afa177b8a6c47e8cdcce3e7f05b`.
The complete build log SHA-256 is
`4949f2baa1afe7fcc7eb61fb6a3d2a0ac0b6c2239342a975110b2d428a98fe25`.

The source-only accepted stage is
`.cache/build-tmp/conditional18-v435-source-candidate-accepted-20260924/`.
Its `SOURCE_SYNC.json` SHA-256 is
`46bedcf205109bff4ebaa2c756e72b5c1a7e40aa57bc7b2ca8da70c3c843263a`;
its `SELECTED_BUILD_RECEIPT.json` SHA-256 is
`fd2141d0c3e5503435baba3c8e8d10a1e354bb9fb0da0455018eb89aed33e150`.
The receipt checks the full log success marker and equality of every selected
source hash before and after the build and in the accepted stage.

The accepted-stage promotion preflight found 235 changed selected source files:
57 native and 178 vendored. Its final source diff manifest is
[`candidate18-selected-source-diffs-accepted50_134514.json`](../conditional-20260923/candidate18-selected-source-diffs-accepted50_134514.json),
SHA-256 `6269bc0cc232027431b4b69e2896a23cd8a5e337a459e99e9c5d7e2dabda6a6c`;
the paired patch SHA-256 is
`67d35a9474904552039d936d1168ab2d197205dd1f7ccf93fed9616cb8b31eb1`.
The [native preflight](native-preflight-accepted50_134514.json) and
[vendor preflight](vendor-preflight-accepted50_134514.json) passed on this
accepted source and build receipt. The [native apply](native-apply-accepted50_134514.json)
and [vendor apply](vendor-apply-accepted50_134514.json) used reversible
journals; the [Yamaguchi](yamaguchi-reverse-accepted50_134514.json),
[AINTLIB](aintlib-reverse-accepted50_134514.json), and
[Hadamard](hadamard-reverse-accepted50_134514.json) reverse provenance
checks passed afterward.

This is a selected source build and provenance result. Archive creation,
current Palomar preparation, full current verifier execution, official
submission, and the arithmetic premise H have separate statuses and are not
certified by this receipt. The public PalomarSubmission and PalomarPolicy
main heads were rechecked at approximately 13:44 UTC as
`1703d7babd984ccc3831cdf89c28221abe34808f` and
`792c7c0b9e798bd02719e795ef11fa2b5929e067`, respectively.
