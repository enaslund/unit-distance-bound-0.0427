# C62 check: R5 margin accounting correction (verified)

Source note (reviewed): `research/2026-10-muse-involution-class/notes/reviewed/R5-margin-accounting.md`
(all three sections). Cross-reference:
`research/2026-10-muse-involution-class/corpus/C54-r5-margin-table-correction.md` states the same
correction; this file is an independent second verification from fresh
direct runs plus exact arithmetic.
Check code: `research/2026-10-muse-involution-class/code/C62/c62_margin_check.py` (stdlib-only
arithmetic on the enclosures below; run: `python3
research/2026-10-muse-involution-class/code/C62/c62_margin_check.py`).
Direct runs: `research/2026-10-muse-involution-class/code/R5/repro_margin.py` at delta = 0.043172
with C in {0.0422764, 0.04226506, 0.0422638} (venv with
mpmath 1.3.0, python-flint 0.9.0, numpy 2.5.3, scipy 1.18.1;
e.g. `/tmp/C62-venv/bin/python research/2026-10-muse-involution-class/code/R5/repro_margin.py
0.043172 0.04226506`).
Target: M*(theta) >= 0 on [theta*, 1/2), theta* = 65535/131072,
1 - 2 theta* = 2^-16, 1/2 - theta* = 2^-17.
C inputs from `papers/0.043171/README.md` Section 11c (lines 1229-1231
verified in tree: 0.04226506 via `signed3.py W4 certify` with census to
8.5e14 / 36 abscissae; ~0.0422638 LP estimate with census to 2^50 /
71 abscissae).

## 1. Decimal fix (verified)

0.0422764 - 0.04226506 = 567/50000000 = 1.134e-5 exactly (not
1.134e-6). Margin is affine in C with slope exactly -1 (M* contains -C;
all other terms C-independent; confirmed: the three runs differ only in
the -C term and M*/M*(0)/zero).

Direct enclosures at delta = 0.043172 (C62 reruns):

| C input | M*(theta*) direct enclosure |
|---|---|
| 0.0422764 (certified, witnessed) | [-1.32962595959847075e-05, -1.32962595959484946e-05] |
| 0.04226506 (certified, unwitnessed) | [-1.9562595959847075e-06, -1.9562595959484946e-06] |
| 0.0422638 (LP estimate) | [-6.962595959847075e-07, -6.962595959484946e-07] |

So the mixture note's middle row M* = -1.21623e-5 is REFUTED (it equals
witnessed M* + 1.134e-6, the 10x error, reproduced to all digits);
correct value -1.9562596e-6, matching the accounting note and C54.
Certified (-1.3296260e-5) and estimated (-6.962596e-7) values confirmed
unaffected. Slope enclosure [0.62474619373310090, 0.62474619373310098]
confirmed (note: 0.6247462).

J_R-only needs at theta* (need = -M*_lo / 2^-16): 0.871384 / 0.128205 /
0.045630. The note's 0.8713 / 0.128205 / 0.0456 are confirmed (correct
roundings). The old 0.7971 is withdrawn with the decimal error.

## 2. Both-endpoint framework (verified)

Margin formula `geo:general-margin` (papers/0.04273/sections/geometry.tex
line 709): M(theta) = ... + (1-2 theta) J_R + theta J_C, affine in
theta with slope -log pi - 2 J_R + J_C^*. Hence at fixed pair profile,
shells and analytic input a J_R-only change moves M(theta) by
(1-2 theta) dJ_R and the slope by -2 dJ_R (verified against the
formula; only the (1-2 theta) J_R term moves). At theta = 1/2 the J_R
weight vanishes, so M(1/2) = M(theta*) + slope * 2^-17 is J_R-free.

M(1/2) enclosures (interval arithmetic on the above):

| C input | M(1/2) |
|---|---|
| 0.0422764 | [-8.52982440210e-06, -8.52982440206e-06] |
| 0.04226506 | [+2.81017559790e-06, +2.81017559794e-06] |
| 0.0422638 | [+4.07017559790e-06, +4.07017559794e-06] |

The note's table (-8.5298244e-6 / +2.8101756e-6 / +4.0701756e-6)
matches to all quoted digits.

Repaired branch argument (checked step by step):

- Certified witnessed: M(1/2) < 0 fixed. If slope' >= 0
  (dJ_R <= slope/2 <= 0.3123731; note's 0.3124 confirmed as a rounding),
  M' is non-decreasing so M'(theta*) >= 0 needs dJ_R >= 0.87138, above
  the branch boundary: impossible. If slope' < 0, M' is decreasing so it
  is negative near 1/2. EXCLUDED for J_R-only repair. The parent note's
  proof as written (slope' >= 0 presented as necessary) was invalid;
  the conclusion survives via this argument (agrees with
  `C52-r5-jr-exclusion.md` Sections 2-3).
- Middle certified: M(1/2) > 0 already. Needs dJ_R >= 0.128205 with NO
  upper cap: large dJ_R makes slope' < 0 but both endpoints positive,
  so the whole interval is positive. The mixture note's "exclusion
  extends to the middle baseline" is withdrawn (decimal + logic errors).
- Estimated: M(1/2) > 0 already. Needs dJ_R >= 0.045630 with no cap.
- "Max usable J_R-only improvement ~= 4.77e-6 (= 2^-16 * 0.31238)"
  WITHDRAWN as a general cap: 4.7664e-6 confirmed as the value of the
  *slope-preserving* cap only. It conflated the replay's sufficient
  slope > 0 test (which forces the minimum to theta*; see
  `cert:lower-margin` and `geom241.py` slope_ok assertion) with
  necessity.

Precision notes (no verdict impact; margins are ~1e-6 from zero):

- Scope is uniform-over-signatures at this witness: `geo:transfer`
  needs inf_i M(theta_i) > 0 for the chosen tower sequence, and the
  both-endpoint test is the uniform certificate over all allowed
  signatures (theta* <= theta < 1/2 per `tw:field-family`), which is
  what the replay targets. A non-uniform escape would need new tower
  control on N_iota, not just a profile change.
- Strictness: M > 0 on the half-open [theta*, 1/2) with uniform inf > 0
  is exactly M(theta*) > 0 AND M(1/2) > 0; the note writes >= 0 at both
  points, which is loose at the boundary but immaterial here.

## 3. Consequences (verified)

- Screen reach: polynomial best dJ_R = +3.36e-6 (per
  `C52-r5-family-screen.md`), mixture 0 (per
  `C54-r5-mixture-screen-check.md`), first-variation ascent +1.35e-6
  (per `C57-r5-first-variation-check.md` Section 5, superseding the
  +1.7e-6 quoted before that check). All are far below every need
  (0.045630 / 0.128205 / 0.871384), so all three baselines remain out
  of J_R-only reach on current evidence. Confirmed.
- Zeros (direct enclosures): middle theta_0 in
  [0.49999550189240666, 0.49999550189240672] (note: 0.4999955019);
  estimated theta_0 in [0.49999348507339658, 0.49999348507339664]
  (note: ~0.4999935); witnessed theta_0 = 0.50001365326... > 1/2 (both
  endpoints negative). Both sub-1/2 zeros lie above theta* =
  0.4999923706, and with slope > 0 the margin is positive above each
  zero, so the deficit is only at low theta, i.e. high real-place
  fraction b/d = 1 - 2 theta. Confirmed.

## 4. Status

Substantiated in full (computed + proved): decimal fix 1.134e-5;
middle M* = -1.9562596e-6; needs 0.8714 / 0.1282 / 0.0456; M(1/2)
signs (-8.53e-6 / +2.81e-6 / +4.07e-6); slope 0.6247462 and cap
0.31237; certified J_R-only exclusion via the repaired branch
argument; withdrawal of the middle exclusion and of the 4.77e-6
general cap; zeros and consequences above. Refuted (agreeing with
C54): mixture middle row (-1.21623e-5 / 0.7970 / cap-no) and its
"exclusion extends" claim; slope cap as necessity. No previously
accepted corpus result is overturned: `C54-r5-margin-table-correction.md`
already records the same correction (this check agrees to all quoted
digits), and `C52-r5-jr-exclusion.md` already carries the repaired
exclusion with "maximum slope-preserving" scoping.
