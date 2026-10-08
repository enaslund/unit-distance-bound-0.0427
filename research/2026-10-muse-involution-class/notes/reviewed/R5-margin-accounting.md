# R5: margin accounting correction (decimal fix + both-endpoint framework)

Status: ready for checking. Corrects `R5-real-place-screen.md` §2 and `R5-real-place-mixture.md`
§4. Numbers: exact rational arithmetic on the reproduced enclosures at δ = 0.043172
(`repro_margin.py` direct run at C = 0.04226506 gives M*(θ*) = −1.9562596e-6 independently;
log `.muse-scratch/r5_margin_172_mid.log`).

## 1. Decimal fix

0.0422764 − 0.04226506 = 1.134e-5, not 1.134e-6 as used in the mixture note. Corrected
middle-baseline M*(θ*) = −1.9562596e-6 (was: −1.21623e-5), confirmed by the independent
direct run. The certified (−1.3296260e-5) and estimated (−6.962596e-7) θ*-values are
unaffected. Corrected J_R-only requirement at θ*: middle ΔJ_R ≥ 0.128205 (was: 0.7971).

## 2. Both-endpoint framework (replay sufficient vs transfer necessary)

The transfer theorem needs M > 0 over the signature range [θ*, 1/2); for affine M this is
exactly M(θ*) ≥ 0 AND M(1/2) ≥ 0. The replay's slope > 0 test is sufficient (forces the
minimum to θ*) but not necessary: with slope' < 0 the minimum sits at 1/2, where the J_R
weight (1−2θ) vanishes and M(1/2) is J_R-independent. The earlier notes wrongly presented
slope' ≥ 0 (ΔJ_R ≤ 0.3124) as a general cap. Corrected table (M(1/2) = M(θ*) + slope·2^−17):

| C input | M(θ*) | M(1/2) | J_R-only verdict |
|---|---|---|---|
| 0.0422764 (certified, witnessed) | −1.3296260e-5 | −8.5298244e-6 | EXCLUDED: M(1/2) < 0 fixed, J_R-free |
| 0.04226506 (certified, unwitnessed) | −1.9562596e-6 | +2.8101756e-6 | needs ΔJ_R ≥ 0.1282, no cap |
| ~0.0422638 (LP estimate) | −6.962596e-7 | +4.0701756e-6 | needs ΔJ_R ≥ 0.0456, no cap |

Certified exclusion, repaired: M(1/2) < 0 regardless of J_R, so either branch fails
(slope' ≥ 0 needs ΔJ_R ≥ 0.8713 above the 0.3124 branch boundary; slope' < 0 fails near
1/2). The middle-baseline "exclusion" is withdrawn: it needs ΔJ_R ≥ 0.1282 with no upper
bound (large ΔJ_R is fine since M(1/2) > 0 there). The "max usable J_R-only improvement
≈ 4.77e-6" claim is withdrawn (same conflation).

## 3. Consequences

- Screen results unchanged: families yield ΔJ_R ≤ 3.4e-6, first-variation mechanism stands;
  all three baselines remain out of J_R-only reach (needs 0.8713 / 0.1282 / 0.0456).
- Zeros: middle θ_0 = 0.4999955019, estimated θ_0 ≈ 0.4999935 — both baselines already give
  positive margin above θ_0; the deficit is only at low θ (many real places).
- No certification activity (no slack); C52/C54 own the checks.

## C62 review (2026-10-06)

Reviewer: C62 lane. Reran `repro_margin.py` at delta = 0.043172 for all
three C inputs (0.0422764 / 0.04226506 / 0.0422638) with a fresh venv
(mpmath 1.3.0, python-flint 0.9.0, numpy 2.5.3, scipy 1.18.1); exact
rational C-difference plus needs/M(1/2)/cap/zero arithmetic in
`research/2026-10-muse-involution-class/code/C62/c62_margin_check.py` (all pass). Read
`geo:general-margin` and `geo:transfer` (geometry.tex), `tw:field-family`
(tower.tex), `cert:lower-margin` (certificate.tex), README §11c
(verified C-input provenance lines 1229-1231), and the corpus records
`C52-r5-baseline-check.md`, `C52-r5-jr-exclusion.md`,
`C54-r5-margin-table-correction.md`.

Extracted to corpus (source at
`research/2026-10-muse-involution-class/notes/reviewed/R5-margin-accounting.md`):

- `research/2026-10-muse-involution-class/corpus/C62-r5-margin-accounting-check.md`: the full
  note verified (computed + proved). Decimal fix 1.134e-5 exact;
  M*(θ*) enclosures −1.32962596e-5 / −1.95625960e-6 / −6.9625960e-7
  reproduced; needs 0.8714 / 0.1282 / 0.0456; M(1/2) −8.53e-6 /
  +2.81e-6 / +4.07e-6; slope 0.6247462, cap 0.31237; certified
  J_R-only exclusion via the repaired branch argument; withdrawal of
  the middle-baseline exclusion and of the 4.77e-6 general cap (kept
  as slope-preserving value 4.7664e-6); zeros 0.50001365 /
  0.4999955019 / 0.4999934851 and the §3 consequences. Agrees with
  `C54-r5-margin-table-correction.md` to all quoted digits.

Rejected or unresolved:

- Nothing in this note is rejected. The note's own withdrawals (mixture
  middle row −1.21623e-5 / 0.7970, middle exclusion, slope cap as
  necessity) are confirmed correct.
- Two precision notes, no verdict impact (margins sit ~1e-6 from zero):
  the both-endpoint test is the uniform-over-signatures certificate at
  this witness (`geo:transfer` strictly needs inf_i M(θ_i) > 0 on the
  chosen tower sequence; a non-uniform escape would need new tower
  control, not just a profile); and M > 0 with uniform inf > 0 on
  [θ*, 1/2) is exactly M(θ*) > 0 and M(1/2) > 0, where the note writes
  ≥ 0 at both points.
- The cited log `.muse-scratch/r5_margin_172_mid.log` is uncommitted
  (git-ignored scratch) and was not inspected; the number it supports
  was reproduced by two independent direct runs (C54's and this one).

No previously accepted corpus result was overturned. A flaw in any
withdrawn argument does not rule out the real-place direction; the
repaired exclusion covers J_R-only repair of the witnessed certified
gap at this delta/witness only.
