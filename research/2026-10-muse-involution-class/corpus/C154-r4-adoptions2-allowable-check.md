# C154 check: R4-adoptions2 Sec 4 concentration-adjusted allowable C (computed; comparison conditional on unreviewed C_eff_upper)

Source note (reviewed): `research/2026-10-muse-involution-class/notes/reviewed/R4-adoptions2.md`
(checked at md5 `d11f9a4101ddf6218c74e4ede441c7b5`, commit `2c54ba51`;
HEAD at check `13a18bf841e596b7be7a655e4f3d7de7d1b8762f`).
Check code: `research/2026-10-muse-involution-class/code/C154/c154_allowable_check.py` (exit 0;
output in run log, reproduced below).
Inputs: C62 enclosures from
`research/2026-10-muse-involution-class/corpus/C62-r5-margin-accounting-check.md` Secs 1-2
(witnessed `M*(theta*)`, `M(1/2)`, slope; `C_wit = 0.0422764` exact);
concentration cost `4e-9` from `papers/0.04273/certificates/geom241.py`
line 88 (`after = Mstar - 4*qi(1/10^9)`); theta-independence from
`papers/0.04273/sections/geometry.tex` proof of `geo:transfer`
(`E/n^{1+delta} >= 2^{-2-delta} e^{d(M(theta)-4eta)}`, cost `4eta`
independent of theta); quoted `C_eff_upper = 0.04226505507230665`
from `research/2026-10-muse-involution-class/notes/ready/R4-signed-kernel.md` Sec 3
(md5 `37576348367fc648aa08aa2c0a597459`, still in `ready/`, NOT
verified here).

## 1. Allowable C from C62 lowers minus concentration (computed, verified)

Margin affine: `M(th) = K(th) - C`, `K` from witnessed run.
`theta* = 1/2 - 2^-17`, `th_new = 1/2 - 2^-18`,
`M(th_new) = M(theta*) + slope*2^-18`, `M(1/2)` directly.
`C_allow(th) = K(th)` (max `C` with `M >= 0`); after concentration
`C_allow_after(th) = C_allow(th) - 4e-9` since
`M_after(th) = M(th) - 4e-9` uniformly in theta.

Exact-rational intervals from C62 lower/upper endpoints:

- `C_allow(1/2)` pre-concentration in
  `[0.04226787017559790, 0.04226787017559794]` (width `4e-17`).
  Post-concentration in
  `[0.04226786617559790, 0.04226786617559794]`.
  Note claims `0.0422678661755979`: EXACT match to lower endpoint.
- `C_allow(1/2-2^-18)` pre-concentration in
  `[0.04226548695800095858, 0.04226548695800099479]` (width `~3.6e-20`).
  Post-concentration in
  `[0.04226548295800095858, 0.04226548295800099479]`.
  Note claims `0.0422654829580010`: `4.14e-17` above the rigorous
  lower endpoint (rounding at the 16th decimal place; immaterial
  vs slack `4.28e-7` by 10 orders, but strictly the citable lower
  is the interval low end, not the rounded quote).

Slope enclosure `[0.62474619373310090, 0.62474619373310098] > 0`
justifies using `slope_lo` for the lower bound at `th_new`.

## 2. Comparison to quoted C_eff_upper (conditional, arithmetic verified)

Quoted `C_eff_upper = 0.04226505507230665` (R4-signed-kernel Sec 3)
matches that note to all digits (quote fidelity verified; correctness
NOT verified here -- that note is still in `ready/`).

Slacks `C_allow_after - C_eff_upper` (lower/upper from Sec 1):

- At `th_new`: `[4.27885694309e-7, 4.27885694345e-7]`.
  Note claims `4.278857e-7`: correct rounding of both ends.
- At `1/2`: `[2.81110329125e-6, 2.81110329129e-6]`.
  Note claims `2.811103e-6`: correct rounding.

Hence IF the quoted `C_eff_upper` is a valid upper bound on the true
effective `C` (pending signed-kernel review) AND the C62 enclosures
stand, THEN the recovered `C` is below both concentration-adjusted
allowables with strictly positive slacks `~4.28e-7` (binding, at
`th_new`) and `~2.81e-6` (at `1/2`). Equivalently
`M_after(th_new) >= +4.278857e-7 > 0`,
`M_after(1/2) >= +2.811103e-6 > 0` (lower bounds).

"Conditional close intact" is preserved ONLY as conditional: it still
requires (i) `N_iota >= 2^16` (signature reviews, per R4-signed-kernel
Sec 2 / C86 conditional), (ii) correctness of `C_eff_upper` (pending),
(iii) Gaussian admissibility/Fourier inputs behind the C62 baselines
(review limit, inherited). No exponent gain is established here.

## 3. What was checked (inputs and versions)

- Read the note at `research/2026-10-muse-involution-class/notes/ready/R4-adoptions2.md`
  (pre-review location), C62 corpus Secs 1-2, `geom241.py` lines 86-91
  and 140-141 (`after` definition and print), `geometry.tex`
  `geo:transfer` proof lines 779-785 (`M(theta)-4eta`), C86 Sec 1
  (`theta*(2^16) = 1/2-2^-18`, conditional close), and
  R4-signed-kernel Secs 2-3 (pre-concentration allowables
  `0.0422678701755979` / `0.0422654869580010` and `C_eff_upper`).
- Ran `research/2026-10-muse-involution-class/code/C154/c154_allowable_check.py` (stdlib-only
  exact `Fraction` on C62 decimal endpoints + `Decimal` display):
  intervals, `4.14e-17` rounding excess at `th_new`, slacks, and
  Sec 5 gradient-norm spot check `2.491e-7` (claimed `~2.5e-7`).
  Exit 0.
- Verified concentration-cost source and theta-independence as above;
  verified pre-concentration allowables minus `4e-9` equal the claimed
  post-concentration values to quoted digits (up to the `4.14e-17`
  rounding noted).
- NOT checked: correctness of `C_eff_upper` itself (signed-kernel
  `choose`/`certify` run, kernel cells, census/L inputs by hash);
  near-1 L-validation inheritance; signature `N_iota >= 2^16`
  existence; any profile/Fourier inputs behind C62.

## 4. Status

Substantiated: concentration-adjusted allowable intervals above
(computed from C62 lowers minus paper-standard `4e-9`); slack
arithmetic vs the quoted `C_eff_upper` (computed, conditional on that
quote being a valid upper). No previously accepted corpus result
overturned. Secs 1-3 and 5 of the note are faithful adoptions/
restatements of already-corpus results (C114/C115/C125/C132; see the
review appendix in the note) and are not re-extracted here.
