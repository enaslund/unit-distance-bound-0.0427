# Stream A1: numerical margin of the ℚ(√241) witness

State on 2026-09-29: **done**. `UnitDistance.Sqrt241.Witness.uniform_margin` is
proved with κ = 1189/10⁷ = 0.0001189 and depends only on `propext`,
`Classical.choice`, `Quot.sound` (checked with `#print axioms` from a scratch
file outside the repository). No `sorry`, `axiom`, `native_decide` or
`implemented_by`; the finite arithmetic uses `decide +kernel`.

## Decision: the manuscript's `s` (option b)

`Witness.s` is now the manuscript value `22920117/20000000` (it was
`114697/100000 = (11/10)(1+δ)`). `pair_exponent_gap` now reads
`s * p - 1 = 12493117 / 10427000` (it was `= 6/5`). All other declarations of
`Witness.lean` are unchanged; `finiteProfit_lower` was rebuilt and still holds
(it does not involve `s`). `certificates/finite-witness-241.json` records the new
`pair_profile_s` (the finite generator does not read it).

Why. With the manuscript's `s`, `a` and Bernstein matrix, `pairProfile` and
`pairOverlap` are literally the ℚ development's (`pairProfile_eq_manuscript`,
`pairOverlap_eq_manuscript`), so the verified overlap bound
`UnitDistance.Witness.pairOverlap_coarse_lower` (≈28 modules, no generator)
applies unchanged, as do integrability and positivity of the profile. The mass
must be recomputed in either option, because `p = 2/(1+δ)` changed; the new mass
certificate below works for any rational `q`, so keeping `q = 6/5` bought
nothing. The cost of (b) is 1.6·10⁻⁶ of true margin (0.00011917 instead of
0.00012079 at ceiling 0.0495). The same identities make every `s`-dependent
fact of the ℚ development about `UnitDistance.Witness.pairProfile` (Student
envelope, Fourier tube, moments) available to the geometric stream by rewriting
with `pairProfile_eq_manuscript`; facts that also involve `p` must be redone.

## Delivered statements (namespace `UnitDistance.Sqrt241.Witness`)

Main result (`Numerics/Margin.lean`):

```lean
theorem uniform_margin (θ : ℝ) (hθ : thetaMin ≤ θ) :
    (1189 / 10 ^ 7 : ℝ) < margin θ - 4 * epsilon
theorem uniform_threshold (θ : ℝ) (hθ : thetaMin ≤ θ) :
    (496189 / 10 ^ 7 : ℝ) - ceiling < margin θ - 4 * epsilon   -- `ceiling` not unfolded
theorem margin_at_min : (1189 / 10 ^ 7 : ℝ) < margin thetaMin - 4 * epsilon
theorem margin_at_min_threshold :
    (496189 / 10 ^ 7 : ℝ) - ceiling < margin thetaMin - 4 * epsilon
theorem margin_mono : Monotone margin
theorem signature_slope_pos : 0 < -Real.log Real.pi - 2 * JCompact + JPair
theorem signature_slope_lower : (63 / 100 : ℝ) < -Real.log Real.pi - 2 * JCompact + JPair
theorem JCompact_bounds :
    (-2106409928080139 / 10 ^ 16 : ℝ) ≤ JCompact ∧ JCompact ≤ (-2106409928080137 / 10 ^ 16 : ℝ)
```

`uniform_threshold` is the form to use if `ceiling` (now fixed at 0.0495) is ever changed:
any ceiling below 0.0496189 keeps a positive margin, without re-proving anything.

Pair functional (`Numerics/PairFunctional.lean`, `PairTransfer.lean`,
`PairMassNormalization.lean`):

```lean
theorem JPair_lower : (13564458712 / 10 ^ 10 : ℝ) ≤ JPair
theorem JPair_eq_normalized :
    JPair = Real.log normalizedPairOverlap + 2 * (1 + increment) * Real.log (s * p - 1)
      - 2 * increment * Real.log Real.pi + 2 * increment * Real.log a
      - (1 + increment) * Real.log normalizedPairMass
theorem normalizedPairOverlap_lower : pairOverlapNormalizedLower ≤ normalizedPairOverlap
    -- pairOverlapNormalizedLower = 3484186885 / 10^7
theorem pairOverlap_lower : pairOverlapNormalizedLower * pairArchScale ≤ pairOverlap
theorem normalizedPairMass_le_decimal : normalizedPairMass ≤ (38794821206 / 10 ^ 9 : ℝ)
theorem normalizedPairMass_eq_betaIntegral : normalizedPairMass = pairMassBetaIntegral
theorem pairMassBetaIntegral_eq_iterated : pairMassBetaIntegral =
    ∫ t in Icc 0 1, ∫ u in Icc 0 1, betaDensity pairBetaExponent t *
      betaDensity pairBetaExponent u * (polynomial t u) ^ p     -- q = 12493117/10427000
theorem s_eq_manuscript : s = UnitDistance.Witness.s          -- also a, bernsteinCoefficients,
theorem pairProfile_eq_manuscript : pairProfile = UnitDistance.Witness.pairProfile  -- polynomial
theorem pairOverlap_eq_manuscript : pairOverlap = UnitDistance.Witness.pairOverlap
theorem pairMass_pos : 0 < pairMass
theorem pairOverlap_pos : 0 < pairOverlap
theorem integrable_pairMass : Integrable (fun z : ℂ × ℂ => pairProfile z ^ p)
```

Compact functional (`Numerics/Compact.lean`):

```lean
theorem JCompact_log_eq : JCompact = -increment - increment * Real.log Real.pi
    + increment * Real.log (4 * increment) - (1 + increment) * Real.log (1 + increment)
theorem compactMass_eq : compactMass = Real.pi / (2 * increment * p)
theorem compactOverlap_eq : compactOverlap = Real.exp (-increment) * (Real.pi / (4 * increment))
```

Logarithms (`Numerics/LogConstants.lean`), ℓ = `logRD`:

```lean
theorem logRD_bounds :
    (565600472355630 / 10 ^ 14 : ℝ) ≤ logRD ∧ logRD ≤ (565600472355631 / 10 ^ 14 : ℝ)
theorem log_two_bounds : (693147180559945309 / 10 ^ 18 : ℝ) ≤ Real.log 2 ∧
    Real.log 2 ≤ (693147180559945310 / 10 ^ 18 : ℝ)
theorem log_3615_bounds : (8192847134592865061 / 10 ^ 18 : ℝ) ≤ Real.log 3615 ∧
    Real.log 3615 ≤ (8192847134592865062 / 10 ^ 18 : ℝ)
theorem log_pi_bounds : (1144729885849400174 / 10 ^ 18 : ℝ) ≤ Real.log Real.pi ∧
    Real.log Real.pi ≤ (1144729885849400175 / 10 ^ 18 : ℝ)
theorem log_four_increment_bounds, log_one_add_increment_bounds  -- log(4δ), log(1+δ)
```

Generic tools (namespace `UnitDistance.Sqrt241.Numerics`, `Numerics/RatLog.lean`),
usable by other streams for any rational logarithm or real power:

```lean
def logLo (y : ℚ) : ℚ   -- 30-term artanh series after scaling y into [1,2)
def logHi (y : ℚ) : ℚ
theorem log_bounds {y : ℚ} (hy : 0 < y) :
    ((logLo y : ℚ) : ℝ) ≤ Real.log (y : ℝ) ∧ Real.log (y : ℝ) ≤ ((logHi y : ℚ) : ℝ)
theorem log_ge_of_le_logLo {y lo : ℚ} (hy : 0 < y) (h : lo ≤ logLo y) : (lo : ℝ) ≤ Real.log y
theorem log_le_of_logHi_le {y hi : ℚ} (hy : 0 < y) (h : logHi y ≤ hi) : Real.log y ≤ hi
theorem rpow_le_of_logs {y e U : ℚ} (hy : 0 < y) (hU : 0 < U) (he : 0 ≤ e)
    (h : e * logHi y ≤ logLo U) : (y : ℝ) ^ (e : ℝ) ≤ (U : ℝ)
theorem le_rpow_of_logs {y e L : ℚ} (hy : 0 < y) (hL : 0 < L) (he : 0 ≤ e)
    (h : logHi L ≤ e * logLo y) : (L : ℝ) ≤ (y : ℝ) ^ (e : ℝ)
```

The premises `h` are closed by `decide +kernel` (about 0.05 s each); the
enclosure width is about 10⁻²⁸(1 + |log₂ y|).

## Numbers

| quantity | proved | floating point (exact functional) |
|---|---|---|
| finiteProfit | ≥ 0.721977083 | 0.7219770832 |
| ℓ | [5.65600472355630, 5.65600472355631] | 5.6560047235563 |
| JCompact | [−0.2106409928080139, −0.2106409928080137] | −0.2106409928080 |
| normalized overlap | ≥ 348.4186885 | 348.4186894704 |
| normalized mass | ≤ 38.794821206 | 38.7948058919 |
| JPair | ≥ 1.3564458712 | 1.3564462857 |
| θ-slope | > 0.63 | 0.63300 |
| margin(θmin) − 4ε, ceiling 0.0495 | > 0.0001189 | 0.00011917 |

The floating-point column is from
`papers/0.04273/certificates/geom241.py` (`margin` with
`s = 22920117/20000000`, δ = 0.0427, C = 0.0495: margin after 4ε
`0.00011917147`, J_D `1.356446285661`). The loss to κ is almost all in the
mass (relative 3.9·10⁻⁷, i.e. 2.1·10⁻⁷ of margin).

## Mass certificate

`pairMassBetaIntegral = E[P(T,U)^p]`, `T, U` i.i.d. `Beta(q,1)`,
`p = 20000/10427`, `q = 12493117/10427000`. The unit square is cut into
12 × 12 cells. On a cell, `P` is monotone in each variable (ℚ development,
`polynomial_cell_bounds`), so `|P/h − 1| ≤ ρ` with `ρ = cellRho`; then
`P^p = h^p (1+w)^p ≤ h^p (∑_{k≤3} C(p,k) w^k + |C(p,4)| ρ⁴/(1−ρ))`
(`generalizedBinomial_truncation_error`). Expanding `w^k` in powers of `P` and
`P^m` (`m ≤ 3`) in monomials (tables `c1Table`–`c3Table`, identities by `ring`),
the cell integral is the exact contraction of beta moments
`q((r^{q+m} − l^{q+m})/(q+m))`, bounded with directed enclosures of `(k/12)^q`.
`h^p ≤ HTab` and the grid enclosures are checked through the outward-rounded
logarithm enclosures `logLoR`/`logHiR` (`RatLogRounded.lean`: the argument
reduction and 30-term `artanh` series of `RatLog.lean`, with every power and every
term rounded outward to a multiple of 10⁻⁴⁰; `logR_bounds`).
All of this is the generic theorem `MassCert.pairMassBetaIntegral_le_of_checks`
(`PairMassCell.lean`); its rational premises are decided by the kernel in
`PairMassData.lean`, one lemma per grid point (`grid_check_k`) and per cell
(`cell_check_i_j`). The total is checked cell by cell: the exact contribution
`HTab i j · max(cellEbar …, 0)` of each cell is bounded by `cTab i j`, rounded up
to a multiple of 10⁻¹⁵ (`contrib_check_i_j`), and only these short rationals are
summed (`total_sum_check`; `massTotal_le_of_cells` in `PairMassRat.lean`).
Reference: the ℚ development's 8 × 8,
degree-3 chain (`PairMass*`, q = 6/5) follows the same idea but proves the
contractions through `Polynomial (Polynomial ℝ)` and encloses `(k/8)^{6/5}` by
fifth powers; here the majorant is written directly in monomials and the grid
powers are enclosed through logarithms, so the soundness proof is generic in the
grid `N` and needs no special form of `q` (only `qQ`, `pQ` and the degree 3 are
fixed in `PairMassRat.lean`).

**Kernel cost (2026-09-29).** The first version decided the grid, cell and total
premises by one `decide +kernel` each, over all points and cells at once, with the
exact series of `RatLog.lean`. Lean's kernel and NanoDa check that quickly, but
con-ron (the independent checker of the Palomar pipeline) keeps every intermediate
of a declaration in memory and normalizes large rationals slowly: the exact 144-cell
total carries denominators of tens of thousands of digits, and one exact logarithm
of a 15–25-digit argument takes 4–15 s. Its Standard-profile replay (4 CPUs, 16 GiB)
was killed at 16 GiB with those three checks outstanding. The certificate is now
split into 299 separate kernel checks with short rationals; con-ron checks the whole
certificate in about 140 s with a peak of 0.7 GiB. The certificate data (`XL`, `XU`,
`hTab`, `HTab`) and `massUpper` are unchanged; see
`verification/sqrt241-bounded-20260929/`.

## Files

```
UnitDistance/Sqrt241/Witness.lean                     s and pair_exponent_gap changed (see above)
UnitDistance/Sqrt241/Numerics/RatLog.lean             generic ℚ log/rpow enclosures
UnitDistance/Sqrt241/Numerics/RatLogRounded.lean      the same, rounded outward (short rationals)
UnitDistance/Sqrt241/Numerics/PairTransfer.lean       identities with UnitDistance.Witness, overlap bound
UnitDistance/Sqrt241/Numerics/PairMassNormalization.lean  mass = beta integral, JPair_eq_normalized
UnitDistance/Sqrt241/Numerics/PairMassTables.lean     generated: power tables of P, P², P³
UnitDistance/Sqrt241/Numerics/PairMassRat.lean        rational arithmetic of the cell certificate
UnitDistance/Sqrt241/Numerics/PairMassCell.lean       soundness of the cell certificate
UnitDistance/Sqrt241/Numerics/PairMassData.lean       generated: N = 12 data and per-point/per-cell kernel checks
UnitDistance/Sqrt241/Numerics/Compact.lean            JCompact closed form
UnitDistance/Sqrt241/Numerics/LogConstants.lean       log 2, log 3615, log π, ℓ, log 4δ, log(1+δ)
UnitDistance/Sqrt241/Numerics/PairFunctional.lean     JPair_lower
UnitDistance/Sqrt241/Numerics/Margin.lean             JCompact_bounds, slope, uniform_margin
scripts/sqrt241/generate_pair_mass_certificate.py     generator of PairMassTables/PairMassData
```

Imported from the ℚ development without change: `LogBounds` (`log_enclosure`),
`GaussianProfiles` (complex Gaussian integrals), `PairBetaMoments`,
`PairBinomialTail`, `PairMassCellCertificate` (generic beta and binomial
lemmas, `polynomial_cell_bounds`), `PairMassNormalization`
(`complex_student_coordinate_integral`), `PairOverlapCoarseLower`
(`pairOverlap_coarse_lower`), `StudentProfiles`.

## Rebuild

```
./.toolchain/bin/lake build UnitDistance.Sqrt241.Numerics.Margin
```

builds the chain (PairMassData ≈ 3 min, every other module < 15 s). To
regenerate the certificate data (Python 3 with mpmath; `PYLIB` may point to a
directory containing mpmath):

```
PYLIB=... python3 scripts/sqrt241/generate_pair_mass_certificate.py 12
```

It rewrites `PairMassTables.lean` and `PairMassData.lean` deterministically
(same output for the same `N`) and prints the certified total. `N = 8` gives
mass ≤ 38.79489 (loss 1.1·10⁻⁶ of margin), `N = 16` gives 38.79481.

Axiom check (scratch file outside the repository):

```lean
import UnitDistance.Sqrt241.Numerics.Margin
#print axioms UnitDistance.Sqrt241.Witness.uniform_margin
-- [propext, Classical.choice, Quot.sound]
```

## Open items

None for the numerics. For other streams:

* `docs/SQRT241_PORT.md` (§2 numeric row, §4) still describes `s′ = 114697/100000`
  with `q = 6/5`; the witness now uses the manuscript's `s` (this note).
* If the ceiling moves, use `uniform_threshold` (threshold 0.0496189).
