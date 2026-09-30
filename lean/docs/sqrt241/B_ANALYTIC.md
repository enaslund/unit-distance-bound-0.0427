# Stream B: canonical genus field and analytic bridge

Owner directories: `UnitDistance/Sqrt241/Analytic/`, `UnitDistance/Sqrt241/Genus/`,
`scripts/sqrt241/generate_analytic_numerics.py`, this note.

## Status (2026-09-29): Goals 1 and 2 done

All modules below compile with `lake build`; every listed theorem depends only
on `propext`, `Classical.choice`, `Quot.sound` (checked with `#print axioms`
from a scratch file outside the repository). No `sorry`, `axiom`,
`native_decide`, `implemented_by`/`extern`; kernel computations use
`decide +kernel`. (The deprecated `inertiaDeg'` lemmas formerly used in
`Analytic/Fibers.lean` and `Genus/Frobenius.lean` were replaced by
`Ideal.pow_inertiaDeg` and `Ideal.inertiaDeg_eq_of_isMaximal` on 2026-09-29.)

| module | content |
|---|---|
| `Analytic/Fibers.lean` | weighted Euler defects of `K/F` above finitely many rational primes (any antitone nonnegative weight: Euler log at σ, prime-debit weight); Galois evaluation `φ(p^f)/(e f)` |
| `Analytic/NumericsBasic.lean` | directed enclosures of `a(q) = -log(1-q^{-σ})`, σ = 1 + 1/300, and of `log q/(q²-1)` |
| `Analytic/Numerics.lean` | generated certificates; `Numerics.corrections_ge` |
| `Analytic/Bridge.lean` | `Analytic.fixedBaseCeiling_lt_of_local_types` (abstract `E ⊆ M`) |
| `Analytic/GenusBridge.lean` | **`UnitDistance.Sqrt241.fixedBaseCeiling_lt_of_genus_bound`** (Goal 1) |
| `Genus/Kummer.lean` | one quadratic Kummer step inside an intermediate field |
| `Genus/Base.lean` | `B = ℚ(√241)` via `QuadraticAlgebra ℚ 241 0` and `ev`; radicands, norms, conjugates; kernel certificate that no nonempty product of radicands is a square in `B` |
| `Genus/Degree.lean` | `Genus.finrank_carrier : finrank ℚ Carrier = 512` |
| `Genus/Galois.lean` | instances `Genus.normal_carrier`, `Genus.isGalois_carrier`; `σ(√241) = ±√241`, `σ² = 1` if `σ` fixes `√241`, `σ⁴ = 1` |
| `Genus/Frobenius.lean` | generic (any number field Galois over ℚ): `f ∣ n` if the decomposition group has exponent dividing `n` (Frobenius lift); `e = 1` from trivial inertia; `e f = |D|`; Fermat `x^(p^f) ≡ x`; `n ≤ e` from `p ∈ Pⁿ` |
| `Genus/Integers.lean` | explicit integers of `E` (`√241`, radicands, conjugates, genus roots, `ℚ(√241) → E`) |
| `Genus/Local.lean` | inertia trivial away from 2, 3, 5, 241; decomposition group fixes `√241` at split primes and at 2; `|D| ≤ 8` at 2 |
| `Genus/LocalTypes.lean` | `Genus.genusLocalTypes : Analytic.GenusLocalTypes Carrier` |
| `Genus/ExactTypes.lean` | `Genus.exactLocalTypes`: (e,f) = (4,2) at 2, (1,2) at 29, (1,4) at 7 (a complement: not used by the final proof, which needs only the upper bounds of `Genus.genusLocalTypes`; of this module the final proof uses `ramificationIdxIn_29`, `ramificationIdxIn_7` (`e = 1`, for the Frobenius labels in `Local/Caps.lean`) and `gE_zero_sq` (`√−1`, in `Retained/Field.lean`)) |

## Statements

### Goal 1

```lean
theorem UnitDistance.Sqrt241.fixedBaseCeiling_lt_of_genus_bound
    (M : Type) [Field M] [NumberField M] [IsGalois ℚ M]
    [Algebra UnitDistance.Sqrt241.CanonicalGenus.Carrier M]
    (h2 : (rationalPrimeIdeal 2).ramificationIdxIn (𝓞 M) = 8 ∧ (rationalPrimeIdeal 2).inertiaDegIn (𝓞 M) = 4)
    (h29 : (rationalPrimeIdeal 29).ramificationIdxIn (𝓞 M) = 1 ∧ (rationalPrimeIdeal 29).inertiaDegIn (𝓞 M) = 4)
    (h7 : (rationalPrimeIdeal 7).ramificationIdxIn (𝓞 M) = 1 ∧ (rationalPrimeIdeal 7).inertiaDegIn (𝓞 M) = 8)
    (hcensus : ∀ p ∈ ({41, 47, 53, 59, 61, 67, 79, 83, 97} : Finset ℕ),
      4 ≤ (rationalPrimeIdeal p).inertiaDegIn (𝓞 M))
    (H : Real.log (dedekindZeta CanonicalGenus.Carrier ((1 + (1 / 300 : ℝ) : ℝ) : ℂ)).re / (512 : ℝ) +
        (1 / 300 : ℝ) * ((Witness.logRD - Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 4 -
          (logDeriv (dedekindZeta CanonicalGenus.Carrier) 2).re / (512 : ℝ)) < 852 / 10000) :
    fixedBaseResidueCeiling M Witness.logRD (1 / 300) < Witness.ceiling
```

(`rationalPrimeIdeal`, `fixedBaseResidueCeiling` are the `UnitDistance.NumberFieldAnalysis`
names; `Witness` is `UnitDistance.Sqrt241.Witness`.) Only facts about `M` are
assumed; the `[Algebra Carrier M]` instance is arbitrary. `H` is the H of
`ChallengeZeta241.lean` with `Witness.logRD` (same body as the challenge's
`logRD`) and the literal `852/10000`.

Proof outline. With `σ = 1 + 1/300` and `T = {2, 29, 7} ∪ census`:

    log ζ_M(σ)/[M:ℚ] ≤ log ζ_E(σ)/512 − Σ_{p∈T} (a(p^{f_E})/(e_E f_E) − a(p^{f_M})/(e_M f_M)),
    D_M ≤ D_E − Σ_{p∈{2,29,7}} (w(p^{f_E})/(e_E f_E) − w(p^{f_M})/(e_M f_M)),

(`Fibers.normalized_weight_le_sub_contributions`: fiberwise Euler defects of
`M/E` are nonnegative, the finite subfamily over `T` is evaluated exactly with
the Galois formula `#{P | p} · e f = [K:ℚ]`), `D_K` the normalized prime debit,
`D_E = −(ζ_E'/ζ_E)(2)/512` (`normalizedPrimeDebit_eq_neg_logDeriv`). The types of
`E` enter only through upper bounds (`Analytic.GenusLocalTypes`):

| p | used for E | used for M |
|---|---|---|
| 2 | `f ∣ 2`, `e f ≤ 8` ⇒ contribution ≥ a(4)/8 | (8,4): a(16)/32 |
| 29 | `e = 1`, `f ∣ 2` ⇒ ≥ a(29²)/2 | (1,4): a(29⁴)/4 |
| 7 | `e = 1`, `f ∣ 4` ⇒ ≥ a(7⁴)/4 | (1,8): a(7⁸)/8 |
| census | `e = 1`, `f ∣ 2` ⇒ ≥ a(p²)/2 | `f ≥ 4` ⇒ ≤ a(p⁴)/4 |

(`a(q^k) ≤ k a(q)` and `w(q^k) ≤ k w(q)` handle `f = 1`.)

### Goal 2 (facts about E = `CanonicalGenus.Carrier`)

* `Genus.finrank_carrier : Module.finrank ℚ Carrier = 512`. Tower
  `ℚ(√241) ⊂ … ⊂ ℚ(√241, √α₀, …, √α₇)`; an element of `B` that is a square in
  the `j`-th field is a square in `B` up to a product of radicands with index
  `< j`; `Base.nonsquareCert_all` checks by `decide +kernel`, for all 255
  nonempty subsets, that the product of radicands has non-square norm or is a
  rational `r` with neither `r` nor `r/241` a square.
* `Genus.isGalois_carrier : IsGalois ℚ Carrier` (instance). Normality from
  explicit square roots of the conjugate radicands:
  `ᾱ₀ = α₀`, `ᾱ₁ = −1/α₁`, `ᾱ₂ = −α₃`, `ᾱ₃ = −α₂`, `ᾱ₄ = α₅`, `ᾱ₆ = α₇`.
* `Genus.genusLocalTypes : Analytic.GenusLocalTypes Carrier` (the upper bounds used by
  Goal 1). Also, for every prime `p ∉ {2,3,5,241}`: `e = 1`, `f ∣ 4`, and `f ∣ 2` if
  `241` is a square mod `p` (`ramificationIdxIn_eq_one`, `inertiaDegIn_dvd_four`,
  `inertiaDegIn_dvd_two_of_sqrt`).
* Complement, not used by the final proof: `Genus.exactLocalTypes`, the exact types
  (e,f) = (4,2) at 2, (1,2) at 29, (1,4) at 7 (its lemmas `ramificationIdxIn_29` and
  `ramificationIdxIn_7` are used, for the Frobenius labels of `Local/Caps.lean`).

Arguments (all with Mathlib's `Ideal.card_stabilizer_eq`,
`Ideal.card_inertia_eq_ramificationIdxIn`, `Ideal.Quotient.stabilizerHom_surjective`):
inertia moving `√241` or `√α_i` would put `2√241` or `2√α_i` in `P`, forcing
`p ∣ 964` or `p ∣ 4N(α_i)`; at split `p` (`241 ≡ c²`) or at 2 (`π₂π₂' = 2`,
`π₂' − π₂ = 6101`) the decomposition group cannot exchange the two primes of
`B`, so it lies in `Gal(E/B)` (exponent 2) and the Frobenius gives `f ∣ 2`. At 2,
`|D| ≤ 8`: for the five products `ρ` of genus roots whose squares are `≡ 1 mod π³`
(`kappaA*`, `kappaB*`: `κ = (1−ρ²)/π³` integral), `γ = π'(1+ρ)/2` is integral
with `γ(π'−γ) = πκ ∈ P`, so an element of `D` with `σρ = −ρ` would put `π'` in
`P`; the remaining three signs determine `σ`. Lower bounds: `2 = (1−ζ₈)⁴u` gives
`e ≥ 4` at 2; the golden ratio (at 2), `√2` (at 29, `2^14 ≢ 1 mod 29`) and `√ε`
(at 7, `ε^24 ≡ −1 mod 7`) have no residue in the prime field resp. `𝔽₄₉`.

## Numbers

`Numerics.corrections_ge` certifies, with kernel-checked rational enclosures
(logs via `UnitDistance.log_enclosure`, `q^{-1/300}` via `Real.exp_bound`,
`−log(1−y)` via its series and Taylor remainder):

    Σ_{p∈T} [a(p^{f_E})/(e_E f_E) − a(p^{f_M})/(e_M f_M)]
      + (1/300) Σ_{p∈{2,29,7}} [w(p^{f_E})/(e_E f_E) − w(p^{f_M})/(e_M f_M)]
      ≥ 0.035753613221 > 357/10000 = 852/10000 − 495/10000.

| part | value |
|---|---|
| design primes, log ζ | 0.0344534299 (2: 0.0337706405, 29: 0.0005813329, 7: 0.0001014565) |
| census (9 primes), log ζ | 0.0012627908 |
| debit × ε, design primes | 0.0000373926 |
| total (PARI, 50 digits) | 0.0357536133046 |
| certified lower bound | 0.035753613221 |
| **slack** over 357/10000 | **5.361e-5** |

These reproduce `SQRT241_PORT.md` §1 (0.0344534, 0.0000374, 0.0012628) and the
formulas of `certificates/ceiling241.py` (`exc`, census saving `a(N²)/4 −
a(N⁴)/8` per prime of B). `python-flint`/`mpmath` are not installed on this
host, so the check was done with PARI/GP and exact `fractions` arithmetic.

Consequences: with H at 852/10000 the tower ceiling 0.0495 holds with 5.36e-5
to spare. The largest H-ceiling that still yields `Witness.ceiling = 0.0495`
with these corrections is 0.0495 + 0.0357536 = **0.0852536**. Without the
debit correction the slack would be 1.62e-5. With the numerical value of H's
left side (≈ 0.0848336, `afe241.py`) the bound on the tower ceiling is ≈ 0.04908.

## Open items / notes

* H itself is the hypothesis; its numerical evaluation (`afe241.py`, PARI
  `lfun`) is outside Lean.
* The census could be extended (more primes of B with `f_M ≥ 4`) if more slack
  is ever needed; each prime needs only its `c` with `c² ≡ 241 (mod p)` in
  `Genus.LocalTypes.sqrt241Mod` and entries in the generator.
* For stream A: the conclusion matches the hypothesis `hfinite` of the
  planned `target_of_growing_galois_fields` (`fixedBaseResidueCeiling M
  Witness.logRD (1/300) < Witness.ceiling`).
* Checked (scratch file importing `ChallengeZeta241` and `Analytic.GenusBridge`):
  the theorem accepts the challenge's literal `hfinite` (stated with
  `UnitDistanceSqrt241Submission.CanonicalGenus.Carrier`, `.logRD`, `.ceiling`)
  directly by `exact`, i.e. the two `CanonicalGenus` copies, `logRD` and
  `852/10000` agree definitionally.

## Rebuild

    ./.toolchain/bin/lake build UnitDistance.Sqrt241.Analytic.GenusBridge UnitDistance.Sqrt241.Genus.ExactTypes
    python3 scripts/sqrt241/generate_analytic_numerics.py   # regenerates Analytic/Numerics.lean

A full rebuild of the fourteen modules takes about a minute on this host.
