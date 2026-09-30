module

public import UnitDistance.Sqrt241.Genus.LocalTypes

@[expose] public section
set_option backward.privateInPublic true


/-!
# The analytic bridge from the canonical genus field

`fixedBaseCeiling_lt_of_genus_bound`: the one hypothesis `H` of
`ChallengeZeta241.lean` on the canonical genus field
`E = CanonicalGenus.Carrier` (degree 512, Galois over ℚ), together with the
local types of a Galois field `M ⊇ E` at 2, 29, 7 and the nine census primes,
bounds the fixed-base residue ceiling of `M` at `ε = 1/300` by
`Witness.ceiling = 495/10000`.

The facts about `E` are proved in `Genus/*`: `finrank ℚ E = 512`
(`Genus.finrank_carrier`), `IsGalois ℚ E` (instance `Genus.isGalois_carrier`)
and the local types (`Genus.genusLocalTypes`).
-/

noncomputable section
open NumberField

namespace UnitDistance.Sqrt241

open UnitDistance.NumberFieldAnalysis

/-- **Analytic bridge.** Only standard axioms. -/
theorem fixedBaseCeiling_lt_of_genus_bound
    (M : Type) [Field M] [NumberField M] [IsGalois ℚ M]
    [Algebra UnitDistance.Sqrt241.CanonicalGenus.Carrier M]
    (h2 : (rationalPrimeIdeal 2).ramificationIdxIn (𝓞 M) = 8 ∧
      (rationalPrimeIdeal 2).inertiaDegIn (𝓞 M) = 4)
    (h29 : (rationalPrimeIdeal 29).ramificationIdxIn (𝓞 M) = 1 ∧
      (rationalPrimeIdeal 29).inertiaDegIn (𝓞 M) = 4)
    (h7 : (rationalPrimeIdeal 7).ramificationIdxIn (𝓞 M) = 1 ∧
      (rationalPrimeIdeal 7).inertiaDegIn (𝓞 M) = 8)
    (hcensus : ∀ p ∈ ({41, 47, 53, 59, 61, 67, 79, 83, 97} : Finset ℕ),
      4 ≤ (rationalPrimeIdeal p).inertiaDegIn (𝓞 M))
    (H : Real.log (dedekindZeta CanonicalGenus.Carrier ((1 + (1 / 300 : ℝ) : ℝ) : ℂ)).re /
          (512 : ℝ) + (1 / 300 : ℝ) *
        ((Witness.logRD - Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 4 -
          (logDeriv (dedekindZeta CanonicalGenus.Carrier) 2).re / (512 : ℝ)) <
        852 / 10000) :
    fixedBaseResidueCeiling M Witness.logRD (1 / 300) < Witness.ceiling :=
  Analytic.fixedBaseCeiling_lt_of_local_types Genus.finrank_carrier Genus.genusLocalTypes
    h2 h29 h7 hcensus H

end UnitDistance.Sqrt241
