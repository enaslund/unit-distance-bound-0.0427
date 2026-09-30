module

public import UnitDistance.Sqrt241.Geometry.FixedBaseBridge
public import UnitDistance.Sqrt241.Numerics.Margin
public import UnitDistance.Sqrt241.Analytic.GenusBridge

@[expose] public section
set_option backward.privateInPublic true


/-!
# Assembly: the planar target from tower data and the genus-field hypothesis

This module combines the three completed parts of the ℚ(√241) development:

* `target_of_growing_galois_fields` (downstream geometric chain, `Geometry/`);
* `Witness.uniform_margin` (numerical margin, `Numerics/`), which discharges
  the margin hypothesis of the downstream chain;
* `fixedBaseCeiling_lt_of_genus_bound` (analytic bridge, `Analytic/`), which
  turns the hypothesis H on the canonical genus field into the fixed-base
  ceiling of the retained field `M`.

The remaining hypotheses of `target_of_tower_data` are exactly the
obligations of the tower over `B = ℚ(√241)`: a Galois number field `M`
receiving the canonical genus field, with its local types at 2, 29, 7 and the
census primes, `√3, √−1 ∈ M`, its root discriminant, and a growing family of
Galois fields `Ks j ⊇ M` with the five local types, complex conjugation,
prime freedom and centralizer index at least `2^16`.
-/

noncomputable section
open NumberField Filter
namespace UnitDistance.Sqrt241

/-- The planar sequence theorem at exponent `10427/10000` from the tower data
and the hypothesis H on the canonical genus field. -/
theorem target_of_tower_data
    (M : Type) [Field M] [NumberField M] [IsGalois ℚ M]
    [Algebra CanonicalGenus.Carrier M]
    (Ks : ℕ → Type) [∀ j, Field (Ks j)] [∀ j, NumberField (Ks j)]
    [∀ j, IsGalois ℚ (Ks j)] [∀ j, Algebra M (Ks j)]
    (φ : ∀ j, Ks j →+* ℂ) (c : ∀ j, Gal(Ks j/ℚ))
    (hc : ∀ j, NumberField.ComplexEmbedding.IsConj (φ j) (c j))
    (hc1 : ∀ j, c j ≠ 1)
    (hdegree : Tendsto (fun j => Module.finrank ℚ (Ks j)) atTop atTop)
    (hunrM : ∀ᶠ j in atTop, NumberFieldAnalysis.FiniteUnramified M (Ks j))
    (he : ∀ᶠ j in atTop, ∀ a : Fin 5,
      (NumberFieldAnalysis.rationalPrimeIdeal (Witness.primes a)).ramificationIdxIn
        (𝓞 (Ks j)) = Witness.ramification a)
    (hf : ∀ᶠ j in atTop, ∀ a : Fin 5,
      (NumberFieldAnalysis.rationalPrimeIdeal (Witness.primes a)).inertiaDegIn
        (𝓞 (Ks j)) = Witness.residueDegree a)
    (hfree : ∀ᶠ j in atTop, ∀ (a : Fin 5)
      (P : NumberFieldAnalysis.PrimeNormFiber (Ks j) (Witness.primeNorm a)),
        Ideal.map (RingOfIntegers.mapRingHom (c j).toRingHom) P.1.asIdeal ≠ P.1.asIdeal)
    (hindex : ∀ᶠ j in atTop, 65536 ≤ (Subgroup.centralizer (Set.singleton (c j))).index)
    (hdiscM : Real.log (NumberFieldAnalysis.rootDiscriminant M) ≤ Witness.logRD)
    (r3 : M) (hr3 : r3 ^ 2 = 3) (ii : M) (hii : ii ^ 2 = -1)
    (h2 : (NumberFieldAnalysis.rationalPrimeIdeal 2).ramificationIdxIn (𝓞 M) = 8 ∧
      (NumberFieldAnalysis.rationalPrimeIdeal 2).inertiaDegIn (𝓞 M) = 4)
    (h29 : (NumberFieldAnalysis.rationalPrimeIdeal 29).ramificationIdxIn (𝓞 M) = 1 ∧
      (NumberFieldAnalysis.rationalPrimeIdeal 29).inertiaDegIn (𝓞 M) = 4)
    (h7 : (NumberFieldAnalysis.rationalPrimeIdeal 7).ramificationIdxIn (𝓞 M) = 1 ∧
      (NumberFieldAnalysis.rationalPrimeIdeal 7).inertiaDegIn (𝓞 M) = 8)
    (hcensus : ∀ p ∈ ({41, 47, 53, 59, 61, 67, 79, 83, 97} : Finset ℕ),
      4 ≤ (NumberFieldAnalysis.rationalPrimeIdeal p).inertiaDegIn (𝓞 M))
    (H : Real.log (dedekindZeta CanonicalGenus.Carrier
          ((1 + (1 / 300 : ℝ) : ℝ) : ℂ)).re / (512 : ℝ) + (1 / 300 : ℝ) *
        ((Witness.logRD - Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 4 -
          (logDeriv (dedekindZeta CanonicalGenus.Carrier) 2).re / (512 : ℝ)) <
        852 / 10000) :
    Target :=
  target_of_growing_galois_fields M Ks φ c hc hc1 hdegree hunrM he hf hfree hindex hdiscM
    r3 hr3 ii hii
    (fun θ hθ => lt_trans (by norm_num) (Witness.uniform_margin θ hθ))
    (fixedBaseCeiling_lt_of_genus_bound M h2 h29 h7 hcensus H)

end UnitDistance.Sqrt241
