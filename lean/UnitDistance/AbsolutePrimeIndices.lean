module

public import UnitDistance.ChosenPrimeInertiaImage
public import UnitDistance.AbsolutePrimeImages

@[expose] public section
set_option backward.privateInPublic true


/-! Actual ramification and residue degrees recovered from absolute local images. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open NumberField IsDedekindDomain
namespace UnitDistance.PrimeCompletion
open AlgebraicNumberTheory.Valuations
attribute [local instance] primeFact baseRationalAlgebra
variable (p : Nat.Primes) (M : Type) [Field M] [NumberField M] [IsGalois ℚ M]
  (j : M →ₐ[ℚ] AlgebraicClosure ℚ)

/-- Every extension-center at `p` lies over the literal integer ideal `(p)`. -/
theorem finitePlaceCentre_liesOver_rationalPrime
    (w : AbsoluteValueExtension (HeightOneSpectrum.adicAbv ℚ (place p)) M) :
    (finitePlaceExtensionCentre (place p) w).asIdeal.LiesOver
      (NumberFieldAnalysis.rationalPrimeIdeal p.val) := by
  let P := finitePlaceExtensionCentre (place p) w
  letI := P.isPrime
  letI : P.asIdeal.LiesOver (place p).asIdeal := finitePlaceExtensionCentre_liesOver (place p) w
  have hmem : (p.val : 𝓞 M) ∈ P.asIdeal := by
    have h : (p.val : 𝓞 ℚ) ∈ P.asIdeal.under (𝓞 ℚ) := by
      rw [←Ideal.over_def P.asIdeal (place p).asIdeal]
      exact prime_mem_place p
    change algebraMap (𝓞 ℚ) (𝓞 M) (p.val : 𝓞 ℚ) ∈ P.asIdeal at h
    simpa using h
  constructor
  apply Ideal.IsMaximal.eq_of_le (inferInstance :
    (NumberFieldAnalysis.rationalPrimeIdeal p.val).IsMaximal)
    (Ideal.IsPrime.ne_top (inferInstance : (P.asIdeal.under ℤ).IsPrime))
  rw [Ideal.span_singleton_le_iff_mem]
  change algebraMap ℤ (𝓞 M) (p.val : ℤ) ∈ P.asIdeal
  simpa using hmem

/-- Genuine absolute inertia image size is the actual absolute ramification index. -/
theorem inertiaRestriction_card : Nat.card (inertiaRestriction p M j).range=
    (NumberFieldAnalysis.rationalPrimeIdeal p.val).ramificationIdxIn (𝓞 M) := by
  rw [inertiaRestriction_card_eq_chosenIdeal M p j]
  let P := chosenLocalPrime M (place p)
  letI : P.asIdeal.LiesOver (NumberFieldAnalysis.rationalPrimeIdeal p.val) :=
    finitePlaceCentre_liesOver_rationalPrime p M (chosenFinitePlaceExtension (L:=M) (place p))
  exact Ideal.card_inertia_eq_ramificationIdxIn (G:=Gal(M/ℚ))
    (NumberFieldAnalysis.rationalPrimeIdeal p.val) P.asIdeal

/-- The image of actual absolute inertia equals inertia of the same actual center prime. -/
theorem inertiaRestriction_range_eq : (inertiaRestriction p M j).range=
    (restrictedAbsolutePrime M p j).asIdeal.inertia Gal(M/ℚ) := by
  apply Subgroup.eq_of_le_of_card_ge (inertiaRestriction_range_le p M j)
  rw [inertiaRestriction_card p M j]
  let P := restrictedAbsolutePrime M p j
  letI : P.asIdeal.LiesOver (NumberFieldAnalysis.rationalPrimeIdeal p.val) :=
    restrictedAbsolutePrime_liesOver M p j
  exact (Ideal.card_inertia_eq_ramificationIdxIn (G:=Gal(M/ℚ))
    (NumberFieldAnalysis.rationalPrimeIdeal p.val) P.asIdeal).le

/-- Exact actual `e` and `f` follow from exact arithmetic local-image cardinalities. -/
theorem ramification_residue_of_absolute_image_cards (e f : ℕ) (hepos : 0<e)
    (he : Nat.card (inertiaRestriction p M j).range=e)
    (hd : Nat.card (decompositionRestriction p M j).range=e*f) :
    (NumberFieldAnalysis.rationalPrimeIdeal p.val).ramificationIdxIn (𝓞 M)=e ∧
    (NumberFieldAnalysis.rationalPrimeIdeal p.val).inertiaDegIn (𝓞 M)=f := by
  rw [inertiaRestriction_card p M j] at he
  rw [decompositionRestriction_card p M j,he] at hd
  exact ⟨he,Nat.eq_of_mul_eq_mul_left hepos hd⟩

end UnitDistance.PrimeCompletion
