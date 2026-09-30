module

public import UnitDistance.GaloisRetainedFamily
public import UnitDistance.SIntegerWitnessGaloisFamily
public import UnitDistance.RationalGaloisAlgebra

@[expose] public section
set_option backward.privateInPublic true


/-! The terminal reduction from an actual infinite Galois quotient and actual
finite-layer local arithmetic; no preassigned number-field family is assumed. -/
noncomputable section
set_option maxHeartbeats 800000
open NumberField Filter
open scoped Classical
namespace UnitDistance.SIntegerCRT
open NumberFieldAnalysis Witness GaloisQuotient ArithmeticRetained
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω]
variable {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  [T2Space Q] [CompactSpace Q] [TotallyDisconnectedSpace Q] [Infinite Q]
variable (ρ : Gal(Ω/ℚ) →ₜ* Q) (hρ : Function.Surjective ρ)
variable (e : RetainedField →ₐ[ℚ] Ω)
variable {C : Type} [Group C] [Fintype C] [TopologicalSpace C] [DiscreteTopology C]
variable (χ : Gal(Ω/ℚ) →ₜ* C)
variable (hM : ρ.toMonoidHom.ker ≤ e.fieldRange.fixingSubgroup)
variable (hχ : ρ.toMonoidHom.ker ≤ χ.toMonoidHom.ker)

/-- All global growth and signature assertions are derived from the actual
infinite quotient and its finite detector. The remaining arithmetic hypotheses
are about unramifiedness and actual prime ideals in the constructed layers. -/
theorem target_of_infinite_retained_quotient
    (hχsurj : Function.Surjective χ) (Φ : Ω →+* ℂ) (c : Gal(Ω/ℚ))
    (hc : NumberField.ComplexEmbedding.IsConj Φ c)
    (hindex : 4096 ≤ (Subgroup.centralizer ({χ c} : Set C)).index)
    (hunrM : ∀ᶠ j in atTop, FiniteUnramified RetainedField (retainedLevel ρ hρ e χ hM hχ j))
    (he : ∀ᶠ j in atTop, ∀a : Fin 11,
      (rationalPrimeIdeal (primes a)).ramificationIdxIn
        (𝓞 (retainedLevel ρ hρ e χ hM hχ j)) = ramification a)
    (hf : ∀ᶠ j in atTop, ∀a : Fin 11,
      (rationalPrimeIdeal (primes a)).inertiaDegIn
        (𝓞 (retainedLevel ρ hρ e χ hM hχ j)) = residueDegree a)
    (hfree : ∀ᶠ j in atTop, ∀a : Fin 11,
      ∀P : PrimeNormFiber (retainedLevel ρ hρ e χ hM hχ j) (primeNorm a),
      Ideal.map (RingOfIntegers.mapRingHom
        (retainedLevelConjugation ρ hρ e χ hM hχ c j).toRingHom) P.1.asIdeal ≠ P.1.asIdeal)
    (hpair : (1379635324335 : ℝ)/10^12 ≤ JPair)
    (hdiscM : Real.log (rootDiscriminant RetainedField) ≤ logRD)
    (hfinite : Real.log (dedekindZeta RetainedField ((1+(1/12000:ℝ):ℝ):ℂ)).re /
        (524288 : ℝ) + (1/12000:ℝ)*
          ((logRD-Real.eulerMascheroniConstant-Real.log (4*Real.pi))/4-
            (logDeriv (dedekindZeta RetainedField) 2).re/(524288 : ℝ)) < ceiling) :
    Target := by
  let Ks : ℕ → Type := fun j => retainedLevel ρ hρ e χ hM hχ j
  let E (j : ℕ) := @RationalGalois.autEquiv (Ks j) _
    (retainedLevel_algebra ρ hρ e χ hM hχ j) DivisionRing.toRatAlgebra
  let cN (j : ℕ) := E j (retainedLevelConjugation ρ hρ e χ hM hχ c j)
  letI : ∀j, @IsGalois ℚ _ (Ks j) _ DivisionRing.toRatAlgebra := fun j =>
    @RationalGalois.isGalois (Ks j) _ (retainedLevel_algebra ρ hρ e χ hM hχ j)
      DivisionRing.toRatAlgebra (retainedLevel_galois ρ hρ e χ hM hχ j)
  refine target_of_growing_retained_galois_fields Ks
    (retainedLevelEmbedding ρ hρ e χ hM hχ Φ) cN ?_ ?_
    ?_ hunrM he hf ?_ ?_ hpair hdiscM hfinite
  · intro j
    change ComplexEmbedding.conjugate _ = _
    apply RingHom.ext
    intro x
    change star (retainedLevelEmbedding ρ hρ e χ hM hχ Φ j x) =
      retainedLevelEmbedding ρ hρ e χ hM hχ Φ j (cN j x)
    have hx : cN j x = retainedLevelConjugation ρ hρ e χ hM hχ c j x :=
      RationalGalois.autEquiv_apply _ _ _ _ _
    rw [hx]
    exact (retainedLevel_isConj ρ hρ e χ hM hχ Φ c hc j).eq x |>.symm
  · intro j heq
    apply retainedLevel_conjugation_ne_one ρ hρ e χ hM hχ Φ c hc j
    exact (E j).injective (heq.trans (E j).map_one.symm)
  · convert retainedLevel_degree_tendsto ρ hρ e χ hM hχ using 1
    funext j
    exact (RationalGalois.finrank_eq (Ks j)
      (retainedLevel_algebra ρ hρ e χ hM hχ j) DivisionRing.toRatAlgebra).symm
  · filter_upwards [hfree] with j hj
    intro a P
    have heq : (cN j).toRingHom =
        (retainedLevelConjugation ρ hρ e χ hM hχ c j).toRingHom := by
      apply RingHom.ext
      intro x
      exact RationalGalois.autEquiv_apply _ _ _ _ _
    rw [heq]
    exact hj a P
  · apply Eventually.of_forall
    intro j
    have h0 := retainedLevel_conjugacy_index ρ hρ e χ hM hχ hχsurj c hindex j
    have h1 := GaloisConjugation.centralizer_index_le_of_surjective
      (E j).symm.toMonoidHom (E j).symm.surjective (cN j)
    dsimp only [cN] at h1
    simp only [MulEquiv.coe_toMonoidHom,MulEquiv.symm_apply_apply] at h1
    exact h0.trans h1

end UnitDistance.SIntegerCRT
