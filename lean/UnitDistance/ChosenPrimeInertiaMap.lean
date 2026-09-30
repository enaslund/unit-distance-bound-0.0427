module

public import UnitDistance.ChosenPrimeInertia
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Galois.CyclicPrimeSubextension
public import UnitDistance.RationalInertiaBaseChange

@[expose] public section
set_option backward.privateInPublic true


/-! The actual finite inertia image, computed through the chosen localization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
open NumberField IsDedekindDomain
open scoped Pointwise ValuativeRel NNReal
namespace UnitDistance.PrimeCompletion
open HilbertRamification AlgebraicNumberTheory.Valuations
open ArithmeticProP LocalClassFieldTheory LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
attribute [local instance] primeFact baseRationalAlgebra
variable (M : Type) [Field M] [NumberField M] [IsGalois ℚ M]
variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem chosenLocal_stabilizerComparison :
    absoluteValueDecompositionGroup ℚ (chosenFinitePlaceExtension (L:=M) v).1 =
      MulAction.stabilizer Gal(M/ℚ) (chosenLocalPrime M v).asIdeal := by
  let w := chosenFinitePlaceExtension (L:=M) v
  have hmap (σ : Gal(M/ℚ)) (P : Ideal (𝓞 M)) :
      σ • P=Ideal.map (RingOfIntegers.mapRingHom σ.toRingHom) P := by
    rw [Ideal.pointwise_smul_def]
    congr 1
  have hconj (σ : Gal(M/ℚ)) :
      (finitePlaceExtensionCentre v
        (absoluteValueExtensionConjugate (HeightOneSpectrum.adicAbv ℚ v) w σ)).asIdeal=
        σ⁻¹ • (finitePlaceExtensionCentre v w).asIdeal := by
    rw [finitePlaceExtensionCentre_conjugate,finitePlaceEquiv_asIdeal,hmap]
    rfl
  ext σ
  rw [mem_absoluteValueDecompositionGroup_iff_extensionConjugate_eq
    (HeightOneSpectrum.adicAbv ℚ v) (RayClass.adicAbv_isNontrivial v)]
  change _ ↔ σ • (finitePlaceExtensionCentre v w).asIdeal = _
  constructor
  · intro h
    have he := congrArg (fun w => (finitePlaceExtensionCentre v w).asIdeal) h
    rw [hconj] at he
    exact ((inv_smul_eq_iff).mp he).symm
  · intro h
    apply finitePlaceExtensionCentre_injective v
    apply HeightOneSpectrum.ext
    rw [hconj]
    exact inv_smul_eq_iff.mpr h.symm

/-- The exact image of local finite inertia under restriction is ideal inertia. -/
theorem chosenLocal_inertia_map :
    ((galoisGroupResidueAlgEquivHomOfIsIntegralClosure (chosenLocalBase v)
      (chosenLocalField M v)).ker).map (chosenLocalRestriction M v) =
    (chosenLocalPrime M v).asIdeal.inertia Gal(M/ℚ) := by
  apply le_antisymm
  · rintro _ ⟨τ,hτ,rfl⟩
    exact (chosenLocalRestriction_mem_inertia_iff M v τ).mpr hτ
  · intro σ hσ
    have hd := Ideal.inertia_le_stabilizer (M:=Gal(M/ℚ))
      (chosenLocalPrime M v).asIdeal hσ
    rw [←chosenLocal_stabilizerComparison M v] at hd
    let τ := decompositionGroupEquivAlgebraicLocalizationAut (HeightOneSpectrum.adicAbv ℚ v)
      (RayClass.adicAbv_isNontrivial v) (chosenFinitePlaceExtension (L:=M) v) ⟨σ,hd⟩
    have he : chosenLocalRestriction M v τ=σ := by
      change ((decompositionGroupEquivAlgebraicLocalizationAut
        (HeightOneSpectrum.adicAbv ℚ v) (RayClass.adicAbv_isNontrivial v)
        (chosenFinitePlaceExtension (L:=M) v)).symm τ).val=σ
      dsimp only [τ]
      rw [MulEquiv.symm_apply_apply]
    refine ⟨τ,(chosenLocalRestriction_mem_inertia_iff M v τ).mp ?_,he⟩
    rwa [he]

def chosenLocalEmbeddingRing : M →+* chosenLocalField M v :=
  AbsoluteValue.toAlgebraicLocalization (HeightOneSpectrum.adicAbv ℚ v)
    (chosenFinitePlaceExtension (L:=M) v).1 (chosenFinitePlaceExtension (L:=M) v).2

instance chosenLocal_charZero : CharZero (chosenLocalField M v) :=
  charZero_of_injective_ringHom (chosenLocalEmbeddingRing M v).injective

def chosenLocalEmbedding : M →ₐ[ℚ] chosenLocalField M v :=
  (chosenLocalEmbeddingRing M v).toRatAlgHom

theorem chosenLocalRestriction_commutes (τ : Gal(chosenLocalField M v / chosenLocalBase v))
    (x : M) : chosenLocalEmbedding M v (chosenLocalRestriction M v τ x)=
      τ (chosenLocalEmbedding M v x) := by
  let w := chosenFinitePlaceExtension (L:=M) v
  let e := decompositionGroupEquivAlgebraicLocalizationAut (HeightOneSpectrum.adicAbv ℚ v)
    (RayClass.adicAbv_isNontrivial v) w
  have h := localizationRamificationGroups_decompositionGroupEquiv_toLocalization
    (HeightOneSpectrum.adicAbv ℚ v) (RayClass.adicAbv_isNontrivial v) w (e.symm τ) x
  rw [show decompositionGroupEquivAlgebraicLocalizationAut _ _ _ (e.symm τ)=τ from e.apply_symm_apply τ] at h
  exact h.symm

variable (p : Nat.Primes) (j : M →ₐ[ℚ] AlgebraicClosure ℚ)
local instance chosenLocal_finite : Module.Finite (Base p) (chosenLocalField M (place p)) :=
  chosenFinitePlaceLocalizedFiniteDimensional (K:=ℚ) (L:=M) (place p)
local instance chosenLocal_galois : IsGalois (Base p) (chosenLocalField M (place p)) :=
  chosenFinitePlaceLocalizedIsGalois (K:=ℚ) (L:=M) (place p)

variable (f : chosenLocalField M (place p) →ₐ[Base p] SeparableClosure (Base p))

def chosenLocalRationalEmbedding : M →ₐ[ℚ] SeparableClosure (Base p) :=
  f.toRingHom.toRatAlgHom.comp (chosenLocalEmbedding M (place p))

theorem chosenLocalRestriction_absolute_commuting :
    (chosenLocalRestriction M (place p)).comp
      (finiteAbsoluteRestriction (Base p) (chosenLocalField M (place p)) f)=
      (GaloisEmbedding.restriction (chosenLocalRationalEmbedding M p f)).toMonoidHom.comp
        (AlgEquiv.restrictScalarsHom ℚ) := by
  apply MonoidHom.ext
  intro σ
  symm
  apply GaloisEmbedding.restriction_unique
  intro x
  change f (chosenLocalEmbedding M (place p)
      (chosenLocalRestriction M (place p)
        (finiteAbsoluteRestriction (Base p) (chosenLocalField M (place p)) f σ) x)) =
    σ (f (chosenLocalEmbedding M (place p) x))
  rw [chosenLocalRestriction_commutes]
  exact (finiteAbsoluteRestriction_commutes (Base p) (chosenLocalField M (place p)) f σ _).symm

end UnitDistance.PrimeCompletion
