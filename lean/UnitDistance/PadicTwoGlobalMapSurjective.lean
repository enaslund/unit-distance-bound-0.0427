module

public import UnitDistance.PadicTwoGlobalMap
public import UnitDistance.SigmaUnramifiedFrobenius

@[expose] public section
set_option backward.privateInPublic true


/-! The actual local-closure comparison is onto. Hence the image of the
maximal local pro-two group is the full fixed dyadic decomposition image. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace UnitDistance.PadicTwoGlobalMap
open PadicTwoMaximalProTwo
attribute [local instance] PrimeCompletion.primeFact PrimeCompletion.baseRationalAlgebra

theorem absoluteHom_surjective : Function.Surjective absoluteHom := by
  intro τ
  let σ : AbsoluteGroup :=
    { closureEquiv.trans (τ.toRingEquiv.trans closureEquiv.symm) with
      commutes' := by
        intro x
        change closureEquiv.symm (τ (closureEquiv (algebraMap ℚ_[2] Closure x)))=algebraMap ℚ_[2] Closure x
        rw [closureEquiv_commutes,τ.commutes]
        apply closureEquiv.injective
        rw [closureEquiv.apply_symm_apply,closureEquiv_commutes] }
  refine ⟨σ,?_⟩
  apply AlgEquiv.ext
  intro y
  change closureEquiv (closureEquiv.symm (τ (closureEquiv (closureEquiv.symm y))))=τ y
  rw [closureEquiv.apply_symm_apply,closureEquiv.apply_symm_apply]

theorem decomposition_surjective : Function.Surjective decomposition := by
  intro d
  obtain ⟨σ,hσ⟩ := absoluteHom_surjective (PrimeCompletion.decompositionEquiv prime d)
  refine ⟨σ,?_⟩
  change (PrimeCompletion.decompositionEquiv prime).symm (absoluteHom σ)=d
  rw [hσ,ContinuousMulEquiv.symm_apply_apply]

theorem decompositionMap_apply (σ : AbsoluteGroup) :
    SigmaUnramified.decompositionMap prime (decomposition σ)=absoluteMap σ := rfl

/-- Both actual definitions have exactly the same full arithmetic image. -/
theorem toGlobal_range_eq_decomposition_range :
    toGlobal.toMonoidHom.range=(SigmaUnramified.decompositionMap prime).toMonoidHom.range := by
  apply le_antisymm
  · rintro _ ⟨g,rfl⟩
    obtain ⟨σ,rfl⟩ := projection_surjective g
    exact ⟨decomposition σ,rfl⟩
  · rintro _ ⟨d,rfl⟩
    obtain ⟨σ,rfl⟩ := decomposition_surjective d
    exact ⟨projection σ,rfl⟩

end UnitDistance.PadicTwoGlobalMap
