module

public import UnitDistance.LocalTensorH2Evaluation
public import UnitDistance.TensorEvaluationH2
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Algebra

@[expose] public section
set_option backward.privateInPublic true


/-! Connect the actual completion evaluation to the generic field-unit
localization map, with no supplied compatibility or injectivity hypothesis. -/
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace UnitDistance.ArithmeticProP
open LocalClassFieldTheory AlgebraicNumberTheory.Valuations HilbertRamification

variable {K L : Type} [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L] [IsGalois K L]
variable (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
variable (w : AbsoluteValueExtension vK L)
local instance : Algebra vK.Completion (LocalizedCompletion vK w) :=
  localizedCompletionBaseAlgebra vK w
local instance : Algebra K (LocalizedCompletion vK w) :=
  localizedCompletionGlobalAlgebra vK w
local instance : IsScalarTower K vK.Completion (LocalizedCompletion vK w) :=
  localizedCompletionIsScalarTower vK w
local instance : MulDistribMulAction Gal(L/K) (vK.Completion ⊗[K] L)ˣ :=
  scalarTensorUnitsAction (K := K) (L := L) (A := vK.Completion)

/-- The actual global-to-local field embedding is equivariant for the
actual decomposition-group restriction. -/
theorem localizedCompletionToAlgHom_equivariant
    (σ : Gal((LocalizedCompletion vK w)/vK.Completion)) (x : L) :
    localizedCompletionToAlgHom vK w (localFieldToGlobalAut vK hvK w σ x) =
      σ (localizedCompletionToAlgHom vK w x) := by
  change AbsoluteValue.toAlgebraicLocalization vK w.1 w.2
    (localFieldToGlobalAut vK hvK w σ x) =
    σ (AbsoluteValue.toAlgebraicLocalization vK w.1 w.2 x)
  rw [localFieldToGlobalAut_apply]
  exact (localizationRamificationGroups_decompositionGroupEquiv_toLocalization vK hvK w
    ((decompositionGroupEquivAlgebraicLocalizationAut vK hvK w).symm σ) x).symm.trans
    (by rw [MulEquiv.apply_symm_apply])

/-- Both tensor evaluations are the same actual ring map. -/
theorem actualLocalTensorEvaluation_eq (z : vK.Completion ⊗[K] L) :
    UnitDistance.ArithmeticProP.localTensorEvaluation K L vK.Completion
      (LocalizedCompletion vK w) (localizedCompletionToAlgHom vK w) z =
    LocalClassFieldTheory.localTensorEvaluation vK hvK w z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp [hx,hy]
  | tmul a x =>
    rw [UnitDistance.ArithmeticProP.localTensorEvaluation_tmul,
      LocalClassFieldTheory.localTensorEvaluation_tmul]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The generic tensor evaluation map at the actual completion is injective on H². -/
theorem actualLocalTensorEvaluationH2_injective :
    Function.Injective
      (groupCohomology.map (localFieldToGlobalAut vK hvK w)
        (localTensorEvaluationRepHom K L vK.Completion (LocalizedCompletion vK w)
          (localizedCompletionToAlgHom vK w) (localFieldToGlobalAut vK hvK w)
          (localizedCompletionToAlgHom_equivariant vK hvK w)) 2).hom := by
  have hmap : groupCohomology.map (localFieldToGlobalAut vK hvK w)
        (localTensorEvaluationRepHom K L vK.Completion (LocalizedCompletion vK w)
          (localizedCompletionToAlgHom vK w) (localFieldToGlobalAut vK hvK w)
          (localizedCompletionToAlgHom_equivariant vK hvK w)) 2 =
      groupCohomology.map (localFieldToGlobalAut vK hvK w)
        (localTensorFieldEvaluationRepHom vK hvK w) 2 := by
    apply groupCohomology.map_congr rfl
    apply LinearMap.ext
    intro z
    apply Units.ext
    exact actualLocalTensorEvaluation_eq vK hvK w _
  rw [hmap]
  exact localTensorFieldEvaluationH2_injective vK hvK w

/-- Vanishing in the actual local field and actual tensor block are equivalent. -/
theorem fieldUnitsTensorH2_eq_zero_iff_localField
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :
    (fieldUnitsTensorH2 K L vK.Completion).hom x = 0 ↔
      (groupCohomology.map (localFieldToGlobalAut vK hvK w)
        (fieldUnitsEvaluationRepHom K L vK.Completion (LocalizedCompletion vK w)
          (localizedCompletionToAlgHom vK w) (localFieldToGlobalAut vK hvK w)
          (localizedCompletionToAlgHom_equivariant vK hvK w)) 2).hom x = 0 := by
  constructor
  · exact fieldUnitsEvaluation_eq_zero_of_tensor_eq_zero K L vK.Completion
      (LocalizedCompletion vK w) (localizedCompletionToAlgHom vK w)
      (localFieldToGlobalAut vK hvK w) (localizedCompletionToAlgHom_equivariant vK hvK w) x
  · intro hx
    apply actualLocalTensorEvaluationH2_injective vK hvK w
    rw [map_zero]
    have h := congrArg (fun m => m.hom x)
      (fieldUnitsTensorH2_evaluation K L vK.Completion
        (LocalizedCompletion vK w) (localizedCompletionToAlgHom vK w)
        (localFieldToGlobalAut vK hvK w) (localizedCompletionToAlgHom_equivariant vK hvK w))
    exact h.trans hx

end UnitDistance.ArithmeticProP
