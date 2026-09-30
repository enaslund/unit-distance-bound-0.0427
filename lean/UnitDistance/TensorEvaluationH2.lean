module

public import UnitDistance.TensorBaseChangeH2

@[expose] public section
set_option backward.privateInPublic true


/-! Actual evaluation of local tensor H² in a field completion. The kernel
transport uses coefficient maps directly and needs no Shapiro comparison. -/
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace UnitDistance.ArithmeticProP

variable (K L A E : Type) [Field K] [Field L] [Algebra K L]
variable [Field A] [Algebra K A] [Field E] [Algebra A E] [Algebra K E]
variable [IsScalarTower K A E]
variable (f : L →ₐ[K] E)
variable (r : Gal(E/A) →* Gal(L/K))
variable (hr : ∀ σ x, f (r σ x) = σ (f x))

/-- The local tensor algebra evaluates in the actual field extension. -/
def localTensorEvaluation : A ⊗[K] L →ₐ[K] E :=
  Algebra.TensorProduct.lift (IsScalarTower.toAlgHom K A E) f
    (fun _ _ => Commute.all _ _)

@[simp] theorem localTensorEvaluation_tmul (a : A) (x : L) :
    localTensorEvaluation K L A E f (a ⊗ₜ[K] x) = algebraMap A E a*f x := rfl

include hr in
/-- Evaluation intertwines the actual tensor and field automorphisms. -/
theorem localTensorEvaluation_conjugation (σ : Gal(E/A)) (z : A ⊗[K] L) :
    localTensorEvaluation K L A E f
      (scalarTensorConjugation (K := K) (L := L) (A := A) (r σ) z) =
    σ (localTensorEvaluation K L A E f z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [hr,σ.commutes]
  | add x y hx hy => simp [hx,hy]

local instance tensorEvaluationAction : MulDistribMulAction Gal(L/K) (A ⊗[K] L)ˣ :=
  scalarTensorUnitsAction (K := K) (L := L) (A := A)

/-- The actual equivariant tensor-unit evaluation map. -/
def localTensorEvaluationRepHom :
    Rep.res r (Rep.ofMulDistribMulAction Gal(L/K) (A ⊗[K] L)ˣ) ⟶
      Rep.ofAlgebraAutOnUnits A E := by
  apply Rep.ofHom
  refine ⟨(Units.map (localTensorEvaluation K L A E f).toMonoidHom).toAdditive.toIntLinearMap,?_⟩
  intro σ
  apply LinearMap.ext
  intro z
  apply Units.ext
  exact localTensorEvaluation_conjugation K L A E f r hr σ
    ((show Additive (A ⊗[K] L)ˣ from z).toMul : A ⊗[K] L)

/-- The original field units evaluate in the completion with its actual action. -/
def fieldUnitsEvaluationRepHom :
    Rep.res r (Rep.ofAlgebraAutOnUnits K L) ⟶ Rep.ofAlgebraAutOnUnits A E := by
  apply Rep.ofHom
  refine ⟨(Units.map f.toMonoidHom).toAdditive.toIntLinearMap,?_⟩
  intro σ
  apply LinearMap.ext
  intro z
  apply Units.ext
  exact hr σ ((show Additive Lˣ from z).toMul : L)

/-- Evaluating the localized field-unit class agrees with direct localization
in the actual field. -/
theorem fieldUnitsTensorH2_evaluation :
    fieldUnitsTensorH2 K L A ≫
      groupCohomology.map r (localTensorEvaluationRepHom K L A E f r hr) 2 =
    groupCohomology.map r (fieldUnitsEvaluationRepHom K L A E f r hr) 2 := by
  unfold fieldUnitsTensorH2
  rw [← groupCohomology.map_comp]
  apply groupCohomology.map_congr
  · ext σ x
    rfl
  · apply LinearMap.ext
    intro z
    apply Units.ext
    change localTensorEvaluation K L A E f
      (1 ⊗ₜ[K] ((show Additive Lˣ from z).toMul : L)) =
      f ((show Additive Lˣ from z).toMul : L)
    simp

/-- Tensor-local triviality gives a genuine field-local coboundary class. -/
theorem fieldUnitsEvaluation_eq_zero_of_tensor_eq_zero
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2)
    (hx : (fieldUnitsTensorH2 K L A).hom x = 0) :
    (groupCohomology.map r (fieldUnitsEvaluationRepHom K L A E f r hr) 2).hom x = 0 := by
  have h := congrArg (fun m => m.hom x) (fieldUnitsTensorH2_evaluation K L A E f r hr)
  change (groupCohomology.map r (localTensorEvaluationRepHom K L A E f r hr) 2).hom
      ((fieldUnitsTensorH2 K L A).hom x) = _ at h
  rw [hx,map_zero] at h
  exact h.symm

end UnitDistance.ArithmeticProP
