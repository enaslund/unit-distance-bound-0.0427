module

public import UnitDistance.CoinducedH2Transport
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Tensor
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.MultiplicativeInducedShapiro

@[expose] public section
set_option backward.privateInPublic true


/-! Injectivity of actual local tensor evaluation on H², using the explicit
coinduced primitive and the actual tensor decomposition. -/
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace UnitDistance.ArithmeticProP
open LocalClassFieldTheory AlgebraicNumberTheory.Valuations HilbertRamification
open ClassFieldTower.Cohomology CyclicCohomology

variable {K L : Type} [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L] [IsGalois K L]
variable (vK : AbsoluteValue K ℝ) (hvK : vK.IsNontrivial)
variable (w : AbsoluteValueExtension vK L)

local instance : Algebra K w.1.Completion := AbsoluteValue.extensionCompletionAlgebra (K := K) w.1
local instance : Algebra vK.Completion w.1.Completion := AbsoluteValue.completionAlgebra vK w.1 w.2
local instance (w' : AbsoluteValueExtension vK L) : Algebra vK.Completion w'.1.Completion :=
  AbsoluteValue.completionAlgebra vK w'.1 w'.2
/-- Actual decomposition-group action on the chosen local field units. -/
abbrev localDecompositionUnitsRep : Rep ℤ (absoluteValueDecompositionGroup K w.1) :=
  letI := decompositionGroupLocalUnitsAction vK hvK w
  Rep.ofMulDistribMulAction (absoluteValueDecompositionGroup K w.1) (LocalizedCompletion vK w)ˣ
local instance : MulDistribMulAction Gal(L/K) (LocalTensorAlgebra (L := L) vK)ˣ :=
  localTensorUnitsAction vK

/-- The actual local tensor-unit representation is concretely coinduced. -/
def localTensorRepIsoCoind :
    Rep.ofMulDistribMulAction Gal(L/K) (LocalTensorAlgebra (L := L) vK)ˣ ≅
    Rep.coind (absoluteValueDecompositionGroup K w.1).subtype
      (localDecompositionUnitsRep vK hvK w) := by
  letI := decompositionGroupLocalUnitsAction vK hvK w
  let e := localTensorUnitsEquivLocalPlaceBlock vK hvK w
  let e1 : Rep.ofMulDistribMulAction Gal(L/K) (LocalTensorAlgebra (L := L) vK)ˣ ≅
      Rep.ofMulDistribMulAction Gal(L/K) (LocalPlaceBlock vK hvK w) :=
    Rep.mkIso (Representation.Equiv.mk e.toAdditive.toIntLinearEquiv (by
      intro g
      apply LinearMap.ext
      intro x
      exact congrArg Additive.ofMul
        (localTensorUnitsEquivLocalPlaceBlock_smul vK hvK w g x.toMul)))
  exact e1 ≪≫ multiplicativeInducedRepIsoCoind
    (absoluteValueDecompositionGroup K w.1) (LocalizedCompletion vK w)ˣ

/-- Restriction to the actual decomposition group followed by actual tensor
algebra evaluation at the chosen extension of the absolute value. -/
def localTensorDecompositionEvaluationRepHom :
    Rep.res (absoluteValueDecompositionGroup K w.1).subtype
      (Rep.ofMulDistribMulAction Gal(L/K) (LocalTensorAlgebra (L := L) vK)ˣ) ⟶
    localDecompositionUnitsRep vK hvK w := by
  letI := decompositionGroupLocalUnitsAction vK hvK w
  apply Rep.ofHom
  refine ⟨(Units.map (LocalClassFieldTheory.localTensorEvaluation vK hvK w).toMonoidHom).toAdditive.toIntLinearMap,?_⟩
  intro h
  apply LinearMap.ext
  intro x
  apply Units.ext
  change LocalClassFieldTheory.localTensorEvaluation vK hvK w
    (localTensorConjugation vK h.1
      ((show Additive (LocalTensorAlgebra (L := L) vK)ˣ from x).toMul : LocalTensorAlgebra (L := L) vK)) =
    decompositionGroupEquivAlgebraicLocalizationAut vK hvK w h
      (LocalClassFieldTheory.localTensorEvaluation vK hvK w
        ((show Additive (LocalTensorAlgebra (L := L) vK)ˣ from x).toMul : LocalTensorAlgebra (L := L) vK))
  simpa only [mul_one,localTensorConjugation_one] using
    localTensorEvaluation_conjugation_decomposition vK hvK w h 1
      ((show Additive (LocalTensorAlgebra (L := L) vK)ˣ from x).toMul : LocalTensorAlgebra (L := L) vK)

/-- The coinduced-model evaluation is literally the actual tensor evaluation. -/
theorem localTensorRepIsoCoind_evaluation :
    (Rep.resFunctor (absoluteValueDecompositionGroup K w.1).subtype).map
      (localTensorRepIsoCoind vK hvK w).hom ≫
      coindEvaluationRepHom (absoluteValueDecompositionGroup K w.1)
        (localDecompositionUnitsRep vK hvK w) =
    localTensorDecompositionEvaluationRepHom vK hvK w := by
  letI := decompositionGroupLocalUnitsAction vK hvK w
  apply Rep.hom_ext
  ext x
  change Additive.ofMul
    ((localTensorUnitsEquivLocalPlaceBlock vK hvK w
      (show Additive (LocalTensorAlgebra (L := L) vK)ˣ from x).toMul).1 1) = _
  rw [localTensorUnitsEquivLocalPlaceBlock_eq_orbitHom_apply]
  apply Units.ext
  change LocalClassFieldTheory.localTensorEvaluation vK hvK w
    (localTensorConjugation vK 1 _) = _
  rw [localTensorConjugation_one]
  rfl

/-- The actual local tensor evaluation detects all degree-two classes. -/
theorem localTensorDecompositionEvaluationH2_injective :
    Function.Injective
      (groupCohomology.map (absoluteValueDecompositionGroup K w.1).subtype
        (localTensorDecompositionEvaluationRepHom vK hvK w) 2).hom := by
  rw [← localTensorRepIsoCoind_evaluation]
  exact coindModelEvaluationH2_injective _ _ _ (localTensorRepIsoCoind vK hvK w)

/-- The actual restriction from local field automorphisms to global automorphisms. -/
def localFieldToGlobalAut :
    Gal((LocalizedCompletion vK w)/vK.Completion) →* Gal(L/K) :=
  (absoluteValueDecompositionGroup K w.1).subtype.comp
    (decompositionGroupEquivAlgebraicLocalizationAut vK hvK w).symm.toMonoidHom

@[simp] theorem localFieldToGlobalAut_apply (σ : Gal((LocalizedCompletion vK w)/vK.Completion)) :
    localFieldToGlobalAut vK hvK w σ =
      ((decompositionGroupEquivAlgebraicLocalizationAut vK hvK w).symm σ).1 := rfl

/-- The same actual tensor evaluation, expressed in the local field Galois group. -/
def localTensorFieldEvaluationRepHom :
    Rep.res (localFieldToGlobalAut vK hvK w)
      (Rep.ofMulDistribMulAction Gal(L/K) (LocalTensorAlgebra (L := L) vK)ˣ) ⟶
    Rep.ofAlgebraAutOnUnits vK.Completion (LocalizedCompletion vK w) := by
  apply Rep.ofHom
  refine ⟨(Units.map (LocalClassFieldTheory.localTensorEvaluation vK hvK w).toMonoidHom).toAdditive.toIntLinearMap,?_⟩
  intro σ
  apply LinearMap.ext
  intro x
  apply Units.ext
  change LocalClassFieldTheory.localTensorEvaluation vK hvK w
    (localTensorConjugation vK (localFieldToGlobalAut vK hvK w σ)
      ((show Additive (LocalTensorAlgebra (L := L) vK)ˣ from x).toMul : LocalTensorAlgebra (L := L) vK)) =
    σ (LocalClassFieldTheory.localTensorEvaluation vK hvK w
      ((show Additive (LocalTensorAlgebra (L := L) vK)ˣ from x).toMul : LocalTensorAlgebra (L := L) vK))
  rw [localFieldToGlobalAut_apply]
  simpa only [mul_one,localTensorConjugation_one,MulEquiv.apply_symm_apply] using
    localTensorEvaluation_conjugation_decomposition vK hvK w
      ((decompositionGroupEquivAlgebraicLocalizationAut vK hvK w).symm σ) 1
      ((show Additive (LocalTensorAlgebra (L := L) vK)ˣ from x).toMul : LocalTensorAlgebra (L := L) vK)

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency false in
/-- Actual evaluation into the local field-unit H² is injective. -/
theorem localTensorFieldEvaluationH2_injective :
    Function.Injective
      (groupCohomology.map (localFieldToGlobalAut vK hvK w)
        (localTensorFieldEvaluationRepHom vK hvK w) 2).hom := by
  let e := decompositionGroupEquivAlgebraicLocalizationAut vK hvK w
  let j := groupCohomology.mapIso
    (A := Rep.ofAlgebraAutOnUnits vK.Completion (LocalizedCompletion vK w))
    (B := localDecompositionUnitsRep vK hvK w)
    e (LinearEquiv.refl ℤ (Additive (LocalizedCompletion vK w)ˣ))
    (by intro g; ext x; rfl) 2
  have hj : groupCohomology.map (localFieldToGlobalAut vK hvK w)
        (localTensorFieldEvaluationRepHom vK hvK w) 2 =
      groupCohomology.map (absoluteValueDecompositionGroup K w.1).subtype
        (localTensorDecompositionEvaluationRepHom vK hvK w) 2 ≫ j.hom := by
    dsimp only [j,groupCohomology.mapIso]
    rw [← groupCohomology.map_comp]
    apply groupCohomology.map_congr rfl
    apply LinearMap.ext
    intro x
    rfl
  rw [hj]
  exact j.toLinearEquiv.injective.comp
    (localTensorDecompositionEvaluationH2_injective vK hvK w)

end UnitDistance.ArithmeticProP
