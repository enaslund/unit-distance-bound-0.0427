module

public import UnitDistance.TensorEvaluationH2
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.Kummer.FiniteGaloisTowerUnitsH2

@[expose] public section
set_option backward.privateInPublic true


/-! Compatibility of actual field-unit inflation with actual local field
embeddings, and zero detection through local inflation injectivity. -/
noncomputable section
open CategoryTheory
namespace UnitDistance.ArithmeticProP
open ClassFieldTower.Cohomology

variable (K F L A B C : Type)
variable [Field K] [Field F] [Field L] [Algebra K F] [Algebra F L] [Algebra K L]
variable [IsScalarTower K F L] [Normal K F]
variable [Field A] [Algebra K A]
variable [Field B] [Algebra A B] [Algebra K B] [IsScalarTower K A B]
variable [Field C] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [Algebra K C] [IsScalarTower K A C] [Normal A B]
variable (f : F →ₐ[K] B) (l : L →ₐ[K] C)
variable (rF : Gal(B/A) →* Gal(F/K)) (rL : Gal(C/A) →* Gal(L/K))
variable (hf : ∀ σ x, f (rF σ x) = σ (f x))
variable (hl : ∀ σ x, l (rL σ x) = σ (l x))
variable (hfield : ∀ x : F, algebraMap B C (f x) = l (algebraMap F L x))
variable (hgroup : (AlgEquiv.restrictNormalHom F).comp rL =
  rF.comp (AlgEquiv.restrictNormalHom B))

include hfield hgroup

/-- Actual global and local field-unit inflation commute with localization. -/
theorem fieldUnitsH2Inflation_evaluation :
    finiteGaloisTowerUnitsH2Inflation K F L ≫
      groupCohomology.map rL (fieldUnitsEvaluationRepHom K L A C l rL hl) 2 =
    groupCohomology.map rF (fieldUnitsEvaluationRepHom K F A B f rF hf) 2 ≫
      finiteGaloisTowerUnitsH2Inflation A B C := by
  unfold finiteGaloisTowerUnitsH2Inflation
  rw [← groupCohomology.map_comp,← groupCohomology.map_comp]
  apply groupCohomology.map_congr hgroup
  apply LinearMap.ext
  intro z
  apply Units.ext
  exact (hfield ((show Additive Fˣ from z).toMul : F)).symm

/-- A lower-field class is locally zero if its actual inflation is locally
zero in a finite Galois tower of local fields. -/
theorem fieldUnitsEvaluation_eq_zero_of_inflation_eq_zero
    [FiniteDimensional A C] [IsGalois A C]
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K F) 2)
    (hx : (groupCohomology.map rL
        (fieldUnitsEvaluationRepHom K L A C l rL hl) 2).hom
      ((finiteGaloisTowerUnitsH2Inflation K F L).hom x) = 0) :
    (groupCohomology.map rF
      (fieldUnitsEvaluationRepHom K F A B f rF hf) 2).hom x = 0 := by
  apply finiteGaloisTowerUnitsH2Inflation_injective A B C
  rw [map_zero]
  have h := congrArg (fun m => m.hom x)
    (fieldUnitsH2Inflation_evaluation K F L A B C f l rF rL hf hl hfield hgroup)
  exact h.symm.trans hx

end UnitDistance.ArithmeticProP
