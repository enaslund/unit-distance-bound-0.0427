module

public import UnitDistance.ActualLocalTensorH2
public import UnitDistance.LocalGaloisTowerRestriction
public import UnitDistance.FiniteLocalTowerEmbedding
public import UnitDistance.FieldUnitsH2LocalInflation
public import UnitDistance.TensorH2CoefficientChange
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.Relative.FinitePlaceTensorNorm

@[expose] public section
set_option backward.privateInPublic true


/-! Actual local zero detection for inflation in a finite Galois tower.
Both finite global extensions may be nonabelian. -/
noncomputable section
open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField TensorProduct
namespace UnitDistance.ArithmeticProP
open LocalClassFieldTheory AlgebraicNumberTheory.Valuations HilbertRamification
open ClassFieldTower.Cohomology

variable (K F L : Type) [Field K] [NumberField K] [Field F] [NumberField F]
variable [Field L] [NumberField L]
variable [Algebra K F] [Algebra F L] [Algebra K L] [IsScalarTower K F L]
variable [FiniteDimensional K F] [FiniteDimensional K L]
variable [IsGalois K F] [IsGalois K L]

set_option maxHeartbeats 300000 in
set_option backward.isDefEq.respectTransparency false in
/-- Actual inflation preserves and reflects vanishing at every finite tensor block. -/
theorem finiteFieldUnitsTensor_inflation_eq_zero_iff
    (v : HeightOneSpectrum (𝓞 K))
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K F) 2) :
    (fieldUnitsTensorH2 K L (v.adicCompletion K)).hom
      ((finiteGaloisTowerUnitsH2Inflation K F L).hom x) = 0 ↔
    (fieldUnitsTensorH2 K F (v.adicCompletion K)).hom x = 0 := by
  let vK := HeightOneSpectrum.adicAbv K v
  have hvK : vK.IsNontrivial := RayClass.adicAbv_isNontrivial v
  let wL := chosenFinitePlaceExtension (L := L) v
  let wF := restrictFinitePlaceExtension (K := K) (L := L) (E := F) v wL
  let A := vK.Completion
  let B := LocalizedCompletion vK wF
  let C := LocalizedCompletion vK wL
  letI : Algebra A B := localizedCompletionBaseAlgebra vK wF
  letI : Algebra A C := localizedCompletionBaseAlgebra vK wL
  letI : Algebra K B := localizedCompletionGlobalAlgebra vK wF
  letI : Algebra K C := localizedCompletionGlobalAlgebra vK wL
  letI : IsScalarTower K A B := localizedCompletionIsScalarTower vK wF
  letI : IsScalarTower K A C := localizedCompletionIsScalarTower vK wL
  let e : B →ₐ[A] C := finitePlaceRestrictedLocalizedCompletionAlgHom
    (K := K) (L := L) (E := F) v wL
  letI : Algebra B C := e.toRingHom.toAlgebra
  letI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro a
    exact (e.commutes a).symm)
  letI : FiniteDimensional A B := localizedCompletionFiniteDimensional vK hvK wF
  letI hGB : IsGalois A B := localizedCompletionIsGalois vK wF
  letI : Normal A B := hGB.to_normal
  letI : FiniteDimensional A C := localizedCompletionFiniteDimensional vK hvK wL
  letI : IsGalois A C := localizedCompletionIsGalois vK wL
  let f : F →ₐ[K] B := localizedCompletionToAlgHom vK wF
  let l : L →ₐ[K] C := localizedCompletionToAlgHom vK wL
  let rF : Gal(B/A) →* Gal(F/K) := localFieldToGlobalAut vK hvK wF
  let rL : Gal(C/A) →* Gal(L/K) := localFieldToGlobalAut vK hvK wL
  have hf : ∀ σ z, f (rF σ z) = σ (f z) :=
    localizedCompletionToAlgHom_equivariant vK hvK wF
  have hl : ∀ σ z, l (rL σ z) = σ (l z) :=
    localizedCompletionToAlgHom_equivariant vK hvK wL
  have hfield : ∀ z : F, algebraMap B C (f z) = l (algebraMap F L z) :=
    finitePlaceRestrictedLocalizedCompletionAlgHom_toAlgebraicLocalization
      (K := K) (L := L) (E := F) v wL
  have hgroup : (AlgEquiv.restrictNormalHom F).comp rL =
      rF.comp (AlgEquiv.restrictNormalHom (F := A) (K₁ := C) B) := by
    ext σ z
    have h := localizationAut_restrict_of_commutes_galois
      (K := K) (L := L) (E := F) vK hvK wF wL e hfield σ
    exact congrArg (fun τ : Gal(F/K) => τ z) h
  constructor
  · intro hx
    have htop : (fieldUnitsTensorH2 K L A).hom
        ((finiteGaloisTowerUnitsH2Inflation K F L).hom x) = 0 :=
      (fieldUnitsTensorH2_eq_zero_iff_coefficients K L A (v.adicCompletion K)
        (finitePlaceCompletionAlgEquiv v) _).mpr hx
    have htopLocal := (fieldUnitsTensorH2_eq_zero_iff_localField vK hvK wL _).mp htop
    have hbottomLocal := fieldUnitsEvaluation_eq_zero_of_inflation_eq_zero
      K F L A B C f l rF rL hf hl hfield hgroup x htopLocal
    have hbottom : (fieldUnitsTensorH2 K F A).hom x = 0 :=
      (fieldUnitsTensorH2_eq_zero_iff_localField vK hvK wF x).mpr hbottomLocal
    exact (fieldUnitsTensorH2_eq_zero_iff_coefficients K F A (v.adicCompletion K)
      (finitePlaceCompletionAlgEquiv v) x).mp hbottom
  · intro hx
    have hbottom : (fieldUnitsTensorH2 K F A).hom x = 0 :=
      (fieldUnitsTensorH2_eq_zero_iff_coefficients K F A (v.adicCompletion K)
        (finitePlaceCompletionAlgEquiv v) x).mpr hx
    have hbottomLocal := (fieldUnitsTensorH2_eq_zero_iff_localField vK hvK wF x).mp hbottom
    have hcomp := congrArg (fun m => m.hom x)
      (fieldUnitsH2Inflation_evaluation K F L A B C f l rF rL hf hl hfield hgroup)
    change (groupCohomology.map rL (fieldUnitsEvaluationRepHom K L A C l rL hl) 2).hom
        ((finiteGaloisTowerUnitsH2Inflation K F L).hom x) =
      (finiteGaloisTowerUnitsH2Inflation A B C).hom
        ((groupCohomology.map rF (fieldUnitsEvaluationRepHom K F A B f rF hf) 2).hom x) at hcomp
    rw [hbottomLocal,map_zero] at hcomp
    have htop := (fieldUnitsTensorH2_eq_zero_iff_localField vK hvK wL _).mpr hcomp
    exact (fieldUnitsTensorH2_eq_zero_iff_coefficients K L A (v.adicCompletion K)
      (finitePlaceCompletionAlgEquiv v) _).mp htop

end UnitDistance.ArithmeticProP
