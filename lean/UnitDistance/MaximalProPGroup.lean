/-
Adapted from Naganori Yamaguchi's SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4 (Apache-2.0).
This new development removes the condition at infinite places; all finite
unramifiedness and actual Galois/p-group conditions are retained.
-/
module

public import UnitDistance.FinitePExtensionSupport
public import UnitDistance.MaximalProPOutside
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.ProC.InverseLimits.Predicates
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.Profinite.OpenSubgroups
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.Galois.Profinite

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# The Galois group of the maximal pro-p compositum

Every finite normal subextension of the constructed compositum is contained
in an admissible finite layer. Restriction therefore makes its Galois group
a quotient of a p-group. Applying this to fixed fields of open normal
subgroups gives a basis of open normal subgroups with finite p-group
quotients. The argument applies to `p = 2` as well as odd primes.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace UnitDistance.ArithmeticProP

open ClassFieldTower.Sawin

/-- A finite normal subextension of the maximal compositum has a
p-group Galois group, by restriction from one admissible finite layer. -/
theorem isPGroup_galois_of_le_maximalProPOutside
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (L : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ L] [Normal ℚ L]
    (hL : L ≤ maximalProPOutside p T) :
    IsPGroup p (L ≃ₐ[ℚ] L) := by
  obtain ⟨C, hLC⟩ :=
    finiteDimensional_le_iSup_pExtension_exists_extension p T L hL
  let : Algebra L C.val :=
    RingHom.toAlgebra (IntermediateField.inclusion hLC).toRingHom
  let : IsScalarTower ℚ L C.val := IsScalarTower.of_algebraMap_eq' rfl
  let : Normal ℚ C.val.toIntermediateField := C.val.isGalois.to_normal
  exact C.property.1.of_surjective
    (AlgEquiv.restrictNormalHom L)
    (AlgEquiv.restrictNormalHom_surjective C.val)

/-- The actual Galois group of the maximal compositum has an
open-normal basis whose finite quotients are p-groups. -/
theorem maximalProPOutside_galoisGroup_hasPGroupOpenNormalBasis
    (p : ℕ) [Fact p.Prime] (T : Set (HeightOneSpectrum (𝓞 ℚ))) :
    ProCGroups.ProC.HasPGroupOpenNormalBasis p
      (maximalProPOutside p T ≃ₐ[ℚ] maximalProPOutside p T) := by
  let : IsGalois ℚ (maximalProPOutside p T) :=
    maximalProPOutside_isGalois p T
  rw [ProCGroups.ProC.HasPGroupOpenNormalBasis]
  apply ProCGroups.ProC.HasOpenNormalBasisInClass.of_allOpenNormalQuotients
  intro U
  refine ⟨inferInstance, ?_⟩
  let Uc : ClosedSubgroup
      (maximalProPOutside p T ≃ₐ[ℚ] maximalProPOutside p T) :=
    ⟨(U : Subgroup
      (maximalProPOutside p T ≃ₐ[ℚ] maximalProPOutside p T)),
      ProCGroups.openNormalSubgroup_isClosed U⟩
  let hUcNormal : Uc.toSubgroup.Normal := U.isNormal'
  let L : IntermediateField ℚ (maximalProPOutside p T) :=
    IntermediateField.fixedField Uc.toSubgroup
  have hfix : L.fixingSubgroup = Uc.toSubgroup := by
    dsimp only [L]
    exact InfiniteGalois.fixingSubgroup_fixedField Uc
  let : FiniteDimensional ℚ L :=
    (InfiniteGalois.isOpen_iff_finite L).mp (by
      rw [hfix]
      exact U.toOpenSubgroup.isOpen)
  let hLNormal : Normal ℚ L :=
    ((InfiniteGalois.normal_iff_isGalois L).mp (by
      rw [hfix]
      exact hUcNormal)).to_normal
  have hL : IsPGroup p (L ≃ₐ[ℚ] L) := by
    let : FiniteDimensional ℚ (IntermediateField.lift L) :=
      (IntermediateField.liftAlgEquiv L).toLinearEquiv.finiteDimensional
    let : Normal ℚ (IntermediateField.lift L) :=
      Normal.of_algEquiv (h := hLNormal) (IntermediateField.liftAlgEquiv L)
    have hLift : IsPGroup p
        (IntermediateField.lift L ≃ₐ[ℚ] IntermediateField.lift L) :=
      isPGroup_galois_of_le_maximalProPOutside p T
        (IntermediateField.lift L) (IntermediateField.lift_le L)
    exact hLift.of_equiv
      (AlgEquiv.autCongr (IntermediateField.liftAlgEquiv L)).symm
  let e :
      ((maximalProPOutside p T ≃ₐ[ℚ] maximalProPOutside p T) ⧸
        Uc.toSubgroup) ≃* (L ≃ₐ[ℚ] L) :=
    InfiniteGalois.normalAutEquivQuotient
      (k := ℚ) (K := maximalProPOutside p T) Uc
  have hquot : IsPGroup p
      ((maximalProPOutside p T ≃ₐ[ℚ] maximalProPOutside p T) ⧸
        Uc.toSubgroup) := hL.of_equiv e.symm
  simpa only [Uc] using hquot

end UnitDistance.ArithmeticProP
