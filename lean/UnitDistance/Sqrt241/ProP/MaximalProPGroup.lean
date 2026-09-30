/-
Retyped from `UnitDistance/MaximalProPGroup.lean` (adapted from Naganori
Yamaguchi's SawinTotallyRealTowers, commit 3a455e1aa9140dbbe7b7d68f508392a69c86d0f4,
Apache-2.0): ℚ is replaced by an arbitrary number field `F`.
-/
module

public import UnitDistance.Sqrt241.ProP.FinitePExtensionSupport
public import UnitDistance.Sqrt241.ProP.MaximalProPOutside
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.ProC.InverseLimits.Predicates
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.Profinite.OpenSubgroups
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.Galois.Profinite

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# The Galois group of the maximal pro-p compositum over `F`

Every finite normal subextension of the constructed compositum is contained
in an admissible finite layer, so its Galois group is a p-group. Applying this
to fixed fields of open normal subgroups gives a basis of open normal
subgroups with finite p-group quotients.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace UnitDistance.Sqrt241.ProP

open ClassFieldTower.Sawin

variable (F : Type) [Field F] [NumberField F]

/-- A finite normal subextension of the maximal compositum has a
p-group Galois group, by restriction from one admissible finite layer. -/
theorem isPGroup_galois_of_le_maximalProPOutside
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 F)))
    (L : IntermediateField F (AlgebraicClosure F))
    [FiniteDimensional F L] [Normal F L]
    (hL : L ≤ maximalProPOutside F p T) :
    IsPGroup p (L ≃ₐ[F] L) := by
  obtain ⟨C, hLC⟩ :=
    finiteDimensional_le_iSup_pExtension_exists_extension F p T L hL
  let : Algebra L C.val :=
    RingHom.toAlgebra (IntermediateField.inclusion hLC).toRingHom
  let : IsScalarTower F L C.val := IsScalarTower.of_algebraMap_eq' rfl
  let : Normal F C.val.toIntermediateField := C.val.isGalois.to_normal
  exact C.property.1.of_surjective
    (AlgEquiv.restrictNormalHom L)
    (AlgEquiv.restrictNormalHom_surjective C.val)

/-- The actual Galois group of the maximal compositum has an
open-normal basis whose finite quotients are p-groups. -/
theorem maximalProPOutside_galoisGroup_hasPGroupOpenNormalBasis
    (p : ℕ) [Fact p.Prime] (T : Set (HeightOneSpectrum (𝓞 F))) :
    ProCGroups.ProC.HasPGroupOpenNormalBasis p
      (maximalProPOutside F p T ≃ₐ[F] maximalProPOutside F p T) := by
  let : IsGalois F (maximalProPOutside F p T) :=
    maximalProPOutside_isGalois F p T
  rw [ProCGroups.ProC.HasPGroupOpenNormalBasis]
  apply ProCGroups.ProC.HasOpenNormalBasisInClass.of_allOpenNormalQuotients
  intro U
  refine ⟨inferInstance, ?_⟩
  let Uc : ClosedSubgroup
      (maximalProPOutside F p T ≃ₐ[F] maximalProPOutside F p T) :=
    ⟨(U : Subgroup
      (maximalProPOutside F p T ≃ₐ[F] maximalProPOutside F p T)),
      ProCGroups.openNormalSubgroup_isClosed U⟩
  let hUcNormal : Uc.toSubgroup.Normal := U.isNormal'
  let L : IntermediateField F (maximalProPOutside F p T) :=
    IntermediateField.fixedField Uc.toSubgroup
  have hfix : L.fixingSubgroup = Uc.toSubgroup := by
    dsimp only [L]
    exact InfiniteGalois.fixingSubgroup_fixedField Uc
  let : FiniteDimensional F L :=
    (InfiniteGalois.isOpen_iff_finite L).mp (by
      rw [hfix]
      exact U.toOpenSubgroup.isOpen)
  let hLNormal : Normal F L :=
    ((InfiniteGalois.normal_iff_isGalois L).mp (by
      rw [hfix]
      exact hUcNormal)).to_normal
  have hL : IsPGroup p (L ≃ₐ[F] L) := by
    let : FiniteDimensional F (IntermediateField.lift L) :=
      (IntermediateField.liftAlgEquiv L).toLinearEquiv.finiteDimensional
    let : Normal F (IntermediateField.lift L) :=
      Normal.of_algEquiv (h := hLNormal) (IntermediateField.liftAlgEquiv L)
    have hLift : IsPGroup p
        (IntermediateField.lift L ≃ₐ[F] IntermediateField.lift L) :=
      isPGroup_galois_of_le_maximalProPOutside F p T
        (IntermediateField.lift L) (IntermediateField.lift_le L)
    exact hLift.of_equiv
      (AlgEquiv.autCongr (IntermediateField.liftAlgEquiv L)).symm
  let e :
      ((maximalProPOutside F p T ≃ₐ[F] maximalProPOutside F p T) ⧸
        Uc.toSubgroup) ≃* (L ≃ₐ[F] L) :=
    InfiniteGalois.normalAutEquivQuotient
      (k := F) (K := maximalProPOutside F p T) Uc
  have hquot : IsPGroup p
      ((maximalProPOutside F p T ≃ₐ[F] maximalProPOutside F p T) ⧸
        Uc.toSubgroup) := hL.of_equiv e.symm
  simpa only [Uc] using hquot

end UnitDistance.Sqrt241.ProP
