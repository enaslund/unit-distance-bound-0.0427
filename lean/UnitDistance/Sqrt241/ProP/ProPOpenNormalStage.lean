/-
Retyped from `UnitDistance/ProPOpenNormalStage.lean` (adapted from Naganori
Yamaguchi, SawinTotallyRealTowers, commit 3a455e1aa9140dbbe7b7d68f508392a69c86d0f4,
Apache-2.0; source RealProPOpenNormalStage.lean): ℚ is replaced by an arbitrary
number field `F`. The generic `openNormalFiniteGaloisField` declarations are
reused from the ℚ module unchanged.
-/
module

public import UnitDistance.Sqrt241.ProP.MaximalProPOutside
public import UnitDistance.ProPOpenNormalStage
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.Galois.GaloisClosure
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.Profinite.OpenSubgroups

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Finite arithmetic stages of the pro-p compositum over `F`

An open normal subgroup determines an actual finite Galois fixed field.
Lifting it to the chosen algebraic closure gives an admissible finite layer.
The quotient is identified with that layer's Galois group.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace UnitDistance.Sqrt241.ProP

open UnitDistance.ArithmeticProP (openNormalFiniteGaloisField
  openNormalQuotientEquivFiniteGaloisField openNormalQuotientEquivFiniteGaloisField_apply)

variable (F : Type) [Field F] [NumberField F]

local instance compositumGalois
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 F))) :
    IsGalois F (maximalProPOutside F p T) := maximalProPOutside_isGalois F p T

/-- The concrete arithmetic layer attached to an open normal subgroup of the
maximal compositum. Its local conditions follow from containment. -/
def proPOpenNormalStage
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 F)))
    (U : OpenNormalSubgroup
      (maximalProPOutside F p T ≃ₐ[F] maximalProPOutside F p T)) :
    FinitePExtension F p T := by
  let L : FiniteGaloisIntermediateField F (maximalProPOutside F p T) :=
    openNormalFiniteGaloisField F (maximalProPOutside F p T) U
  let e : L.toIntermediateField ≃ₐ[F] IntermediateField.lift L.toIntermediateField :=
    IntermediateField.liftAlgEquiv L.toIntermediateField
  letI : IsGalois F L.toIntermediateField := L.isGalois
  let D : FiniteGaloisIntermediateField F (AlgebraicClosure F) :=
    { toIntermediateField := IntermediateField.lift L.toIntermediateField
      finiteDimensional := e.toLinearEquiv.finiteDimensional
      isGalois := IsGalois.of_algEquiv e }
  exact ⟨D, (isAdmissibleFiniteLayer_iff_le_maximalProPOutside F p T D).mpr
    (IntermediateField.lift_le L.toIntermediateField)⟩

/-- The stage is the lift of the finite fixed field, with no auxiliary choice. -/
theorem proPOpenNormalStage_field
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 F)))
    (U : OpenNormalSubgroup
      (maximalProPOutside F p T ≃ₐ[F] maximalProPOutside F p T)) :
    (proPOpenNormalStage F p T U).val.toIntermediateField =
      IntermediateField.lift
        (IntermediateField.fixedField
          (U : Subgroup
            (maximalProPOutside F p T ≃ₐ[F] maximalProPOutside F p T))) := rfl

/-- The quotient group is the Galois group of the constructed admissible layer. -/
def proPOpenNormalQuotientEquivStage
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 F)))
    (U : OpenNormalSubgroup
      (maximalProPOutside F p T ≃ₐ[F] maximalProPOutside F p T)) :
    ((maximalProPOutside F p T ≃ₐ[F] maximalProPOutside F p T) ⧸
      (U : Subgroup
        (maximalProPOutside F p T ≃ₐ[F] maximalProPOutside F p T))) ≃*
      ((proPOpenNormalStage F p T U).val ≃ₐ[F] (proPOpenNormalStage F p T U).val) := by
  let L : FiniteGaloisIntermediateField F (maximalProPOutside F p T) :=
    openNormalFiniteGaloisField F (maximalProPOutside F p T) U
  exact (openNormalQuotientEquivFiniteGaloisField F (maximalProPOutside F p T) U).trans
    (AlgEquiv.autCongr (IntermediateField.liftAlgEquiv L.toIntermediateField))

/-- The quotient action on the arithmetic stage is the restriction of the
original automorphism, transported through the canonical lift. -/
theorem proPOpenNormalQuotientEquivStage_apply
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 F)))
    (U : OpenNormalSubgroup
      (maximalProPOutside F p T ≃ₐ[F] maximalProPOutside F p T))
    (σ : maximalProPOutside F p T ≃ₐ[F] maximalProPOutside F p T)
    (x : (proPOpenNormalStage F p T U).val) :
    ((proPOpenNormalQuotientEquivStage F p T U
      (QuotientGroup.mk' (U : Subgroup
        (maximalProPOutside F p T ≃ₐ[F] maximalProPOutside F p T)) σ) x :
          (proPOpenNormalStage F p T U).val) : AlgebraicClosure F) =
      (σ ⟨(x : AlgebraicClosure F),
        le_maximalProPOutside (proPOpenNormalStage F p T U) x.property⟩ :
          AlgebraicClosure F) := by
  let L : FiniteGaloisIntermediateField F (maximalProPOutside F p T) :=
    openNormalFiniteGaloisField F (maximalProPOutside F p T) U
  let e : L.toIntermediateField ≃ₐ[F] IntermediateField.lift L.toIntermediateField :=
    IntermediateField.liftAlgEquiv L.toIntermediateField
  change (e ((openNormalQuotientEquivFiniteGaloisField F
    (maximalProPOutside F p T) U σ) (e.symm x)) : AlgebraicClosure F) = _
  have hAction := openNormalQuotientEquivFiniteGaloisField_apply F
    (maximalProPOutside F p T) U σ (e.symm x)
  exact congrArg (fun y : maximalProPOutside F p T ↦ (y : AlgebraicClosure F)) hAction

end UnitDistance.Sqrt241.ProP
