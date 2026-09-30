/-
Adapted from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Source: SawinTotallyRealTowers/AbsoluteRealProPUnramified.lean.
Modified: retain finite-inertia proof; remove the infinite-place theorem and its imports.
-/
module

public import UnitDistance.AbsoluteProPRestriction
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.FinitePlaceAbsoluteInertiaKernel
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Completion.ExtensionIndex
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.CompositumUnramified
public import Mathlib.FieldTheory.Galois.Basic

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Ramification killed by the maximal pro-p restriction

Absolute inertia outside the allowed support fixes every admissible finite
layer, hence their compositum. No condition is imposed at infinite places.
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace UnitDistance.ArithmeticProP

open ClassFieldTower.Sawin ClassFieldTower.Martinet.Shafarevich AlgebraicNumberTheory.Valuations

private theorem finiteInertia_fixes_layer
    (F : Type) [Field F] [NumberField F]
    (M : FiniteGaloisIntermediateField F (AlgebraicClosure F)) [NumberField M]
    (T : Set (HeightOneSpectrum (𝓞 F)))
    (hM : IsUnramifiedAtFinitePlacesOutside F M T)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ T)
    (σ : finitePlaceAbsoluteInertiaSubgroup F v) :
    (σ.1.1 : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) ∈
      M.toIntermediateField.fixingSubgroup := by
  have : IsGalois F M.toIntermediateField := M.isGalois
  let s : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F := σ.1.1
  let wM := restrictAbsoluteValueExtensionToIntermediate
    (HeightOneSpectrum.adicAbv F v) (finitePlaceAbsoluteValueExtension F v) M.toIntermediateField
  let P := finitePlaceExtensionCentre (K := F) (L := M) v wM
  have hmem : s.restrictNormal M ∈
      HilbertRamification.Dedekind.inertiaGroup P.asIdeal (M ≃ₐ[F] M) :=
    finitePlaceAbsoluteInertia_restrictNormal_mem_finiteInertia F M.toIntermediateField v σ
  have hBelow : finitePlaceBelow (K := F) P = v :=
    finitePlaceBelow_finitePlaceExtensionCentre (K := F) (L := M) v wM
  have hUnramified : Algebra.IsUnramifiedAt (𝓞 F) P.asIdeal := hM P (hBelow ▸ hv)
  have hbot : HilbertRamification.Dedekind.inertiaGroup P.asIdeal (M ≃ₐ[F] M) = ⊥ :=
    HilbertRamification.Dedekind.inertiaGroup_eq_bot_of_isUnramifiedAt
      (K := F) (M := M) P.asIdeal hUnramified
  rw [← IntermediateField.restrictNormalHom_ker M.toIntermediateField, MonoidHom.mem_ker]
  exact Subgroup.mem_bot.mp (hbot ▸ hmem)

/-- The actual maximal restriction kills finite inertia outside the support. -/
theorem absoluteToMaximalProPOutside_inertia (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 ℚ))) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : v ∉ T) (σ : finitePlaceAbsoluteInertiaSubgroup ℚ v) :
    absoluteToMaximalProPOutside p T
      (finitePlaceAbsoluteDecompositionInclusion ℚ v σ.1) = 1 := by
  let s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ := σ.1.1
  have hmax : maximalProPOutside p T ≤ IntermediateField.fixedField (Subgroup.zpowers s) := by
    apply iSup_le
    intro E
    have : NumberField E.val := NumberField.of_module_finite ℚ E.val
    rw [IntermediateField.le_iff_le, Subgroup.zpowers_le]
    exact finiteInertia_fixes_layer ℚ E.val T E.property.2 v hv σ
  have hfix : Subgroup.zpowers s ≤ (maximalProPOutside p T).fixingSubgroup :=
    (IntermediateField.le_iff_le _ _).mp hmax
  change s ∈ (absoluteToMaximalProPOutside p T).toMonoidHom.ker
  rw [absoluteToMaximalProPOutside_ker]
  exact hfix (Subgroup.mem_zpowers s)

end UnitDistance.ArithmeticProP
