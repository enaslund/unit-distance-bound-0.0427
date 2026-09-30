/-
Adapted from Naganori Yamaguchi's SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4 (Apache-2.0).
This new development removes the condition at infinite places; all finite
unramifiedness and actual Galois/p-group conditions are retained.
-/
module

public import UnitDistance.FinitePExtension
public import UnitDistance.FinitePExtensionSupport
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.FieldTheory.SeparableClosure

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# The maximal compositum with prescribed ramification support

The field is formed from the concrete directed family of finite layers.
Galoisness follows from the corresponding properties of the finite layers. The pro-p property and arithmetic rank estimates are separate
theorems, not inputs to this construction.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace UnitDistance.ArithmeticProP

open ClassFieldTower.Sawin

/-- The compositum of all admissible finite p-extensions of ℚ inside
its fixed algebraic closure. -/
def maximalProPOutside (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ))) :
    IntermediateField ℚ (AlgebraicClosure ℚ) :=
  ⨆ E : FinitePExtension p T, E.val.toIntermediateField

/-- Every admissible finite layer is contained in the maximal compositum. -/
theorem le_maximalProPOutside {p : ℕ}
    {T : Set (HeightOneSpectrum (𝓞 ℚ))}
    (E : FinitePExtension p T) :
    E.val.toIntermediateField ≤ maximalProPOutside p T :=
  le_iSup (fun F : FinitePExtension p T ↦ F.val.toIntermediateField) E

/-- The constructed maximal compositum is Galois over ℚ. -/
theorem maximalProPOutside_isGalois (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 ℚ))) :
    IsGalois ℚ (maximalProPOutside p T) := by
  change IsGalois ℚ
    ((⨆ E : FinitePExtension p T, E.val.toIntermediateField) :
      IntermediateField ℚ (AlgebraicClosure ℚ))
  exact
    { to_isSeparable := IntermediateField.isSeparable_iSup ℚ (AlgebraicClosure ℚ)
        (h := fun E : FinitePExtension p T ↦ E.val.isGalois.to_isSeparable)
      to_normal := IntermediateField.normal_iSup ℚ (AlgebraicClosure ℚ)
        (fun E : FinitePExtension p T ↦ E.val.toIntermediateField)
        (h := fun E : FinitePExtension p T ↦ E.val.isGalois.to_normal) }

/-- A finite Galois intermediate field lies in the maximal compositum
exactly when it satisfies the original arithmetic conditions. Directed
finite support and descent rule out additional inadmissible finite layers. -/
theorem isAdmissibleFiniteLayer_iff_le_maximalProPOutside
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    IsAdmissibleFiniteLayer p T E ↔
      E.toIntermediateField ≤ maximalProPOutside p T := by
  constructor
  · intro hE
    exact le_maximalProPOutside ⟨E, hE⟩
  · intro hE
    obtain ⟨C, hEC⟩ := finiteDimensional_le_iSup_pExtension_exists_extension
      p T E.toIntermediateField hE
    exact IsAdmissibleFiniteLayer.of_le hEC C.property

end UnitDistance.ArithmeticProP
