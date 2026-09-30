/-
Retyped from `UnitDistance/MaximalProPOutside.lean` (adapted from Naganori
Yamaguchi's SawinTotallyRealTowers, commit 3a455e1aa9140dbbe7b7d68f508392a69c86d0f4,
Apache-2.0): ℚ is replaced by an arbitrary number field `F`.
-/
module

public import UnitDistance.Sqrt241.ProP.FinitePExtension
public import UnitDistance.Sqrt241.ProP.FinitePExtensionSupport
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.Galois.Profinite

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# The maximal compositum with prescribed ramification support over `F`

The field is formed from the concrete directed family of finite layers.
Galoisness follows from the corresponding properties of the finite layers.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace UnitDistance.Sqrt241.ProP

open ClassFieldTower.Sawin

variable (F : Type) [Field F] [NumberField F]

/-- The compositum of all admissible finite p-extensions of `F` inside
its fixed algebraic closure. -/
def maximalProPOutside (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 F))) :
    IntermediateField F (AlgebraicClosure F) :=
  ⨆ E : FinitePExtension F p T, E.val.toIntermediateField

variable {F} in
/-- Every admissible finite layer is contained in the maximal compositum. -/
theorem le_maximalProPOutside {p : ℕ}
    {T : Set (HeightOneSpectrum (𝓞 F))}
    (E : FinitePExtension F p T) :
    E.val.toIntermediateField ≤ maximalProPOutside F p T :=
  le_iSup (fun E' : FinitePExtension F p T ↦ E'.val.toIntermediateField) E

/-- The constructed maximal compositum is Galois over `F`. -/
theorem maximalProPOutside_isGalois (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 F))) :
    IsGalois F (maximalProPOutside F p T) := by
  change IsGalois F
    ((⨆ E : FinitePExtension F p T, E.val.toIntermediateField) :
      IntermediateField F (AlgebraicClosure F))
  exact
    { to_isSeparable := IntermediateField.isSeparable_iSup F (AlgebraicClosure F)
        (h := fun E : FinitePExtension F p T ↦ E.val.isGalois.to_isSeparable)
      to_normal := IntermediateField.normal_iSup F (AlgebraicClosure F)
        (fun E : FinitePExtension F p T ↦ E.val.toIntermediateField)
        (h := fun E : FinitePExtension F p T ↦ E.val.isGalois.to_normal) }

instance maximalProPOutside_isGalois_inst (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 F))) :
    IsGalois F (maximalProPOutside F p T) :=
  maximalProPOutside_isGalois F p T

/-- The Krull topology on the Galois group of the maximal compositum is
Hausdorff (registered as an instance: the generic search is slow for `F ≠ ℚ`). -/
instance maximalProPOutside_galoisGroup_t2Space (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 F))) :
    T2Space (maximalProPOutside F p T ≃ₐ[F] maximalProPOutside F p T) :=
  krullTopology_t2

instance maximalProPOutside_galoisGroup_compactSpace (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 F))) :
    CompactSpace (maximalProPOutside F p T ≃ₐ[F] maximalProPOutside F p T) :=
  inferInstance

/-- Local compactness, registered for the same reason as `T2Space`. -/
instance maximalProPOutside_galoisGroup_locallyCompactSpace (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 F))) :
    LocallyCompactSpace (maximalProPOutside F p T ≃ₐ[F] maximalProPOutside F p T) :=
  have : R1Space (maximalProPOutside F p T ≃ₐ[F] maximalProPOutside F p T) :=
    T2Space.r1Space
  have : WeaklyLocallyCompactSpace
      (maximalProPOutside F p T ≃ₐ[F] maximalProPOutside F p T) :=
    ⟨fun _ => ⟨Set.univ, isCompact_univ, Filter.univ_mem⟩⟩
  WeaklyLocallyCompactSpace.locallyCompactSpace

/-- A finite Galois intermediate field lies in the maximal compositum
exactly when it satisfies the arithmetic conditions. -/
theorem isAdmissibleFiniteLayer_iff_le_maximalProPOutside
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 F)))
    (E : FiniteGaloisIntermediateField F (AlgebraicClosure F)) :
    IsAdmissibleFiniteLayer F p T E ↔
      E.toIntermediateField ≤ maximalProPOutside F p T := by
  constructor
  · intro hE
    exact le_maximalProPOutside ⟨E, hE⟩
  · intro hE
    obtain ⟨C, hEC⟩ := finiteDimensional_le_iSup_pExtension_exists_extension
      F p T E.toIntermediateField hE
    exact IsAdmissibleFiniteLayer.of_le hEC C.property

end UnitDistance.Sqrt241.ProP
