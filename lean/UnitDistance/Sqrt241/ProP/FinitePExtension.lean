/-
Retyped from `UnitDistance/FinitePExtension.lean` (itself adapted from Naganori
Yamaguchi's SawinTotallyRealTowers, commit 3a455e1aa9140dbbe7b7d68f508392a69c86d0f4,
Apache-2.0): the base field ℚ is replaced by an arbitrary number field `F`
and `AlgebraicClosure ℚ` by `AlgebraicClosure F`. The proofs are unchanged.
-/
module

public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.GaloisPCompositum
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.RamificationSupportCompositum
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Finite layers with prescribed finite ramification over a number field

We select actual finite Galois intermediate fields of the fixed algebraic
closure of a number field `F`. The base field is a member and binary composita
remain in the family. No condition is imposed at the infinite places.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace UnitDistance.Sqrt241.ProP

open ClassFieldTower.Sawin

variable (F : Type) [Field F] [NumberField F]

local instance finiteGaloisNumberField
    (E : FiniteGaloisIntermediateField F (AlgebraicClosure F)) : NumberField E :=
  NumberField.of_module_finite F E

/-- The finite layers permitted in the pro-p tower over `F`: finite Galois
p-extensions inside `AlgebraicClosure F`, unramified at every finite place
outside `T`. -/
def IsAdmissibleFiniteLayer (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 F)))
    (E : FiniteGaloisIntermediateField F (AlgebraicClosure F)) : Prop :=
  IsPGroup p (E ≃ₐ[F] E) ∧
    IsUnramifiedAtFinitePlacesOutside F E T

/-- The bottom layer satisfies the arithmetic conditions for every prime
parameter and every permitted support. -/
theorem isAdmissibleFiniteLayer_bot (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 F))) :
    IsAdmissibleFiniteLayer F p T ⊥ := by
  let : IsGalois F (⊥ : FiniteGaloisIntermediateField F (AlgebraicClosure F)).toIntermediateField :=
    (⊥ : FiniteGaloisIntermediateField F (AlgebraicClosure F)).isGalois
  refine ⟨?_, ?_⟩
  · apply IsPGroup.of_card (n := 0)
    rw [IsGalois.card_aut_eq_finrank F
      (⊥ : FiniteGaloisIntermediateField F (AlgebraicClosure F))]
    change Module.finrank F (⊥ : IntermediateField F (AlgebraicClosure F)) = p ^ 0
    rw [IntermediateField.finrank_bot, pow_zero]
  · exact IsUnramifiedAtFinitePlacesOutside.congrTop
      (M := (⊥ : FiniteGaloisIntermediateField F (AlgebraicClosure F)))
      (IntermediateField.botEquiv F (AlgebraicClosure F)).symm
      (IsUnramifiedAtFinitePlacesOutside.refl F T)

variable {F}

/-- Binary composita preserve both finite-layer conditions. -/
theorem IsAdmissibleFiniteLayer.sup {p : ℕ}
    {T : Set (HeightOneSpectrum (𝓞 F))}
    {E E' : FiniteGaloisIntermediateField F (AlgebraicClosure F)}
    (hE : IsAdmissibleFiniteLayer F p T E)
    (hE' : IsAdmissibleFiniteLayer F p T E') :
    IsAdmissibleFiniteLayer F p T (E ⊔ E') := by
  let : Algebra.IsAlgebraic F (AlgebraicClosure F) := AlgebraicClosure.isAlgebraic F
  exact ⟨isPGroup_galois_sup E.toIntermediateField E'.toIntermediateField hE.1 hE'.1,
    IsUnramifiedAtFinitePlacesOutside.sup
      E.toIntermediateField E'.toIntermediateField T hE.2 hE'.2⟩

/-- A finite Galois subextension of an admissible layer remains admissible. -/
theorem IsAdmissibleFiniteLayer.of_le {p : ℕ}
    {T : Set (HeightOneSpectrum (𝓞 F))}
    {E E' : FiniteGaloisIntermediateField F (AlgebraicClosure F)}
    (hEE' : E ≤ E') (hE' : IsAdmissibleFiniteLayer F p T E') :
    IsAdmissibleFiniteLayer F p T E := by
  let : Algebra E E' :=
    (IntermediateField.inclusion hEE').toRingHom.toAlgebra
  let : IsScalarTower F E E' := IsScalarTower.of_algebraMap_eq' rfl
  let : Normal F E.toIntermediateField := E.isGalois.to_normal
  let : Normal F E'.toIntermediateField := E'.isGalois.to_normal
  refine ⟨?_, IsUnramifiedAtFinitePlacesOutside.bot T hE'.2⟩
  · exact hE'.1.of_surjective (AlgEquiv.restrictNormalHom E)
      (AlgEquiv.restrictNormalHom_surjective E')

variable (F)

/-- Actual admissible finite layers over `F`. -/
def FinitePExtension (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 F))) : Type :=
  {E : FiniteGaloisIntermediateField F (AlgebraicClosure F) //
    IsAdmissibleFiniteLayer F p T E}

namespace FinitePExtension

/-- The bottom layer of the directed family. -/
def bot (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 F))) :
    FinitePExtension F p T :=
  ⟨⊥, isAdmissibleFiniteLayer_bot F p T⟩

variable {F}

/-- The concrete compositum of two admissible finite layers. -/
def sup {p : ℕ} {T : Set (HeightOneSpectrum (𝓞 F))}
    (E E' : FinitePExtension F p T) : FinitePExtension F p T :=
  ⟨E.val ⊔ E'.val, E.property.sup E'.property⟩

variable (F)

/-- Every pair of finite layers is contained in their admissible compositum. -/
theorem directed (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 F))) :
    Directed (· ≤ ·)
      (fun E : FinitePExtension F p T ↦ E.val.toIntermediateField) := by
  intro E E'
  exact ⟨sup E E', le_sup_left, le_sup_right⟩

end FinitePExtension

end UnitDistance.Sqrt241.ProP
