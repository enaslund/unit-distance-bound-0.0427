module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.LinearAlgebra.Dimension.Finrank

@[expose] public section
set_option backward.privateInPublic true


/-! Explicit transport between the unique rational algebra structures. -/
noncomputable section
namespace UnitDistance.RationalGalois
variable (K : Type*) [Field K]

def autEquiv (A B : Algebra ℚ K) :
    @AlgEquiv ℚ K K _ _ _ A A ≃* @AlgEquiv ℚ K K _ _ _ B B := by
  have hAB : A = B := Subsingleton.elim _ _
  cases hAB
  exact MulEquiv.refl _

@[simp] theorem autEquiv_apply (A B : Algebra ℚ K)
    (σ : @AlgEquiv ℚ K K _ _ _ A A) (x : K) :
    autEquiv K A B σ x = σ x := by
  have hAB : A = B := Subsingleton.elim _ _
  cases hAB
  rfl

theorem finrank_eq (A B : Algebra ℚ K) :
    @Module.finrank ℚ K _ _ (@Algebra.toModule ℚ K _ _ A) =
      @Module.finrank ℚ K _ _ (@Algebra.toModule ℚ K _ _ B) := by
  have hAB : A = B := Subsingleton.elim _ _
  cases hAB
  rfl

theorem isGalois (A B : Algebra ℚ K) (h : @IsGalois ℚ _ K _ A) :
    @IsGalois ℚ _ K _ B := by
  have hAB : A = B := Subsingleton.elim _ _
  cases hAB
  exact h

end UnitDistance.RationalGalois
