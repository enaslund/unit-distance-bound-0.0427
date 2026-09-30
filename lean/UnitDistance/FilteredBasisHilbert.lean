module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Algebra.Polynomial.BigOperators

@[expose] public section
set_option backward.privateInPublic true


/-!
# Hilbert polynomials of actual weighted basis filtrations

The coefficients are dimensions of successive subspaces, and hence of the
actual successive quotient spaces. Counting basis vectors derives their
weight polynomial; no Hilbert value is an assumption.
-/

noncomputable section
open scoped BigOperators
open Polynomial
namespace UnitDistance.FilteredBasis
variable (K V J : Type*) [Field K] [AddCommGroup V] [Module K V]
variable [Fintype J] (b : Module.Basis J K V) (w : J → ℕ)

def weightedSubspace (n : ℕ) : Submodule K V :=
  Submodule.span K {a | ∃ j, n ≤ w j ∧ a = b j}

/-- The actual subspace dimension counts precisely the admissible basis
coordinates, since restricting a basis preserves linear independence. -/
theorem finrank_weightedSubspace (n : ℕ) :
    Module.finrank K (weightedSubspace K V J b w n) =
      (Finset.univ.filter (fun j => n ≤ w j)).card := by
  classical
  have he : {a | ∃ j, n ≤ w j ∧ a = b j} =
      Set.range (fun j : {j : J // n ≤ w j} => b j.val) := by
    ext a
    constructor
    · rintro ⟨j,hj,rfl⟩; exact ⟨⟨j,hj⟩,rfl⟩
    · rintro ⟨j,rfl⟩; exact ⟨j.val,j.property,rfl⟩
  have hi : LinearIndependent K (fun j : {j : J // n ≤ w j} => b j.val) :=
    b.linearIndependent.comp _ Subtype.val_injective
  rw [weightedSubspace,he,finrank_span_eq_card hi]
  exact Fintype.card_subtype _

/-- Taking the difference of the two actual dimensions counts the basis
coordinates of exactly one weight. -/
theorem finrank_weightedSubspace_sub (n : ℕ) :
    Module.finrank K (weightedSubspace K V J b w n) -
      Module.finrank K (weightedSubspace K V J b w (n+1)) =
      (Finset.univ.filter (fun j => w j = n)).card := by
  classical
  rw [finrank_weightedSubspace,finrank_weightedSubspace]
  have he := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun j : J => n ≤ w j)) (fun j => w j = n)
  have h₁ : (Finset.univ.filter (fun j : J => n ≤ w j)).filter (fun j => w j = n) =
      Finset.univ.filter (fun j => w j = n) := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    omega
  have h₂ : (Finset.univ.filter (fun j : J => n ≤ w j)).filter (fun j => ¬ w j = n) =
      Finset.univ.filter (fun j => n+1 ≤ w j) := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    omega
  rw [h₁,h₂] at he
  omega

/-- The independent actual dimension formula equals the weight sum of
the basis, for every cutoff above all its weights. -/
theorem hilbert_eq_weight_sum (N : ℕ) (hN : ∀ j, w j < N) :
    (∑ n ∈ Finset.range N, Polynomial.monomial n
      (Module.finrank K (weightedSubspace K V J b w n) -
        Module.finrank K (weightedSubspace K V J b w (n+1)))) =
      ∑ j, (Polynomial.monomial (w j) 1 : ℕ[X]) := by
  classical
  simp_rw [finrank_weightedSubspace_sub,Finset.card_eq_sum_ones,map_sum,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single (w j)]
  · simp
  · intro n _ hn
    simp [Ne.symm hn]
  · intro hj
    exact (hj (Finset.mem_range.mpr (hN j))).elim

variable (T : Type*) [Fintype T] (u : T → ℕ)

/-- Additive weights in an actual product basis multiply their ordinary
weight polynomials. -/
theorem weight_sum_prod :
    (∑ p : T × J, (Polynomial.monomial (u p.1+w p.2) 1 : ℕ[X])) =
      (∑ t, (Polynomial.monomial (u t) 1 : ℕ[X])) *
        (∑ j, (Polynomial.monomial (w j) 1 : ℕ[X])) := by
  rw [Fintype.sum_prod_type,Finset.sum_mul]
  simp only [Finset.mul_sum,
    Polynomial.monomial_mul_monomial,one_mul]

end UnitDistance.FilteredBasis
