module

public import UnitDistance.FilteredHilbert
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Pi

@[expose] public section
set_option backward.privateInPublic true


/-!
# Hilbert values of actual shifted coordinate blocks

The finite product subspace has dimension equal to the sum of its actual
coordinate dimensions. Consequently a decomposition into shifted copies of
an actual filtration multiplies its Hilbert value by the genuine shift sum.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.FilteredHilbert
variable (K V : Type*) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {T : Type*} [Fintype T]

/-- The actual product subspace of a finite family of coordinate subspaces. -/
def piSpace (F : T → Submodule K V) : Submodule K (T → V) :=
  Submodule.pi Set.univ F

@[simp] theorem mem_piSpace (F : T → Submodule K V) (a : T → V) :
    a ∈ piSpace K V F ↔ ∀ t, a t ∈ F t := by simp [piSpace,Submodule.mem_pi]

/-- Actual vectors in the product subspace are equivalent to tuples of
actual vectors in the coordinate subspaces. -/
def piSpaceEquiv (F : T → Submodule K V) : piSpace K V F ≃ₗ[K] (t : T) → F t where
  toFun a t := ⟨a.1 t,(mem_piSpace K V F a.1).mp a.2 t⟩
  invFun a := ⟨fun t => a t,(mem_piSpace K V F _).mpr (fun t => (a t).2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_piSpace (F : T → Submodule K V) :
    Module.finrank K ↥(piSpace K V F) = ∑ t, Module.finrank K ↥(F t) := by
  rw [(piSpaceEquiv K V F).finrank_eq,Module.finrank_pi_fintype]

/-- Finite actual product filtrations have additive Hilbert values. -/
theorem value_piSpace (F : T → ℕ → Submodule K V) (N : ℕ) (x : ℝ) :
    value K (T → V) (fun n => piSpace K V (fun t => F t n)) N x =
      ∑ t, value K V (F t) N x := by
  unfold value
  simp only [finrank_piSpace,Nat.cast_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  rw [← Finset.sum_sub_distrib,Finset.sum_mul]

/-- Linear coordinate changes preserve all actual filtration dimensions. -/
theorem value_map_equiv {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (e : V ≃ₗ[K] W) (F : ℕ → Submodule K V) (N : ℕ) (x : ℝ) :
    value K W (fun n => (F n).map e.toLinearMap) N x = value K V F N x := by
  unfold value
  simp only [LinearEquiv.finrank_map_eq]

/-- The actual shifted product has the expected shift factor, at every
cutoff beyond all shifted termination bounds. -/
theorem value_shifted_piSpace (F : ℕ → Submodule K V) (w : T → ℕ)
    (N M : ℕ) (hzero : ∀ n, N ≤ n → F n = ⊥)
    (hM : ∀ t, N+w t ≤ M) (x : ℝ) :
    value K (T → V) (fun n => piSpace K V (fun t => F (n-w t))) M x =
      (∑ t, x^(w t)) * value K V F N x := by
  rw [value_piSpace,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t _
  have he : M = (M-w t)+w t := by have := hM t; omega
  conv_lhs => rw [he]
  rw [value_shift_add,value_extend_of_le K V F N (M-w t) (by have := hM t; omega) hzero]

end UnitDistance.FilteredHilbert
