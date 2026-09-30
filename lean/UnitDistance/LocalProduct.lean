module

public import UnitDistance.LocalShells

@[expose] public section
set_option backward.privateInPublic true


/-! # Factorization for product shell weights -/

noncomputable section
open scoped BigOperators

namespace UnitDistance.Local

def shellSquareMass (Q : ℝ) (I : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ i ∈ I, shellMass Q i * a i ^ 2

def shellInteraction (Q : ℝ) (I : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ i ∈ I, ∑ r ∈ I, a i * shellD Q i r * a r

def shellLpMass (Q p : ℝ) (I : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ i ∈ I, shellMass Q i * a i ^ p

theorem sum_four_separated (I J : Finset ℕ) (f g : ℕ → ℕ → ℝ) :
    (∑ i ∈ I, ∑ j ∈ J, ∑ r ∈ I, ∑ t ∈ J, f i r * g j t) =
      (∑ i ∈ I, ∑ r ∈ I, f i r) * (∑ j ∈ J, ∑ t ∈ J, g j t) := by
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.sum_mul_sum]

theorem sum_diagonal (I : Finset ℕ) (f : ℕ → ℝ) :
    (∑ i ∈ I, ∑ r ∈ I, if i = r then f i else 0) = ∑ i ∈ I, f i := by
  classical
  apply Finset.sum_congr rfl
  intro i hi
  simp [hi]

theorem product_kernel_summand (Q : ℝ) (k i j r t : ℕ) (a b : ℕ → ℝ) :
    (a i * b j) * shellKernel Q k i j r t * (a r * b t) =
      (((k : ℝ) + 1) * (if i = r then shellMass Q i * a i ^ 2 else 0)) *
        (if j = t then shellMass Q j * b j ^ 2 else 0) +
      (a i * shellD Q i r * a r) *
        (if j = t then shellMass Q j * b j ^ 2 else 0) +
      (if i = r then shellMass Q i * a i ^ 2 else 0) *
        (b j * shellD Q j t * b t) := by
  classical
  unfold shellKernel
  split_ifs <;> simp_all <;> ring

/-- Exact factorization of the full shell quadratic form for `wᵢⱼ = aᵢ bⱼ`. -/
theorem product_shell_energy (Q : ℝ) (k : ℕ) (I J : Finset ℕ) (a b : ℕ → ℝ) :
    (∑ ij ∈ I ×ˢ J, ∑ rt ∈ I ×ˢ J,
      (a ij.1 * b ij.2) * shellKernel Q k ij.1 ij.2 rt.1 rt.2 * (a rt.1 * b rt.2)) =
      ((k : ℝ) + 1) * shellSquareMass Q I a * shellSquareMass Q J b +
        shellInteraction Q I a * shellSquareMass Q J b +
        shellSquareMass Q I a * shellInteraction Q J b := by
  classical
  simp_rw [Finset.sum_product, product_kernel_summand, Finset.sum_add_distrib]
  rw [sum_four_separated, sum_four_separated, sum_four_separated]
  simp_rw [← Finset.mul_sum]
  simp_rw [sum_diagonal]
  simp only [shellSquareMass, shellInteraction]

/-- The product formula for the weighted moment, using exact real powers. -/
theorem product_shell_moment (Q p : ℝ) (I J : Finset ℕ) (a b : ℕ → ℝ)
    (ha : ∀ i ∈ I, 0 ≤ a i) (hb : ∀ j ∈ J, 0 ≤ b j) :
    (∑ ij ∈ I ×ˢ J, shellMass Q ij.1 * shellMass Q ij.2 * (a ij.1 * b ij.2) ^ p) =
      shellLpMass Q p I a * shellLpMass Q p J b := by
  rw [Finset.sum_product, shellLpMass, shellLpMass, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [Real.mul_rpow (ha i hi) (hb j hj)]
  ring

/-- Symmetric product profiles need only one coefficient vector. -/
theorem symmetric_product_shell_energy (Q : ℝ) (k : ℕ) (I : Finset ℕ) (a : ℕ → ℝ) :
    (∑ ij ∈ I ×ˢ I, ∑ rt ∈ I ×ˢ I,
      (a ij.1 * a ij.2) * shellKernel Q k ij.1 ij.2 rt.1 rt.2 * (a rt.1 * a rt.2)) =
      ((k : ℝ) + 1) * shellSquareMass Q I a ^ 2 +
        2 * shellSquareMass Q I a * shellInteraction Q I a := by
  rw [product_shell_energy]
  ring

end UnitDistance.Local
