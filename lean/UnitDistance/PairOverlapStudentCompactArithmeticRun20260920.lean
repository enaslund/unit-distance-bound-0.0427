module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Finset.Range
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Linarith

@[expose] public section
set_option backward.privateInPublic true


/-! A standalone arithmetic certificate for the finite expression occurring
in the pair-overlap Student constant bound.  It has no analytical imports. -/

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open scoped BigOperators

namespace UnitDistance.Witness.PairOverlapStudentCompactArithmeticRun20260920

def sigma : ℝ := 22920117 / 20000000

def seriesTerm (x : ℝ) (n : ℕ) : ℝ :=
  2 * x ^ 2 /
    ((n + 1 : ℝ) * (n + 1 + x) * (n + 1 + 2 * x))

def numeratorA : ℕ := 2920117
def denominatorB : ℕ := 20000000
def certificateScale : ℕ := 10 ^ 18
def termCount : ℕ := 3500

def termDenominator (k : ℕ) : ℕ :=
  k * (denominatorB * k + numeratorA) *
    (denominatorB * k + 2 * numeratorA)

def termUpperNumerator (k : ℕ) : ℕ :=
  (2 * numeratorA ^ 2 * certificateScale) / termDenominator k + 1

def upperNumeratorSum : ℕ :=
  ∑ n ∈ Finset.range termCount, termUpperNumerator (n + 1)

/-- A generic rational ceiling obtained from natural-number division. -/
theorem nat_ratio_le_div_add_one (A B D : ℕ) (hB : 0 < B) (hD : 0 < D) :
    (A : ℝ) / (B : ℝ) ≤ (((A * D) / B + 1 : ℕ) : ℝ) / (D : ℝ) := by
  have hmod : (A * D) % B < B := Nat.mod_lt _ hB
  have hlt : A * D < ((A * D) / B + 1) * B := by
    calc
      A * D = B * ((A * D) / B) + (A * D) % B := (Nat.div_add_mod _ _).symm
      _ < B * ((A * D) / B) + B := Nat.add_lt_add_left hmod _
      _ = ((A * D) / B + 1) * B := by simp [add_mul, Nat.mul_comm]
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hD' : (0 : ℝ) < D := by exact_mod_cast hD
  apply le_of_lt
  apply (div_lt_div_iff₀ hB' hD').2
  exact_mod_cast hlt

theorem seriesTerm_eq_ratio (n : ℕ) :
    seriesTerm (sigma - 1) n =
      ((2 * numeratorA ^ 2 : ℕ) : ℝ) /
        (termDenominator (n + 1) : ℝ) := by
  unfold seriesTerm sigma termDenominator numeratorA denominatorB
  norm_num
  push_cast
  field_simp <;> (try positivity) <;> ring

theorem seriesTerm_le_upper (n : ℕ) :
    seriesTerm (sigma - 1) n ≤
      (termUpperNumerator (n + 1) : ℝ) / certificateScale := by
  rw [seriesTerm_eq_ratio]
  unfold termUpperNumerator
  exact nat_ratio_le_div_add_one (2 * numeratorA ^ 2)
    (termDenominator (n + 1)) certificateScale
    (by
      unfold termDenominator numeratorA denominatorB
      positivity)
    (by norm_num [certificateScale])

/-- The only 3,500-term computation in the certificate. -/
theorem upperNumeratorSum_eq :
    upperNumeratorSum = 36077197491400761 := by
  decide +kernel

theorem series_sum_le :
    (∑ n ∈ Finset.range termCount, seriesTerm (sigma - 1) n) ≤
      (36077197491400761 : ℝ) / 10 ^ 18 := by
  calc
    (∑ n ∈ Finset.range termCount, seriesTerm (sigma - 1) n) ≤
        ∑ n ∈ Finset.range termCount,
          (termUpperNumerator (n + 1) : ℝ) / certificateScale :=
      Finset.sum_le_sum fun n _ => seriesTerm_le_upper n
    _ = (upperNumeratorSum : ℝ) / certificateScale := by
      rw [← Finset.sum_div, ← Nat.cast_sum]
      rfl
    _ = (36077197491400761 : ℝ) / 10 ^ 18 := by
      rw [upperNumeratorSum_eq]
      norm_num [certificateScale]

/-- Literal rational lower bound for the finite expression consumed by the
analytical remainder theorem. -/
theorem finite_expression_lower :
    (1511896398840 : ℝ) / 10 ^ 12 ≤
      2 / (2 * sigma - 1) -
        ((∑ n ∈ Finset.range termCount, seriesTerm (sigma - 1) n) +
          (sigma - 1) ^ 2 / termCount ^ 2) := by
  calc
    (1511896398840 : ℝ) / 10 ^ 12 ≤
        2 / (2 * sigma - 1) -
          ((36077197491400761 : ℝ) / 10 ^ 18 +
            (sigma - 1) ^ 2 / termCount ^ 2) := by
      norm_num [sigma, termCount]
    _ ≤ 2 / (2 * sigma - 1) -
          ((∑ n ∈ Finset.range termCount, seriesTerm (sigma - 1) n) +
            (sigma - 1) ^ 2 / termCount ^ 2) := by
      linarith only [series_sum_le]

end UnitDistance.Witness.PairOverlapStudentCompactArithmeticRun20260920
