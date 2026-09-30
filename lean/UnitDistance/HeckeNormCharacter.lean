module

public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.Tactic.NormNum

@[expose] public section
set_option backward.privateInPublic true


/-! Real and complex forms of the existing Mathlib character `ZMod.χ₄`,
applied to the ordinary absolute norm of an integral ideal. -/
noncomputable section
open NumberField
namespace UnitDistance.NumberFieldAnalysis

/-- The ordinary primitive quadratic character modulo four, in real values. -/
def chiFourReal (n : ℕ) : ℝ := (ZMod.χ₄ (n : ZMod 4) : ℤ)

/-- The same independently defined character with complex values. -/
def chiFourComplex (n : ℕ) : ℂ := (ZMod.χ₄ (n : ZMod 4) : ℤ)

@[simp] theorem chiFourReal_one : chiFourReal 1 = 1 := by simp [chiFourReal]
@[simp] theorem chiFourComplex_one : chiFourComplex 1 = 1 := by simp [chiFourComplex]

@[simp] theorem chiFourReal_mul (m n : ℕ) :
    chiFourReal (m*n) = chiFourReal m*chiFourReal n := by
  simp only [chiFourReal, Nat.cast_mul, map_mul, Int.cast_mul]

@[simp] theorem chiFourComplex_mul (m n : ℕ) :
    chiFourComplex (m*n) = chiFourComplex m*chiFourComplex n := by
  simp only [chiFourComplex, Nat.cast_mul, map_mul, Int.cast_mul]

theorem chiFourComplex_eq_ofReal (n : ℕ) : chiFourComplex n = (chiFourReal n : ℂ) := by
  simp only [chiFourComplex, chiFourReal, Complex.ofReal_intCast]

theorem abs_chiFourReal_le_one (n : ℕ) : |chiFourReal n| ≤ 1 := by
  rw [chiFourReal, ZMod.χ₄_nat_eq_if_mod_four]
  split_ifs <;> norm_num

theorem norm_chiFourComplex_le_one (n : ℕ) : ‖chiFourComplex n‖ ≤ 1 := by
  rw [chiFourComplex_eq_ofReal, Complex.norm_real, Real.norm_eq_abs]
  exact abs_chiFourReal_le_one n

theorem chiFourReal_sq_of_odd {n : ℕ} (hn : Odd n) : chiFourReal n^2 = 1 := by
  rw [chiFourReal, ZMod.χ₄_nat_eq_if_mod_four, if_neg (by have h := Nat.odd_iff.mp hn; omega : ¬n%2=0)]
  split_ifs <;> norm_num

theorem chiFourReal_zero_of_even {n : ℕ} (hn : Even n) : chiFourReal n = 0 := by
  rw [chiFourReal, ZMod.χ₄_nat_eq_if_mod_four, if_pos (by have h := Nat.even_iff.mp hn; omega : n%2=0)]
  norm_num

variable (K : Type*) [Field K] [NumberField K]

/-- Character of the literal absolute norm of an ordinary integral ideal. -/
def idealChiFour (I : Ideal (𝓞 K)) : ℝ := chiFourReal (Ideal.absNorm I)

@[simp] theorem idealChiFour_mul (I J : Ideal (𝓞 K)) :
    idealChiFour K (I*J) = idealChiFour K I*idealChiFour K J := by
  simp only [idealChiFour, map_mul, chiFourReal_mul]

theorem abs_idealChiFour_le_one (I : Ideal (𝓞 K)) : |idealChiFour K I| ≤ 1 :=
  abs_chiFourReal_le_one _

end UnitDistance.NumberFieldAnalysis
