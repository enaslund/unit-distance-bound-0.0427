module

public import UnitDistance.LocalWindows

@[expose] public section
set_option backward.privateInPublic true


/-! # Exact shell differences and periods

These are algebraic consequences of the proved additive overlap integral in
`LocalWindows`. The connection to actual shell indicators is kept explicit.
-/

noncomputable section

open Set MeasureTheory
open scoped BigOperators

namespace UnitDistance.Local

/-- A backward difference with the ball of index `0` as boundary value. -/
def backDiff (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => f 0
  | i + 1 => f (i + 1) - f i

def mixedDiff (f : ℕ → ℕ → ℝ) (i r : ℕ) : ℝ :=
  backDiff (fun i => backDiff (f i) r) i

/-- Haar mass of the `i`th shell, with the whole valuation ring as shell zero. -/
def shellMass (Q : ℝ) : ℕ → ℝ
  | 0 => 1
  | i + 1 => Q ^ (i + 1) - Q ^ i

def minKernel (Q : ℝ) (i r : ℕ) : ℝ := Q ^ min i r

def maxMinKernel (Q : ℝ) (i r : ℕ) : ℝ := (max i r : ℕ) * Q ^ min i r

/-- The manuscript's one-coordinate shell kernel. -/
def shellD (Q : ℝ) (i r : ℕ) : ℝ :=
  if i = r then
    if i = 0 then 0 else (i : ℝ) * shellMass Q i - Q ^ (i - 1)
  else shellMass Q (min i r)

theorem mixedDiff_minKernel (Q : ℝ) (i r : ℕ) :
    mixedDiff (minKernel Q) i r = if i = r then shellMass Q i else 0 := by
  rcases i with _ | i <;> rcases r with _ | r
  · simp [mixedDiff, backDiff, minKernel, shellMass]
  · simp [mixedDiff, backDiff, minKernel]
  · simp [mixedDiff, backDiff, minKernel]
  · rcases lt_trichotomy i r with h | h | h
    · have hir : i + 1 ≤ r := by omega
      simp [mixedDiff, backDiff, minKernel, min_eq_left (le_of_lt h),
        min_eq_left hir, min_eq_left (by omega : i ≤ r + 1),
        min_eq_left (by omega : i + 1 ≤ r + 1), show i ≠ r by omega]
    · subst r
      simp [mixedDiff, backDiff, minKernel, shellMass]
    · have hri : r + 1 ≤ i := by omega
      simp [mixedDiff, backDiff, minKernel, min_eq_right (le_of_lt h),
        min_eq_right hri, min_eq_right (by omega : r ≤ i + 1),
        min_eq_right (by omega : r + 1 ≤ i + 1), show i ≠ r by omega]

theorem mixedDiff_maxMinKernel (Q : ℝ) (i r : ℕ) :
    mixedDiff (maxMinKernel Q) i r = shellD Q i r := by
  rcases i with _ | i <;> rcases r with _ | r
  · simp [mixedDiff, backDiff, maxMinKernel, shellD]
  · simp [mixedDiff, backDiff, maxMinKernel, shellD, shellMass]
  · simp [mixedDiff, backDiff, maxMinKernel, shellD, shellMass]
  · rcases lt_trichotomy i r with h | h | h
    · have hir : i + 1 ≤ r := by omega
      simp [mixedDiff, backDiff, maxMinKernel, shellD, shellMass,
        min_eq_left (le_of_lt h), min_eq_left hir, min_eq_left (by omega : i ≤ r + 1),
        min_eq_left (by omega : i + 1 ≤ r + 1),
        max_eq_right (le_of_lt h), max_eq_right hir, max_eq_right (by omega : i ≤ r + 1),
        max_eq_right (by omega : i + 1 ≤ r + 1), show i ≠ r by omega]
      ring
    · subst r
      simp [mixedDiff, backDiff, maxMinKernel, shellD, shellMass]
      ring
    · have hri : r + 1 ≤ i := by omega
      simp [mixedDiff, backDiff, maxMinKernel, shellD, shellMass,
        min_eq_right (le_of_lt h), min_eq_right hri, min_eq_right (by omega : r ≤ i + 1),
        min_eq_right (by omega : r + 1 ≤ i + 1),
        max_eq_left (le_of_lt h), max_eq_left hri, max_eq_left (by omega : r ≤ i + 1),
        max_eq_left (by omega : r + 1 ≤ i + 1), show i ≠ r by omega]
      ring

theorem backDiff_add (f g : ℕ → ℝ) (i : ℕ) :
    backDiff (fun i => f i + g i) i = backDiff f i + backDiff g i := by
  cases i with
  | zero => rfl
  | succ i => simp only [backDiff]; ring

theorem backDiff_mul_const (f : ℕ → ℝ) (c : ℝ) (i : ℕ) :
    backDiff (fun i => f i * c) i = backDiff f i * c := by
  cases i with
  | zero => rfl
  | succ i => simp only [backDiff]; ring

theorem mixedDiff_add (f g : ℕ → ℕ → ℝ) (i r : ℕ) :
    mixedDiff (fun i r => f i r + g i r) i r =
      mixedDiff f i r + mixedDiff g i r := by
  simp [mixedDiff, backDiff_add]

theorem mixedDiff_mul_const (f : ℕ → ℕ → ℝ) (c : ℝ) (i r : ℕ) :
    mixedDiff (fun i r => f i r * c) i r = mixedDiff f i r * c := by
  simp [mixedDiff, backDiff_mul_const]

/-- Four successive differences, one for each endpoint coordinate. -/
def fourDiff (f : ℕ → ℕ → ℕ → ℕ → ℝ) (i j r t : ℕ) : ℝ :=
  mixedDiff (fun i r => mixedDiff (fun j t => f i j r t) j t) i r

theorem fourDiff_add (f g : ℕ → ℕ → ℕ → ℕ → ℝ) (i j r t : ℕ) :
    fourDiff (fun i j r t => f i j r t + g i j r t) i j r t =
      fourDiff f i j r t + fourDiff g i j r t := by
  simp [fourDiff, mixedDiff_add]

theorem fourDiff_product (f g : ℕ → ℕ → ℝ) (i j r t : ℕ) :
    fourDiff (fun i j r t => f i r * g j t) i j r t =
      mixedDiff f i r * mixedDiff g j t := by
  simp only [fourDiff]
  conv_lhs => arg 1; ext i r; rw [show (fun j t => f i r * g j t) =
    (fun j t => g j t * f i r) by funext j t; ring, mixedDiff_mul_const]
  simp_rw [mul_comm (mixedDiff g j t), mixedDiff_mul_const]

/-- The rectangle formula restricted to the nonnegative indices relevant to
shells. The factor `Q^k` records the fixed vertical dilation. -/
def rectangleShellGram (Q : ℝ) (k i j r t : ℕ) : ℝ :=
  Q ^ k * (minKernel Q i r * minKernel Q j t *
    ((k : ℝ) + 1 + (max i r : ℕ) + (max j t : ℕ)))

def shellKernel (Q : ℝ) (k i j r t : ℕ) : ℝ :=
  ((k : ℝ) + 1) * shellMass Q i * shellMass Q j * (if i = r ∧ j = t then 1 else 0) +
    shellMass Q j * shellD Q i r * (if j = t then 1 else 0) +
    shellMass Q i * shellD Q j t * (if i = r then 1 else 0)

/-- The exact shell matrix is obtained from rectangle overlaps, rather than
being an independently chosen quadratic form. -/
theorem fourDiff_rectangleShellGram (Q : ℝ) (k i j r t : ℕ) :
    fourDiff (rectangleShellGram Q k) i j r t = Q ^ k * shellKernel Q k i j r t := by
  have h : rectangleShellGram Q k = fun i j r t =>
      minKernel Q i r * (minKernel Q j t * (Q ^ k * ((k : ℝ) + 1))) +
      maxMinKernel Q i r * (minKernel Q j t * Q ^ k) +
      minKernel Q i r * (maxMinKernel Q j t * Q ^ k) := by
    funext i j r t
    simp only [rectangleShellGram, maxMinKernel, minKernel]
    ring
  rw [h]
  simp only [fourDiff_add, fourDiff_product, mixedDiff_mul_const,
    mixedDiff_minKernel, mixedDiff_maxMinKernel, shellKernel]
  split_ifs <;> simp_all <;> ring

end UnitDistance.Local
