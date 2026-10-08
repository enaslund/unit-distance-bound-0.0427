module

public import UnitDistance.Sqrt241.Witness
public import UnitDistance.Sqrt241.Numerics.RatLog
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section
set_option backward.privateInPublic true


/-!
# Logarithm enclosures for the margin of the ℚ(√241) witness

Each bound is an 18-decimal rational endpoint, checked against the rational
enclosures `logLo`/`logHi` of `RatLog.lean` by kernel evaluation. `log π` uses
Mathlib's 20-digit bounds for `π`. `logRD_bounds` encloses the root-discriminant
logarithm `ℓ = (9/4) log 2 + (1/2) log 3615`.
-/

open UnitDistance.Sqrt241.Numerics

namespace UnitDistance.Sqrt241.Witness

theorem log_two_bounds :
    (693147180559945309 / 10 ^ 18 : ℝ) ≤ Real.log 2 ∧
      Real.log 2 ≤ (693147180559945310 / 10 ^ 18 : ℝ) := by
  have h1 := log_ge_of_le_logLo (y := 2) (lo := 693147180559945309 / 10 ^ 18)
    (by norm_num) (by decide +kernel)
  have h2 := log_le_of_logHi_le (y := 2) (hi := 693147180559945310 / 10 ^ 18)
    (by norm_num) (by decide +kernel)
  push_cast at h1 h2
  exact ⟨h1, h2⟩

theorem log_3615_bounds :
    (8192847134592865061 / 10 ^ 18 : ℝ) ≤ Real.log 3615 ∧
      Real.log 3615 ≤ (8192847134592865062 / 10 ^ 18 : ℝ) := by
  have h1 := log_ge_of_le_logLo (y := 3615) (lo := 8192847134592865061 / 10 ^ 18)
    (by norm_num) (by decide +kernel)
  have h2 := log_le_of_logHi_le (y := 3615) (hi := 8192847134592865062 / 10 ^ 18)
    (by norm_num) (by decide +kernel)
  push_cast at h1 h2
  exact ⟨h1, h2⟩

theorem log_pi_bounds :
    (1144729885849400174 / 10 ^ 18 : ℝ) ≤ Real.log Real.pi ∧
      Real.log Real.pi ≤ (1144729885849400175 / 10 ^ 18 : ℝ) := by
  have hlo : (314159265358979323846 / 10 ^ 20 : ℝ) < Real.pi := by
    have h := Real.pi_gt_d20
    norm_num at h ⊢
    linarith
  have hhi : Real.pi < (314159265358979323847 / 10 ^ 20 : ℝ) := by
    have h := Real.pi_lt_d20
    norm_num at h ⊢
    linarith
  have h1 := log_ge_of_le_logLo (y := 314159265358979323846 / 10 ^ 20)
    (lo := 1144729885849400174 / 10 ^ 18) (by norm_num) (by decide +kernel)
  have h2 := log_le_of_logHi_le (y := 314159265358979323847 / 10 ^ 20)
    (hi := 1144729885849400175 / 10 ^ 18) (by norm_num) (by decide +kernel)
  have m1 := Real.log_lt_log (by norm_num) hlo
  have m2 := Real.log_lt_log Real.pi_pos hhi
  push_cast at h1 h2
  constructor <;> linarith

/-- Enclosure of `ℓ = (9/4) log 2 + (1/2) log 3615`. -/
theorem logRD_bounds :
    (565600472355630 / 10 ^ 14 : ℝ) ≤ logRD ∧ logRD ≤ (565600472355631 / 10 ^ 14 : ℝ) := by
  have h2 := log_two_bounds
  have h3 := log_3615_bounds
  unfold logRD
  constructor <;> nlinarith [h2.1, h2.2, h3.1, h3.2]

theorem log_four_increment_bounds :
    (-1756778500332809483 / 10 ^ 18 : ℝ) ≤ Real.log (4 * increment) ∧
      Real.log (4 * increment) ≤ (-1756778500332809480 / 10 ^ 18 : ℝ) := by
  have h1 := log_ge_of_le_logLo (y := 863 / 5000) (lo := -1756778500332809483 / 10 ^ 18)
    (by norm_num) (by decide +kernel)
  have h2 := log_le_of_logHi_le (y := 863 / 5000) (hi := -1756778500332809480 / 10 ^ 18)
    (by norm_num) (by decide +kernel)
  have he : 4 * increment = (863 / 5000 : ℝ) := by norm_num [increment]
  rw [he]
  push_cast at h1 h2
  exact ⟨h1, h2⟩

theorem log_one_add_increment_bounds :
    (42244981593746004 / 10 ^ 18 : ℝ) ≤ Real.log (1 + increment) ∧
      Real.log (1 + increment) ≤ (42244981593746007 / 10 ^ 18 : ℝ) := by
  have h1 := log_ge_of_le_logLo (y := 20863 / 20000) (lo := 42244981593746004 / 10 ^ 18)
    (by norm_num) (by decide +kernel)
  have h2 := log_le_of_logHi_le (y := 20863 / 20000) (hi := 42244981593746007 / 10 ^ 18)
    (by norm_num) (by decide +kernel)
  have he : 1 + increment = (20863 / 20000 : ℝ) := by norm_num [increment]
  rw [he]
  push_cast at h1 h2
  exact ⟨h1, h2⟩

end UnitDistance.Sqrt241.Witness
