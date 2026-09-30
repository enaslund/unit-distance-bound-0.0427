module

public import UnitDistance.LogBounds

@[expose] public section
set_option backward.privateInPublic true


/-!
# Logarithm and real-power enclosures computed in `ℚ`

`logLo y` and `logHi y` are rational numbers computed from `y : ℚ` by exact
rational arithmetic: `y` is scaled by a power of two into `[1, 2)` and the
`artanh` series of `UnitDistance.log_enclosure` is summed to 30 terms, with its
geometric remainder. `log_bounds` proves `logLo y ≤ log y ≤ logHi y` for every
positive `y`, so a concrete enclosure is reduced to a rational inequality that
the kernel checks by evaluation (`decide +kernel`). The width of the enclosure
is about `10⁻²⁸ (1 + |log₂ y|)`.
-/

namespace UnitDistance.Sqrt241.Numerics

/-- Partial sums `∑_{i<n} x^(2i+1)/(2i+1)` of the series of `artanh x`. -/
def atanhSum (x : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => atanhSum x n + x ^ (2 * n + 1) / (2 * n + 1)

theorem atanhSum_cast (x : ℚ) (n : ℕ) :
    ((atanhSum x n : ℚ) : ℝ) =
      ∑ i ∈ Finset.range n, ((x : ℝ) ^ (2 * i + 1) / (2 * i + 1)) := by
  induction n with
  | zero => simp [atanhSum]
  | succ n ih =>
    rw [atanhSum, Finset.sum_range_succ, ← ih]
    push_cast
    ring

/-- Number of series terms used by every enclosure. -/
def logTerms : ℕ := 30

/-- Lower series bound for `log y`, valid for `1 ≤ y`. -/
def logOneLo (y : ℚ) : ℚ := 2 * atanhSum ((y - 1) / (y + 1)) logTerms

/-- Upper series bound for `log y`, valid for `1 ≤ y`. -/
def logOneHi (y : ℚ) : ℚ :=
  2 * (atanhSum ((y - 1) / (y + 1)) logTerms +
    ((y - 1) / (y + 1)) ^ (2 * logTerms + 1) / (1 - ((y - 1) / (y + 1)) ^ 2))

theorem logOne_bounds {y : ℚ} (hy : 1 ≤ y) :
    ((logOneLo y : ℚ) : ℝ) ≤ Real.log (y : ℝ) ∧
      Real.log (y : ℝ) ≤ ((logOneHi y : ℚ) : ℝ) := by
  have hy' : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  apply UnitDistance.log_enclosure (y : ℝ) logTerms hy'
  · apply le_of_eq
    simp only [logOneLo]
    push_cast [atanhSum_cast]
    rfl
  · apply le_of_eq
    simp only [logOneHi]
    push_cast [atanhSum_cast]
    rfl

/-- Scale by powers of two until the value lies in `[1, 2)`; the second
component records the exponent. -/
def reduceTwo : ℕ → ℚ → ℤ → ℚ × ℤ
  | 0, r, k => (r, k)
  | fuel + 1, r, k =>
    if 2 ≤ r then reduceTwo fuel (r / 2) (k + 1)
    else if r < 1 then reduceTwo fuel (r * 2) (k - 1)
    else (r, k)

theorem reduceTwo_spec (fuel : ℕ) :
    ∀ (r : ℚ) (k : ℤ), 0 < r →
      0 < (reduceTwo fuel r k).1 ∧
        ((reduceTwo fuel r k).1 : ℝ) * (2 : ℝ) ^ (reduceTwo fuel r k).2 =
          (r : ℝ) * (2 : ℝ) ^ k := by
  induction fuel with
  | zero => intro r k hr; exact ⟨hr, rfl⟩
  | succ fuel ih =>
    intro r k hr
    simp only [reduceTwo]
    split_ifs with h2 h1
    · obtain ⟨hpos, heq⟩ := ih (r / 2) (k + 1) (by positivity)
      refine ⟨hpos, heq.trans ?_⟩
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      push_cast
      field_simp
    · obtain ⟨hpos, heq⟩ := ih (r * 2) (k - 1) (by positivity)
      refine ⟨hpos, heq.trans ?_⟩
      rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
      push_cast
      field_simp
    · exact ⟨hr, rfl⟩

def log2Lo : ℚ := logOneLo 2
def log2Hi : ℚ := logOneHi 2

theorem log_two_bounds :
    ((log2Lo : ℚ) : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ ((log2Hi : ℚ) : ℝ) := by
  have h := logOne_bounds (y := 2) (by norm_num)
  simpa [log2Lo, log2Hi] using h

/-- Enclosure of `log r` for any positive `r`: the series of `r` if `1 ≤ r`,
otherwise the negated series of `1/r`. -/
def logUnitLo (r : ℚ) : ℚ := if 1 ≤ r then logOneLo r else -logOneHi r⁻¹
def logUnitHi (r : ℚ) : ℚ := if 1 ≤ r then logOneHi r else -logOneLo r⁻¹

theorem logUnit_bounds {r : ℚ} (hr : 0 < r) :
    ((logUnitLo r : ℚ) : ℝ) ≤ Real.log (r : ℝ) ∧
      Real.log (r : ℝ) ≤ ((logUnitHi r : ℚ) : ℝ) := by
  unfold logUnitLo logUnitHi
  split_ifs with h
  · exact logOne_bounds h
  · have hinv : 1 ≤ r⁻¹ := by
      rw [not_le] at h
      exact (one_le_inv₀ hr).mpr h.le
    have hb := logOne_bounds hinv
    have hlog : Real.log ((r⁻¹ : ℚ) : ℝ) = -Real.log (r : ℝ) := by
      push_cast
      exact Real.log_inv _
    rw [hlog] at hb
    push_cast
    constructor <;> linarith [hb.1, hb.2]

/-- Rational lower bound for `log y` (meaningful for `0 < y`). -/
def logLo (y : ℚ) : ℚ :=
  let rk := reduceTwo 400 y 0
  (if 0 ≤ rk.2 then (rk.2 : ℚ) * log2Lo else (rk.2 : ℚ) * log2Hi) + logUnitLo rk.1

/-- Rational upper bound for `log y` (meaningful for `0 < y`). -/
def logHi (y : ℚ) : ℚ :=
  let rk := reduceTwo 400 y 0
  (if 0 ≤ rk.2 then (rk.2 : ℚ) * log2Hi else (rk.2 : ℚ) * log2Lo) + logUnitHi rk.1

theorem log_bounds {y : ℚ} (hy : 0 < y) :
    ((logLo y : ℚ) : ℝ) ≤ Real.log (y : ℝ) ∧ Real.log (y : ℝ) ≤ ((logHi y : ℚ) : ℝ) := by
  obtain ⟨hpos, heq⟩ := reduceTwo_spec 400 y 0 hy
  set r := (reduceTwo 400 y 0).1 with hr
  set k := (reduceTwo 400 y 0).2 with hk
  have hy' : (y : ℝ) = (r : ℝ) * (2 : ℝ) ^ k := by
    rw [heq]
    simp
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hpos
  have hlog : Real.log (y : ℝ) = Real.log (r : ℝ) + (k : ℝ) * Real.log 2 := by
    rw [hy', Real.log_mul hrpos.ne' (zpow_ne_zero _ (by norm_num)), Real.log_zpow]
  have hu := logUnit_bounds hpos
  have h2 := log_two_bounds
  unfold logLo logHi
  simp only [← hr, ← hk]
  rw [hlog]
  split_ifs with hk0
  · have hk0' : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk0
    have h1 := mul_le_mul_of_nonneg_left h2.1 hk0'
    have h3 := mul_le_mul_of_nonneg_left h2.2 hk0'
    push_cast
    constructor <;> nlinarith [hu.1, hu.2]
  · have hk0' : (k : ℝ) ≤ 0 := by
      have : k < 0 := lt_of_not_ge hk0
      exact_mod_cast this.le
    have h1 := mul_le_mul_of_nonpos_left h2.1 hk0'
    have h3 := mul_le_mul_of_nonpos_left h2.2 hk0'
    push_cast
    constructor <;> nlinarith [hu.1, hu.2]

theorem log_ge_of_le_logLo {y lo : ℚ} (hy : 0 < y) (h : lo ≤ logLo y) :
    ((lo : ℚ) : ℝ) ≤ Real.log (y : ℝ) :=
  (Rat.cast_le.mpr h).trans (log_bounds hy).1

theorem log_le_of_logHi_le {y hi : ℚ} (hy : 0 < y) (h : logHi y ≤ hi) :
    Real.log (y : ℝ) ≤ ((hi : ℚ) : ℝ) :=
  (log_bounds hy).2.trans (Rat.cast_le.mpr h)

/-- `y^e ≤ U` from `e · logHi y ≤ logLo U`. -/
theorem rpow_le_of_logs {y e U : ℚ} (hy : 0 < y) (hU : 0 < U) (he : 0 ≤ e)
    (h : e * logHi y ≤ logLo U) : (y : ℝ) ^ (e : ℝ) ≤ (U : ℝ) := by
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  have hU' : (0 : ℝ) < U := by exact_mod_cast hU
  have he' : (0 : ℝ) ≤ e := by exact_mod_cast he
  have hly := (log_bounds hy).2
  have hlU := (log_bounds hU).1
  have hh : ((e * logHi y : ℚ) : ℝ) ≤ ((logLo U : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at hh
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hy' _) hU').mp
  rw [Real.log_rpow hy']
  nlinarith [mul_le_mul_of_nonneg_left hly he']

/-- `L ≤ y^e` from `logHi L ≤ e · logLo y`. -/
theorem le_rpow_of_logs {y e L : ℚ} (hy : 0 < y) (hL : 0 < L) (he : 0 ≤ e)
    (h : logHi L ≤ e * logLo y) : (L : ℝ) ≤ (y : ℝ) ^ (e : ℝ) := by
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have he' : (0 : ℝ) ≤ e := by exact_mod_cast he
  have hly := (log_bounds hy).1
  have hlL := (log_bounds hL).2
  have hh : ((logHi L : ℚ) : ℝ) ≤ ((e * logLo y : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at hh
  apply (Real.log_le_log_iff hL' (Real.rpow_pos_of_pos hy' _)).mp
  rw [Real.log_rpow hy']
  nlinarith [mul_le_mul_of_nonneg_left hly he']

end UnitDistance.Sqrt241.Numerics
