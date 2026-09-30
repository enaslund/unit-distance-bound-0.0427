module

public import UnitDistance.Sqrt241.Numerics.RatLog

@[expose] public section
set_option backward.privateInPublic true


/-!
# Logarithm enclosures with outward rounding

`logLoR y ≤ log y ≤ logHiR y` for every positive rational `y` (`logR_bounds`), with
the same argument reduction and the same 30-term `artanh` series as `logLo`/`logHi`
of `RatLog.lean`, but every power `x^(2i+1)` and every term of the series is rounded
outward to a multiple of `10⁻⁴⁰` (`roundDown`, `roundUp`).

The exact series of `RatLog.lean`, evaluated at an argument with `k`-digit numerator
and denominator, carries rationals with about `60 k` digits; their normalizations
dominate kernel evaluation (in particular in con-ron, the independent checker of the
Palomar pipeline). Here every intermediate rational has at most about 80 digits. For
the reduced arguments `1 ≤ y < 2` the additional error is below `10⁻³⁶`, far inside
the `10⁻²⁸` width of the series enclosure; the bounds hold for every `y` regardless.
-/

namespace UnitDistance.Sqrt241.Numerics

/-- The rounding grid is `1 / roundScale`. -/
def roundScale : ℕ := 10 ^ 40

/-- Round down to a multiple of `1 / roundScale`. -/
def roundDown (r : ℚ) : ℚ := (⌊r * roundScale⌋ : ℚ) / roundScale

/-- Round up to a multiple of `1 / roundScale`. -/
def roundUp (r : ℚ) : ℚ := (⌈r * roundScale⌉ : ℚ) / roundScale

theorem roundScale_pos : (0 : ℚ) < roundScale := by
  unfold roundScale
  positivity

theorem roundDown_le (r : ℚ) : roundDown r ≤ r := by
  unfold roundDown
  rw [div_le_iff₀ roundScale_pos]
  exact Int.floor_le _

theorem le_roundUp (r : ℚ) : r ≤ roundUp r := by
  unfold roundUp
  rw [le_div_iff₀ roundScale_pos]
  exact Int.le_ceil _

theorem roundDown_nonneg {r : ℚ} (hr : 0 ≤ r) : 0 ≤ roundDown r := by
  unfold roundDown
  apply div_nonneg _ roundScale_pos.le
  exact_mod_cast Int.floor_nonneg.mpr (mul_nonneg hr roundScale_pos.le)

/-! ## The rounded `artanh` series -/

/-- Lower bounds for `x^(2n+1)`, rounded down at every step (for `0 ≤ x2 ≤ x²`). -/
def powLoR (x x2 : ℚ) : ℕ → ℚ
  | 0 => roundDown x
  | n + 1 => roundDown (powLoR x x2 n * x2)

/-- Upper bounds for `x^(2n+1)`, rounded up at every step (for `x² ≤ x2`). -/
def powHiR (x x2 : ℚ) : ℕ → ℚ
  | 0 => roundUp x
  | n + 1 => roundUp (powHiR x x2 n * x2)

theorem powLoR_bounds {x x2 : ℚ} (hx : 0 ≤ x) (h0 : 0 ≤ x2) (h1 : x2 ≤ x ^ 2) (n : ℕ) :
    0 ≤ powLoR x x2 n ∧ powLoR x x2 n ≤ x ^ (2 * n + 1) := by
  induction n with
  | zero => exact ⟨roundDown_nonneg hx, by simpa [powLoR] using roundDown_le x⟩
  | succ n ih =>
    obtain ⟨hp0, hp1⟩ := ih
    refine ⟨roundDown_nonneg (mul_nonneg hp0 h0), (roundDown_le _).trans ?_⟩
    calc powLoR x x2 n * x2 ≤ x ^ (2 * n + 1) * x ^ 2 :=
          mul_le_mul hp1 h1 h0 (pow_nonneg hx _)
      _ = x ^ (2 * (n + 1) + 1) := by ring

theorem powHiR_bounds {x x2 : ℚ} (hx : 0 ≤ x) (h1 : x ^ 2 ≤ x2) (n : ℕ) :
    x ^ (2 * n + 1) ≤ powHiR x x2 n := by
  induction n with
  | zero => simpa [powHiR] using le_roundUp x
  | succ n ih =>
    refine le_trans ?_ (le_roundUp _)
    calc x ^ (2 * (n + 1) + 1) = x ^ (2 * n + 1) * x ^ 2 := by ring
      _ ≤ powHiR x x2 n * x2 :=
          mul_le_mul ih h1 (pow_nonneg hx _) ((pow_nonneg hx _).trans ih)

/-- Lower bound for `∑_{i<n} x^(2i+1)/(2i+1)`, every term rounded down. -/
def atanhLoR (x x2 : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => atanhLoR x x2 n + roundDown (powLoR x x2 n / (2 * n + 1))

/-- Upper bound for `∑_{i<n} x^(2i+1)/(2i+1)`, every term rounded up. -/
def atanhHiR (x x2 : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => atanhHiR x x2 n + roundUp (powHiR x x2 n / (2 * n + 1))

theorem atanhLoR_le {x x2 : ℚ} (hx : 0 ≤ x) (h0 : 0 ≤ x2) (h1 : x2 ≤ x ^ 2) (n : ℕ) :
    atanhLoR x x2 n ≤ atanhSum x n := by
  induction n with
  | zero => simp [atanhLoR, atanhSum]
  | succ n ih =>
    simp only [atanhLoR, atanhSum]
    apply add_le_add ih
    refine (roundDown_le _).trans ?_
    exact div_le_div_of_nonneg_right (powLoR_bounds hx h0 h1 n).2 (by positivity)

theorem atanhSum_le_atanhHiR {x x2 : ℚ} (hx : 0 ≤ x) (h1 : x ^ 2 ≤ x2) (n : ℕ) :
    atanhSum x n ≤ atanhHiR x x2 n := by
  induction n with
  | zero => simp [atanhHiR, atanhSum]
  | succ n ih =>
    simp only [atanhHiR, atanhSum]
    apply add_le_add ih
    refine le_trans ?_ (le_roundUp _)
    exact div_le_div_of_nonneg_right (powHiR_bounds hx h1 n) (by positivity)

/-! ## Enclosures of `log y` for `1 ≤ y` -/

/-- Lower bound for `2 artanh x`, `x = (y-1)/(y+1)`. -/
def logOneLoAux (x : ℚ) : ℚ := 2 * atanhLoR x (roundDown (x * x)) logTerms

/-- Upper bound for `2 artanh x` (valid when `roundUp (x * x) < 1`): series plus tail. -/
def logOneHiAux (x : ℚ) : ℚ :=
  2 * (atanhHiR x (roundUp (x * x)) logTerms +
    roundUp (powHiR x (roundUp (x * x)) logTerms / (1 - roundUp (x * x))))

/-- Rounded lower bound for `log y`, valid for `1 ≤ y`. -/
def logOneLoR (y : ℚ) : ℚ := logOneLoAux ((y - 1) / (y + 1))

/-- Rounded upper bound for `log y`, valid for `1 ≤ y` (`y - 1` if the rounded
square of `(y-1)/(y+1)` is not below one). -/
def logOneHiR (y : ℚ) : ℚ :=
  if roundUp ((y - 1) / (y + 1) * ((y - 1) / (y + 1))) < 1 then logOneHiAux ((y - 1) / (y + 1))
  else y - 1

theorem logOneLoR_le_logOneLo {y : ℚ} (hy : 1 ≤ y) : logOneLoR y ≤ logOneLo y := by
  have hx0 : 0 ≤ (y - 1) / (y + 1) := div_nonneg (by linarith) (by linarith)
  unfold logOneLoR logOneLoAux logOneLo
  have h := atanhLoR_le hx0 (roundDown_nonneg (mul_nonneg hx0 hx0))
    ((roundDown_le _).trans (le_of_eq (by ring))) logTerms
  linarith

theorem logOneHi_le_logOneHiAux {y : ℚ} (hy : 1 ≤ y)
    (hsq : roundUp ((y - 1) / (y + 1) * ((y - 1) / (y + 1))) < 1) :
    logOneHi y ≤ logOneHiAux ((y - 1) / (y + 1)) := by
  set x := (y - 1) / (y + 1) with hxdef
  have hx0 : 0 ≤ x := div_nonneg (by linarith) (by linarith)
  have hx2 : x ^ 2 ≤ roundUp (x * x) := (le_of_eq (by ring)).trans (le_roundUp _)
  have hsum := atanhSum_le_atanhHiR hx0 hx2 logTerms
  have hp := powHiR_bounds hx0 hx2 logTerms
  have hden : 0 < 1 - roundUp (x * x) := by linarith
  have htail : x ^ (2 * logTerms + 1) / (1 - x ^ 2) ≤
      roundUp (powHiR x (roundUp (x * x)) logTerms / (1 - roundUp (x * x))) := by
    refine le_trans ?_ (le_roundUp _)
    calc x ^ (2 * logTerms + 1) / (1 - x ^ 2)
        ≤ powHiR x (roundUp (x * x)) logTerms / (1 - x ^ 2) :=
          div_le_div_of_nonneg_right hp (by linarith)
      _ ≤ powHiR x (roundUp (x * x)) logTerms / (1 - roundUp (x * x)) :=
          div_le_div_of_nonneg_left ((pow_nonneg hx0 _).trans hp) hden (by linarith)
  unfold logOneHi logOneHiAux
  rw [← hxdef]
  linarith

theorem logOneR_bounds {y : ℚ} (hy : 1 ≤ y) :
    ((logOneLoR y : ℚ) : ℝ) ≤ Real.log (y : ℝ) ∧
      Real.log (y : ℝ) ≤ ((logOneHiR y : ℚ) : ℝ) := by
  have hb := logOne_bounds hy
  constructor
  · exact (Rat.cast_le.mpr (logOneLoR_le_logOneLo hy)).trans hb.1
  · unfold logOneHiR
    split_ifs with hsq
    · exact hb.2.trans (Rat.cast_le.mpr (logOneHi_le_logOneHiAux hy hsq))
    · have hy0 : (0 : ℝ) < (y : ℝ) := by
        have : (0 : ℚ) < y := by linarith
        exact_mod_cast this
      push_cast
      exact Real.log_le_sub_one_of_pos hy0

/-! ## Enclosures of `log y` for `0 < y` -/

/-- Rounded enclosure of `log r` for positive `r`, as `logUnitLo`/`logUnitHi`. -/
def logUnitLoR (r : ℚ) : ℚ := if 1 ≤ r then logOneLoR r else -logOneHiR r⁻¹
def logUnitHiR (r : ℚ) : ℚ := if 1 ≤ r then logOneHiR r else -logOneLoR r⁻¹

theorem logUnitR_bounds {r : ℚ} (hr : 0 < r) :
    ((logUnitLoR r : ℚ) : ℝ) ≤ Real.log (r : ℝ) ∧
      Real.log (r : ℝ) ≤ ((logUnitHiR r : ℚ) : ℝ) := by
  unfold logUnitLoR logUnitHiR
  split_ifs with h
  · exact logOneR_bounds h
  · have hinv : 1 ≤ r⁻¹ := by
      rw [not_le] at h
      exact (one_le_inv₀ hr).mpr h.le
    have hb := logOneR_bounds hinv
    have hlog : Real.log ((r⁻¹ : ℚ) : ℝ) = -Real.log (r : ℝ) := by
      push_cast
      exact Real.log_inv _
    rw [hlog] at hb
    push_cast
    constructor <;> linarith [hb.1, hb.2]

/-- Rational lower bound for `log y` (meaningful for `0 < y`), rounded outward. -/
def logLoR (y : ℚ) : ℚ :=
  let rk := reduceTwo 400 y 0
  (if 0 ≤ rk.2 then (rk.2 : ℚ) * log2Lo else (rk.2 : ℚ) * log2Hi) + logUnitLoR rk.1

/-- Rational upper bound for `log y` (meaningful for `0 < y`), rounded outward. -/
def logHiR (y : ℚ) : ℚ :=
  let rk := reduceTwo 400 y 0
  (if 0 ≤ rk.2 then (rk.2 : ℚ) * log2Hi else (rk.2 : ℚ) * log2Lo) + logUnitHiR rk.1

theorem logR_bounds {y : ℚ} (hy : 0 < y) :
    ((logLoR y : ℚ) : ℝ) ≤ Real.log (y : ℝ) ∧ Real.log (y : ℝ) ≤ ((logHiR y : ℚ) : ℝ) := by
  obtain ⟨hpos, heq⟩ := reduceTwo_spec 400 y 0 hy
  set r := (reduceTwo 400 y 0).1 with hr
  set k := (reduceTwo 400 y 0).2 with hk
  have hy' : (y : ℝ) = (r : ℝ) * (2 : ℝ) ^ k := by
    rw [heq]
    simp
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hpos
  have hlog : Real.log (y : ℝ) = Real.log (r : ℝ) + (k : ℝ) * Real.log 2 := by
    rw [hy', Real.log_mul hrpos.ne' (zpow_ne_zero _ (by norm_num)), Real.log_zpow]
  have hu := logUnitR_bounds hpos
  have h2 := log_two_bounds
  unfold logLoR logHiR
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

/-- `y^e ≤ U` from `e · logHiR y ≤ logLoR U`. -/
theorem rpow_le_of_logsR {y e U : ℚ} (hy : 0 < y) (hU : 0 < U) (he : 0 ≤ e)
    (h : e * logHiR y ≤ logLoR U) : (y : ℝ) ^ (e : ℝ) ≤ (U : ℝ) := by
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  have hU' : (0 : ℝ) < U := by exact_mod_cast hU
  have he' : (0 : ℝ) ≤ e := by exact_mod_cast he
  have hly := (logR_bounds hy).2
  have hlU := (logR_bounds hU).1
  have hh : ((e * logHiR y : ℚ) : ℝ) ≤ ((logLoR U : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at hh
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hy' _) hU').mp
  rw [Real.log_rpow hy']
  nlinarith [mul_le_mul_of_nonneg_left hly he']

/-- `L ≤ y^e` from `logHiR L ≤ e · logLoR y`. -/
theorem le_rpow_of_logsR {y e L : ℚ} (hy : 0 < y) (hL : 0 < L) (he : 0 ≤ e)
    (h : logHiR L ≤ e * logLoR y) : (L : ℝ) ≤ (y : ℝ) ^ (e : ℝ) := by
  have hy' : (0 : ℝ) < y := by exact_mod_cast hy
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have he' : (0 : ℝ) ≤ e := by exact_mod_cast he
  have hly := (logR_bounds hy).1
  have hlL := (logR_bounds hL).2
  have hh : ((logHiR L : ℚ) : ℝ) ≤ ((e * logLoR y : ℚ) : ℝ) := by exact_mod_cast h
  push_cast at hh
  apply (Real.log_le_log_iff hL' (Real.rpow_pos_of_pos hy' _)).mp
  rw [Real.log_rpow hy']
  nlinarith [mul_le_mul_of_nonneg_left hly he']

end UnitDistance.Sqrt241.Numerics
