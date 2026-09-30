module

public import UnitDistance.PairOverlapBetaLogMoments
public import UnitDistance.PairOverlapStudentConstant

@[expose] public section
set_option backward.privateInPublic true


/-! Collection of the exact leading overlap term into rational contractions. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set
open scoped BigOperators
namespace UnitDistance

theorem digamma_re_add_nat {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (Complex.digamma ((x + n : ℝ) : ℂ)).re =
      (Complex.digamma (x : ℂ)).re + ∑ j ∈ Finset.range n, 1 / (x + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hxn : 0 < x + n := add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg _)
    have hd := Complex.digamma_apply_add_one ((x + n : ℝ) : ℂ) (by
      intro m hm
      have hre := congrArg Complex.re hm
      simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hre
      linarith [Nat.cast_nonneg (α := ℝ) m])
    have hc : (((x + n : ℝ) : ℂ) + 1) = ((x + (n + 1 : ℕ) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hc] at hd
    have hre := congrArg Complex.re hd
    rw [Complex.add_re, ← Complex.ofReal_inv, Complex.ofReal_re, ih] at hre
    rw [hre, Finset.sum_range_succ]
    simp only [one_div]
    ring

namespace Witness

def pairOverlapBetaLogMoment (i k : Fin 4) : ℝ :=
  (Complex.digamma ((s + (i : ℕ) : ℝ) : ℂ)).re +
    (Complex.digamma ((s + (k : ℕ) : ℝ) : ℂ)).re -
      2 * (Complex.digamma ((s + (i : ℕ) + (s + (k : ℕ)) : ℝ) : ℂ)).re

def pairOverlapLeadingMean (i j k l : Fin 4) : ℝ :=
  Real.log (1/a) - Real.eulerMascheroniConstant -
    ((Complex.digamma (pairOverlapBetaExponent i k : ℂ)).re +
      (Complex.digamma (pairOverlapBetaExponent j l : ℂ)).re) / 2 -
        (pairOverlapBetaLogMoment i k + pairOverlapBetaLogMoment j l) / 2

theorem pairOverlapBetaExponent_eq_eta (i k : Fin 4) :
    pairOverlapBetaExponent i k = (pairOverlapEtaQ : ℝ) + (i : ℕ) + (k : ℕ) := by
  unfold pairOverlapBetaExponent pairOverlapEtaQ pairOverlapSQ s
  push_cast
  ring

theorem pairOverlapShiftSum_cast (x : ℚ) (n : ℕ) :
    (pairOverlapShiftSum x n : ℝ) = ∑ j ∈ Finset.range n, 1 / ((x : ℝ) + j) := by
  unfold pairOverlapShiftSum
  push_cast
  rfl

theorem pairOverlapLeadingMean_collected (i j k l : Fin 4) :
    pairOverlapLeadingMean i j k l /
        (pairOverlapBetaExponent i k * pairOverlapBetaExponent j l) =
      (pairOverlapK0 i k : ℝ) * (pairOverlapK0 j l : ℝ) *
          (Real.log (1/a) + pairOverlapStudentConstant) +
        (pairOverlapR0 i k : ℝ) * (pairOverlapK0 j l : ℝ) +
          (pairOverlapK0 i k : ℝ) * (pairOverlapR0 j l : ℝ) := by
  have hs : 0 < s := by norm_num [s]
  have he : 0 < (pairOverlapEtaQ : ℝ) := by norm_num [pairOverlapEtaQ, pairOverlapSQ]
  have hsQ : (pairOverlapSQ : ℝ) = s := by norm_num [pairOverlapSQ, s]
  have h2 : 2*s = (pairOverlapEtaQ : ℝ) + 1 := by norm_num [pairOverlapEtaQ, pairOverlapSQ, s]
  have hsum (u v : Fin 4) : s + (u : ℕ) + (s + (v : ℕ)) =
      (pairOverlapEtaQ : ℝ) + ((u : ℕ) + (v : ℕ) + 1 : ℕ) := by
    push_cast
    linarith [h2]
  unfold pairOverlapLeadingMean pairOverlapBetaLogMoment pairOverlapStudentConstant
  simp_rw [pairOverlapBetaExponent_eq_eta]
  rw [hsum i k, hsum j l, h2]
  have hi := digamma_re_add_nat hs (i : ℕ)
  have hj := digamma_re_add_nat hs (j : ℕ)
  have hk := digamma_re_add_nat hs (k : ℕ)
  have hl := digamma_re_add_nat hs (l : ℕ)
  rw [hi, hj, hk, hl]
  have hcast (u v : Fin 4) : (pairOverlapEtaQ : ℝ) + (u : ℕ) + (v : ℕ) =
      (pairOverlapEtaQ : ℝ) + ((u : ℕ) + (v : ℕ) : ℕ) := by push_cast; ring
  rw [hcast i k, hcast j l]
  simp_rw [digamma_re_add_nat he]
  unfold pairOverlapR0 pairOverlapK0
  push_cast
  simp only [pairOverlapShiftSum_cast, hsQ, Finset.sum_range_one, Nat.cast_zero, add_zero]
  have hde := digamma_re_add_nat he 1
  norm_num at hde
  push_cast at hde
  rw [hde]
  simp only [add_sub_cancel_right]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem sum_pairOverlapLeadingMean_collected :
    (∑ i : Fin 4, ∑ j : Fin 4, ∑ k : Fin 4, ∑ l : Fin 4,
      ((pairOverlapPowerCoefficient i j : ℝ) * (pairOverlapPowerCoefficient k l : ℝ)) *
        (pairOverlapLeadingMean i j k l /
          (pairOverlapBetaExponent i k * pairOverlapBetaExponent j l))) =
      (pairOverlapB0 : ℝ) * (Real.log (1/a) + pairOverlapStudentConstant) +
        (pairOverlapV0 : ℝ) := by
  simp_rw [pairOverlapLeadingMean_collected]
  unfold pairOverlapB0 pairOverlapV0
  push_cast
  simp_rw [mul_add, Finset.sum_add_distrib, ← mul_assoc]
  simp_rw [← Finset.sum_mul]
  ring

end Witness
end UnitDistance
