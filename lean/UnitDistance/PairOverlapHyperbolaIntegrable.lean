module

public import UnitDistance.PairOverlapHyperbola

@[expose] public section
set_option backward.privateInPublic true


/-! Integrability and positivity of the hyperbola kernel. -/

noncomputable section
open MeasureTheory
namespace UnitDistance

theorem pairHyperbolaIntegrand_nonneg {A B b u : ℝ} (hb : 0 ≤ b) :
    0 ≤ pairHyperbolaIntegrand A B b u := by
  unfold pairHyperbolaIntegrand
  positivity

theorem pairHyperbolaIntegrand_eq_studentTail (A b u : ℝ) :
    pairHyperbolaIntegrand A A b u =
      studentOverlapTail (4*b) A (Real.exp u) *
        studentOverlapTail (4*b) A (Real.exp (-u)) := by
  unfold pairHyperbolaIntegrand studentOverlapTail
  have hp : 1 + b * Real.exp (2*u) = 1 + 4*b*(Real.exp u/2)^2 := by
    rw [show Real.exp (2*u) = Real.exp u ^ 2 by
      simpa using Real.exp_nat_mul u 2]
    ring
  have hn : 1 + b * Real.exp (-2*u) = 1 + 4*b*(Real.exp (-u)/2)^2 := by
    rw [show Real.exp (-2*u) = Real.exp (-u) ^ 2 by
      convert Real.exp_nat_mul (-u) 2 using 1 <;> congr 1 <;> ring]
    ring
  rw [hp, hn]

theorem integrable_pairHyperbolaIntegrand {A B b : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hb : 0 < b) :
    Integrable (pairHyperbolaIntegrand A B b) := by
  have hm : 0 < min A B := lt_min hA hB
  have hI : Integrable (pairHyperbolaIntegrand (min A B) (min A B) b) := by
    apply (integrable_reciprocal_student_tail (a := 4*b) (by positivity) hm).congr
    filter_upwards with u
    exact (pairHyperbolaIntegrand_eq_studentTail (min A B) b u).symm
  have hmeas : Measurable (pairHyperbolaIntegrand A B b) := by
    unfold pairHyperbolaIntegrand
    fun_prop
  apply hI.mono' hmeas.aestronglyMeasurable
  filter_upwards with u
  rw [Real.norm_eq_abs, abs_of_nonneg (pairHyperbolaIntegrand_nonneg hb.le)]
  unfold pairHyperbolaIntegrand
  have hbase (v : ℝ) : 1 ≤ 1 + b * Real.exp v :=
    le_add_of_nonneg_right (by positivity)
  apply mul_le_mul
  · exact Real.rpow_le_rpow_of_exponent_le (hbase _) (neg_le_neg (min_le_left _ _))
  · exact Real.rpow_le_rpow_of_exponent_le (hbase _) (neg_le_neg (min_le_right _ _))
  · positivity
  · positivity

theorem pairHyperbola_nonneg {A B b : ℝ} (hb : 0 ≤ b) :
    0 ≤ pairHyperbola A B b :=
  integral_nonneg (fun _ => pairHyperbolaIntegrand_nonneg hb)

theorem integrable_reciprocal_powers {A B X Y : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hX : 0 < X) (hY : 0 < Y) :
    Integrable (fun u : ℝ => (1 + X * Real.exp (2*u)) ^ (-A) *
      (1 + Y * Real.exp (-2*u)) ^ (-B)) := by
  let c : ℝ := (Real.log Y - Real.log X) / 4
  have hi := (integrable_pairHyperbolaIntegrand hA hB
    (pairHyperbolaMean_pos X Y)).comp_add_right (-c)
  apply hi.congr
  filter_upwards with u
  unfold pairHyperbolaIntegrand pairHyperbolaMean c
  have hx : Real.exp ((Real.log X + Real.log Y)/2) *
      Real.exp (2*(u + -((Real.log Y - Real.log X)/4))) = X * Real.exp (2*u) := by
    rw [← Real.exp_add, show (Real.log X + Real.log Y)/2 +
      2*(u + -((Real.log Y - Real.log X)/4)) = Real.log X + 2*u by ring,
      Real.exp_add, Real.exp_log hX]
  have hy : Real.exp ((Real.log X + Real.log Y)/2) *
      Real.exp (-2*(u + -((Real.log Y - Real.log X)/4))) = Y * Real.exp (-2*u) := by
    rw [← Real.exp_add, show (Real.log X + Real.log Y)/2 +
      -2*(u + -((Real.log Y - Real.log X)/4)) = Real.log Y + -2*u by ring,
      Real.exp_add, Real.exp_log hY]
  rw [hx, hy]

end UnitDistance
