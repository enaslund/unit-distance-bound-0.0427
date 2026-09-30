module

public import UnitDistance.StudentProfiles
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section
set_option backward.privateInPublic true


/-!
# Integrability of the joint reciprocal-displacement Student overlap

The convolution split uses the ordinary triangle inequality: at least one
endpoint is at distance at least half the displacement from the origin.
It gives an actual integrable envelope in the logarithmic displacement.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace UnitDistance

noncomputable def studentOverlapTail (a r t : ℝ) : ℝ :=
  (1+a*(t/2)^2)^(-r)

theorem studentWeight_nonneg {a : ℝ} (ha : 0 ≤ a) (r : ℝ) (z : ℂ) :
    0 ≤ studentWeight a r z := by unfold studentWeight; positivity

theorem studentWeight_le_one {a r : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) (z : ℂ) :
    studentWeight a r z ≤ 1 := by
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · nlinarith [mul_nonneg ha (sq_nonneg ‖z‖)]
  · linarith

theorem measurable_studentWeight (a r : ℝ) : Measurable (studentWeight a r) := by
  unfold studentWeight
  fun_prop

/-- The elementary two-endpoint convolution split, with the actual norm of
its displacement in the tail. -/
theorem student_overlap_split {a r : ℝ} (ha : 0 < a) (hr : 0 ≤ r) (z β : ℂ) :
    studentWeight a r z * studentWeight a r (z+β) ≤
      studentOverlapTail a r ‖β‖ * (studentWeight a r z + studentWeight a r (z+β)) := by
  have htail : 0 ≤ studentOverlapTail a r ‖β‖ := by unfold studentOverlapTail; positivity
  have hlarge (x : ℂ) (hx : ‖β‖/2 ≤ ‖x‖) :
      studentWeight a r x ≤ studentOverlapTail a r ‖β‖ := by
    apply Real.rpow_le_rpow_of_nonpos (by positivity : 0 < 1+a*(‖β‖/2)^2)
    · have hs := pow_le_pow_left₀ (by positivity : 0 ≤ ‖β‖/2) hx 2
      nlinarith [mul_le_mul_of_nonneg_left hs ha.le]
    · linarith
  have hz := studentWeight_nonneg ha.le r z
  have hy := studentWeight_nonneg ha.le r (z+β)
  by_cases h : ‖β‖/2 ≤ ‖z‖
  · calc
      _ ≤ studentOverlapTail a r ‖β‖ * studentWeight a r (z+β) :=
        mul_le_mul_of_nonneg_right (hlarge z h) hy
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) htail
  · have htri : ‖β‖ ≤ ‖z+β‖ + ‖z‖ := by
      simpa only [add_sub_cancel_left] using norm_sub_le (z+β) z
    have hylarge : ‖β‖/2 ≤ ‖z+β‖ := by linarith
    calc
      _ ≤ studentWeight a r z * studentOverlapTail a r ‖β‖ :=
        mul_le_mul_of_nonneg_left (hlarge (z+β) hylarge) hz
      _ ≤ _ := by nlinarith [mul_nonneg htail hy]

theorem integrable_student_overlap {a r : ℝ} (ha : 0 < a) (hr : 1 < r) (β : ℂ) :
    Integrable (fun z : ℂ => studentWeight a r z * studentWeight a r (z+β)) := by
  have hm := (measurable_studentWeight a r).mul
    ((measurable_studentWeight a r).comp (measurable_add_const β))
  apply (integrable_studentWeight ha hr).mono' hm.aestronglyMeasurable
  filter_upwards with z
  change ‖studentWeight a r z * studentWeight a r (z+β)‖ ≤ studentWeight a r z
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (studentWeight_nonneg ha.le r z) (studentWeight_nonneg ha.le r (z+β)))]
  exact mul_le_of_le_one_right (studentWeight_nonneg ha.le r z)
    (studentWeight_le_one ha.le (by linarith) (z+β))

/-- Actual spatial convolution decays at least as a Student weight in half
the displacement. Translation invariance identifies both residual integrals. -/
theorem student_convolution_le {a r : ℝ} (ha : 0 < a) (hr : 1 < r) (β : ℂ) :
    (∫ z : ℂ, studentWeight a r z * studentWeight a r (z+β)) ≤
      2 * (∫ z : ℂ, studentWeight a r z) * studentOverlapTail a r ‖β‖ := by
  have hi := integrable_studentWeight ha hr
  have hj := hi.comp_add_right β
  have hb := integral_mono (integrable_student_overlap ha hr β)
    ((hi.add hj).const_mul (studentOverlapTail a r ‖β‖))
    (student_overlap_split ha (by linarith) · β)
  rw [integral_const_mul] at hb
  simp only [Pi.add_apply] at hb
  rw [integral_add hi hj, integral_add_right_eq_self (studentWeight a r) β] at hb
  calc
    _ ≤ studentOverlapTail a r ‖β‖ * ((∫ z : ℂ, studentWeight a r z) +
        (∫ z : ℂ, studentWeight a r z)) := hb
    _ = _ := by ring

theorem studentOverlapTail_le_one {a r t : ℝ} (ha : 0 ≤ a) (hr : 0 ≤ r) :
    studentOverlapTail a r t ≤ 1 := by
  apply Real.rpow_le_one_of_one_le_of_nonpos
  · nlinarith [mul_nonneg ha (sq_nonneg (t/2))]
  · linarith

/-- Exponential decay of a Student tail along an exponential displacement. -/
theorem studentOverlapTail_exp_le {a r : ℝ} (ha : 0 < a) (hr : 0 ≤ r) (u : ℝ) :
    studentOverlapTail a r (Real.exp u) ≤ (a/4)^(-r) * Real.exp (-2*r*u) := by
  have hb : 0 < (a/4)*(Real.exp u)^2 := by positivity
  have h := Real.rpow_le_rpow_of_nonpos hb
    (show (a/4)*(Real.exp u)^2 ≤ 1+a*(Real.exp u/2)^2 by nlinarith) (by linarith : -r ≤ 0)
  rw [Real.mul_rpow (by positivity : 0 ≤ a/4) (sq_nonneg _)] at h
  have he : ((Real.exp u)^2)^(-r) = Real.exp (-2*r*u) := by
    rw [Real.rpow_def_of_pos (by positivity), Real.log_pow, Real.log_exp]
    congr 1
    ring
  rw [he] at h
  exact h

theorem reciprocal_student_tail_le {a r : ℝ} (ha : 0 < a) (hr : 0 ≤ r) (u : ℝ) :
    studentOverlapTail a r (Real.exp u) * studentOverlapTail a r (Real.exp (-u)) ≤
      (a/4)^(-r) * Real.exp (-2*r*|u|) := by
  have hnonneg (t : ℝ) : 0 ≤ studentOverlapTail a r t := by unfold studentOverlapTail; positivity
  by_cases hu : 0 ≤ u
  · rw [abs_of_nonneg hu]
    exact (mul_le_of_le_one_right (hnonneg _) (studentOverlapTail_le_one ha.le hr)).trans
      (studentOverlapTail_exp_le ha hr u)
  · rw [abs_of_nonpos (le_of_not_ge hu)]
    exact (mul_le_of_le_one_left (hnonneg _) (studentOverlapTail_le_one ha.le hr)).trans
      (studentOverlapTail_exp_le ha hr (-u))

theorem integrable_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) :
    Integrable (fun u : ℝ => Real.exp (-c*|u|)) := by
  have hp : IntegrableOn (fun u : ℝ => Real.exp (-c*|u|)) (Set.Ioi 0) := by
    apply (integrableOn_exp_mul_Ioi (by linarith : -c < 0) 0).congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    rw [abs_of_pos hu]
  have hn : IntegrableOn (fun u : ℝ => Real.exp (-c*|u|)) (Set.Iic 0) := by
    apply (integrableOn_exp_mul_Iic hc 0).congr
    filter_upwards [self_mem_ae_restrict measurableSet_Iic] with u hu
    rw [abs_of_nonpos hu]
    congr 1
    ring
  have h := hp.union hn
  simpa only [Set.Ioi_union_Iic, integrableOn_univ] using h

theorem integrable_reciprocal_student_tail {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    Integrable (fun u : ℝ =>
      studentOverlapTail a r (Real.exp u) * studentOverlapTail a r (Real.exp (-u))) := by
  have hm : Measurable (fun u : ℝ =>
      studentOverlapTail a r (Real.exp u) * studentOverlapTail a r (Real.exp (-u))) := by
    unfold studentOverlapTail
    fun_prop
  apply ((integrable_exp_neg_mul_abs (show 0 < 2*r by linarith)).const_mul ((a/4)^(-r))).mono'
    hm.aestronglyMeasurable
  filter_upwards with u
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold studentOverlapTail; positivity)]
  simpa only [neg_mul] using reciprocal_student_tail_le ha hr.le u

namespace Witness

/-- Product convolution envelope for the exact Bernstein-Student profile. -/
theorem pairProfile_overlap_integral_le (β : ℂ × ℂ) :
    (∫ z : ℂ × ℂ, pairProfile z * pairProfile (z+β)) ≤
      196 * (2 * ∫ z : ℂ, studentWeight a s z)^2 *
        (studentOverlapTail a s ‖β.1‖ * studentOverlapTail a s ‖β.2‖) := by
  have ha := witness_basic.2.1
  have hs : 1 < s := by norm_num [s]
  let g := studentWeight a s
  have hg (z : ℂ) : 0 ≤ g z := studentWeight_nonneg ha.le s z
  have hp (z : ℂ × ℂ) : pairProfile z ≤ (g z.1 * g z.2) * 14 := by
    simpa only [Real.rpow_one, mul_one] using pairProfile_rpow_le z (by norm_num : (0:ℝ)≤1)
  have hI := (integrable_student_overlap ha hs β.1).mul_prod (integrable_student_overlap ha hs β.2)
  have hpoint (z : ℂ × ℂ) : pairProfile z * pairProfile (z+β) ≤
      196*((g z.1 * g (z.1+β.1)) * (g z.2 * g (z.2+β.2))) := by
    calc
      _ ≤ ((g z.1*g z.2)*14) * ((g (z.1+β.1)*g (z.2+β.2))*14) :=
        mul_le_mul (hp z) (hp (z+β)) (pairProfile_pos (z+β)).le
          (by positivity [hg z.1, hg z.2])
      _ = _ := by ring
  have hbound := integral_mono (integrable_pairProfile_overlap β) (hI.const_mul 196) hpoint
  rw [integral_const_mul] at hbound
  have hProdInt : (∫ z : ℂ × ℂ, (g z.1 * g (z.1+β.1)) * (g z.2 * g (z.2+β.2))) =
      (∫ x : ℂ, g x * g (x+β.1)) * (∫ y : ℂ, g y * g (y+β.2)) :=
    integral_prod_mul (fun x : ℂ => g x * g (x+β.1)) (fun y : ℂ => g y * g (y+β.2))
  rw [hProdInt] at hbound
  have h1 := student_convolution_le ha hs β.1
  have h2 := student_convolution_le ha hs β.2
  have hI0 : 0 ≤ ∫ z : ℂ, g z := integral_nonneg hg
  have htail0 (t : ℝ) : 0 ≤ studentOverlapTail a s t := by unfold studentOverlapTail; positivity
  have hC2 : 0 ≤ ∫ z : ℂ, g z * g (z+β.2) :=
    integral_nonneg (fun z => mul_nonneg (hg z) (hg (z+β.2)))
  have hprod := mul_le_mul h1 h2 hC2 (mul_nonneg (by positivity : 0 ≤ 2*∫ z : ℂ, g z) (htail0 _))
  calc
    _ ≤ 196 * ((2*∫ z : ℂ, g z)*studentOverlapTail a s ‖β.1‖ *
        ((2*∫ z : ℂ, g z)*studentOverlapTail a s ‖β.2‖)) := by linarith
    _ = _ := by ring

noncomputable def reciprocalPairStep (u : ℝ) : ℂ × ℂ :=
  ((Real.exp u : ℂ), (Real.exp (-u) : ℂ))

noncomputable def pairOverlapIntegrand (w : ℝ × (ℂ × ℂ)) : ℝ :=
  pairProfile w.2 * pairProfile (w.2 + reciprocalPairStep w.1)

theorem measurable_reciprocalPairStep : Measurable reciprocalPairStep := by
  unfold reciprocalPairStep
  fun_prop

theorem measurable_pairOverlapIntegrand : Measurable pairOverlapIntegrand :=
  (measurable_pairProfile.comp measurable_snd).mul
    (measurable_pairProfile.comp (measurable_snd.add
      (measurable_reciprocalPairStep.comp measurable_fst)))

theorem pairOverlapIntegrand_pos (w : ℝ × (ℂ × ℂ)) : 0 < pairOverlapIntegrand w :=
  mul_pos (pairProfile_pos w.2) (pairProfile_pos (w.2+reciprocalPairStep w.1))

theorem pairOverlapIntegrand_integral_le (u : ℝ) :
    (∫ z : ℂ × ℂ, pairOverlapIntegrand (u,z)) ≤
      (196*(2*∫ z : ℂ, studentWeight a s z)^2) *
        (studentOverlapTail a s (Real.exp u) * studentOverlapTail a s (Real.exp (-u))) := by
  simpa only [pairOverlapIntegrand, reciprocalPairStep, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos u), abs_of_pos (Real.exp_pos (-u))] using
    pairProfile_overlap_integral_le (reciprocalPairStep u)

/-- The actual joint logarithmic-displacement/position overlap is integrable.
The proof supplies an integrable bound in u, not merely pointwise finiteness
of each spatial integral. -/
theorem integrable_pairOverlapIntegrand : Integrable pairOverlapIntegrand := by
  have hI (u : ℝ) : Integrable (fun z : ℂ × ℂ => pairOverlapIntegrand (u,z)) :=
    integrable_pairProfile_overlap (reciprocalPairStep u)
  have hmI : StronglyMeasurable (fun u : ℝ => ∫ z : ℂ × ℂ, ‖pairOverlapIntegrand (u,z)‖) :=
    measurable_pairOverlapIntegrand.norm.stronglyMeasurable.integral_prod_right'
  have houter : Integrable (fun u : ℝ => ∫ z : ℂ × ℂ, ‖pairOverlapIntegrand (u,z)‖) := by
    apply ((integrable_reciprocal_student_tail witness_basic.2.1 witness_basic.1).const_mul
      (196*(2*∫ z : ℂ, studentWeight a s z)^2)).mono' hmI.aestronglyMeasurable
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun z => norm_nonneg _))]
    have he : (∫ z : ℂ × ℂ, ‖pairOverlapIntegrand (u,z)‖) =
        ∫ z : ℂ × ℂ, pairOverlapIntegrand (u,z) := by
      apply integral_congr_ae
      filter_upwards with z
      exact Real.norm_of_nonneg (pairOverlapIntegrand_pos (u,z)).le
    rw [he]
    exact pairOverlapIntegrand_integral_le u
  exact (integrable_prod_iff measurable_pairOverlapIntegrand.aestronglyMeasurable).mpr
    ⟨Filter.Eventually.of_forall hI, houter⟩

/-- Fubini identifies the joint integral with the independently defined
manuscript overlap integral. -/
theorem pairOverlap_eq_integral : pairOverlap = ∫ w, pairOverlapIntegrand w := by
  change (∫ u : ℝ, ∫ z : ℂ × ℂ, pairOverlapIntegrand (u,z)) = ∫ w, pairOverlapIntegrand w
  exact (integral_prod pairOverlapIntegrand integrable_pairOverlapIntegrand).symm

theorem pairOverlap_pos : 0 < pairOverlap := by
  rw [pairOverlap_eq_integral]
  apply (integral_pos_iff_support_of_nonneg
    (fun w => (pairOverlapIntegrand_pos w).le) integrable_pairOverlapIntegrand).mpr
  have hs : Function.support pairOverlapIntegrand = Set.univ := by
    ext w
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (pairOverlapIntegrand_pos w).ne'
  rw [hs]
  exact Measure.measure_univ_pos.mpr (NeZero.ne _)

theorem pairEnergy_overlap_weight (w : ℝ × (ℂ × ℂ)) :
    Real.exp (-(pairEnergy w.2 + pairEnergy (w.2+reciprocalPairStep w.1))) =
      pairOverlapIntegrand w := by
  change _ = pairProfile w.2 * pairProfile (w.2+reciprocalPairStep w.1)
  calc
    _ = Real.exp (-1*pairEnergy w.2) * Real.exp (-1*pairEnergy (w.2+reciprocalPairStep w.1)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = _ := by rw [pairEnergy_weight, pairEnergy_weight, Real.rpow_one, Real.rpow_one]

theorem integrable_pairEnergy_overlap : Integrable (fun w : ℝ × (ℂ × ℂ) =>
    Real.exp (-(pairEnergy w.2 + pairEnergy (w.2+reciprocalPairStep w.1)))) := by
  simpa only [pairEnergy_overlap_weight] using integrable_pairOverlapIntegrand

theorem pairEnergy_overlap_mass :
    (∫ w : ℝ × (ℂ × ℂ), Real.exp (-(pairEnergy w.2 +
      pairEnergy (w.2+reciprocalPairStep w.1)))) = pairOverlap := by
  simp only [pairEnergy_overlap_weight, pairOverlap_eq_integral]

end Witness

end UnitDistance
