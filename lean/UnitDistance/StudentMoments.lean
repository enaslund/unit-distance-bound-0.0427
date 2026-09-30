module

public import UnitDistance.StudentOverlap
public import UnitDistance.GaussianMoments
public import UnitDistance.GeometryEndpointExchange

@[expose] public section
set_option backward.privateInPublic true


/-!
# Finite second moments of the actual Student pair energy

A fractional power of the positive profile absorbs its squared logarithm.
The exact witness leaves room for a smaller Student exponent still above the
complex integrability threshold, so the proved reciprocal convolution bound
also controls the endpoint energy moments.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace UnitDistance

/-- The ordinary reciprocal overlap of a pure two-coordinate Student product. -/
noncomputable def studentPairOverlap (a r : ℝ) (w : ℝ × (ℂ × ℂ)) : ℝ :=
  (studentWeight a r w.2.1 * studentWeight a r (w.2.1 + (Real.exp w.1 : ℂ))) *
    (studentWeight a r w.2.2 * studentWeight a r (w.2.2 + (Real.exp (-w.1) : ℂ)))

theorem measurable_studentPairOverlap (a r : ℝ) : Measurable (studentPairOverlap a r) := by
  unfold studentPairOverlap studentWeight
  fun_prop

theorem studentPairOverlap_nonneg {a : ℝ} (ha : 0 ≤ a) (r : ℝ) (w : ℝ × (ℂ × ℂ)) :
    0 ≤ studentPairOverlap a r w := by
  unfold studentPairOverlap
  exact mul_nonneg (mul_nonneg (studentWeight_nonneg ha r _) (studentWeight_nonneg ha r _))
    (mul_nonneg (studentWeight_nonneg ha r _) (studentWeight_nonneg ha r _))

theorem studentPairOverlap_integral_le {a r : ℝ} (ha : 0 < a) (hr : 1 < r) (u : ℝ) :
    (∫ z : ℂ × ℂ, studentPairOverlap a r (u,z)) ≤
      (2*∫ z : ℂ, studentWeight a r z)^2 *
        (studentOverlapTail a r (Real.exp u) * studentOverlapTail a r (Real.exp (-u))) := by
  let I := ∫ z : ℂ, studentWeight a r z
  have hI : 0 ≤ I := integral_nonneg (studentWeight_nonneg ha.le r)
  have ht (t : ℝ) : 0 ≤ studentOverlapTail a r t := by unfold studentOverlapTail; positivity
  have h1 := student_convolution_le ha hr (Real.exp u : ℂ)
  have h2 := student_convolution_le ha hr (Real.exp (-u) : ℂ)
  have hc2 : 0 ≤ ∫ z : ℂ, studentWeight a r z * studentWeight a r (z+(Real.exp (-u) : ℂ)) :=
    integral_nonneg (fun z => mul_nonneg (studentWeight_nonneg ha.le r _) (studentWeight_nonneg ha.le r _))
  have hb := mul_le_mul h1 h2 hc2 (mul_nonneg (by positivity : 0 ≤ 2*I) (ht _))
  have hprod : (∫ z : ℂ × ℂ, studentPairOverlap a r (u,z)) =
      (∫ x : ℂ, studentWeight a r x * studentWeight a r (x+(Real.exp u : ℂ))) *
      (∫ y : ℂ, studentWeight a r y * studentWeight a r (y+(Real.exp (-u) : ℂ))) :=
    integral_prod_mul (fun x : ℂ => studentWeight a r x * studentWeight a r (x+(Real.exp u : ℂ)))
      (fun y : ℂ => studentWeight a r y * studentWeight a r (y+(Real.exp (-u) : ℂ)))
  rw [← hprod] at hb
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos u),
    abs_of_pos (Real.exp_pos (-u))] at hb
  calc
    _ ≤ (2*I*studentOverlapTail a r (Real.exp u)) *
        (2*I*studentOverlapTail a r (Real.exp (-u))) := hb
    _ = _ := by ring

/-- The reciprocal Student joint overlap is integrable at every exponent
strictly above one, allowing a smaller exponent for logarithmic moments. -/
theorem integrable_studentPairOverlap {a r : ℝ} (ha : 0 < a) (hr : 1 < r) :
    Integrable (studentPairOverlap a r) := by
  have hinner (u : ℝ) : Integrable (fun z : ℂ × ℂ => studentPairOverlap a r (u,z)) :=
    (integrable_student_overlap ha hr (Real.exp u : ℂ)).mul_prod
      (integrable_student_overlap ha hr (Real.exp (-u) : ℂ))
  have hm := measurable_studentPairOverlap a r
  have hmI : StronglyMeasurable (fun u : ℝ => ∫ z : ℂ × ℂ, ‖studentPairOverlap a r (u,z)‖) :=
    hm.norm.stronglyMeasurable.integral_prod_right'
  have houter : Integrable (fun u : ℝ => ∫ z : ℂ × ℂ, ‖studentPairOverlap a r (u,z)‖) := by
    apply ((integrable_reciprocal_student_tail ha (by linarith)).const_mul
      ((2*∫ z : ℂ, studentWeight a r z)^2)).mono' hmI.aestronglyMeasurable
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun z => norm_nonneg _))]
    have he : (∫ z : ℂ × ℂ, ‖studentPairOverlap a r (u,z)‖) =
        ∫ z : ℂ × ℂ, studentPairOverlap a r (u,z) := by
      apply integral_congr_ae
      filter_upwards with z
      exact Real.norm_of_nonneg (studentPairOverlap_nonneg ha.le r (u,z))
    rw [he]
    exact studentPairOverlap_integral_le ha hr u
  exact (integrable_prod_iff hm.aestronglyMeasurable).mpr
    ⟨Filter.Eventually.of_forall hinner, houter⟩

/-- A bounded positive profile absorbs its squared logarithm into any
strictly smaller nonnegative power. The displayed constant is explicit;
no asymptotic decay assertion is supplied as an input. -/
theorem log_square_mul_le_fractional {x q : ℝ} (hx : 0 < x) (hx14 : x ≤ 14)
    (hq0 : 0 ≤ q) (hq1 : q < 1) :
    (-Real.log x)^2 * x ≤ (2744+2/(1-q)^2) * x^q := by
  have hη : 0 < 1-q := by linarith
  have hη2 : 0 < (1-q)^2 := sq_pos_of_pos hη
  have hxq : 0 < x^q := Real.rpow_pos_of_pos hx q
  by_cases hx1 : x ≤ 1
  · have hE : 0 ≤ -Real.log x := neg_nonneg.mpr (Real.log_nonpos hx.le hx1)
    have hpow := Real.pow_div_factorial_le_exp ((1-q)*(-Real.log x))
      (mul_nonneg hη.le hE) 2
    norm_num at hpow
    have he : Real.exp ((1-q)*(-Real.log x)) * x = x^q := by
      calc
        _ = Real.exp ((1-q)*(-Real.log x)) * Real.exp (Real.log x) := by
          rw [Real.exp_log hx]
        _ = Real.exp (Real.log x*q) := by rw [← Real.exp_add]; congr 1; ring
        _ = x^q := (Real.rpow_def_of_pos hx q).symm
    simp only [mul_neg] at he
    have hm := mul_le_mul_of_nonneg_right hpow hx.le
    have hb : (-Real.log x)^2*x ≤ (2*x^q)/(1-q)^2 := by
      apply (le_div_iff₀ hη2).mpr
      rw [← he]
      nlinarith
    calc
      _ ≤ (2*x^q)/(1-q)^2 := hb
      _ = (2/(1-q)^2)*x^q := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hxq.le
  · have h1 : 1 ≤ x := le_of_not_ge hx1
    have hl0 := Real.log_nonneg h1
    have hl14 : Real.log x ≤ 14 := by linarith [Real.log_le_sub_one_of_pos hx]
    have hlsq := pow_le_pow_left₀ hl0 hl14 2
    have hb : (-Real.log x)^2*x ≤ (196:ℝ)*14 := by
      rw [neg_sq]
      exact mul_le_mul (by norm_num at hlsq ⊢; exact hlsq) hx14 hx.le (by norm_num)
    have hC : 0 ≤ 2744+2/(1-q)^2 := by positivity
    have hxq1 : 1 ≤ x^q := Real.one_le_rpow h1 hq0
    calc
      _ ≤ (196:ℝ)*14 := hb
      _ ≤ 2744+2/(1-q)^2 := by
        have : 0 ≤ 2/(1-q)^2 := by positivity
        linarith
      _ ≤ _ := le_mul_of_one_le_right hC hxq1

/-- The same smaller power absorbs a bounded positive profile itself. -/
theorem bounded_profile_le_fractional {x q : ℝ} (hx : 0 < x) (hx14 : x ≤ 14)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : x ≤ 14*x^q := by
  by_cases hx1 : x ≤ 1
  · have h : x ≤ x^q := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hx hx1 hq1
    exact h.trans (by nlinarith [Real.rpow_nonneg hx.le q])
  · have h := Real.one_le_rpow (le_of_not_ge hx1) hq0
    linarith

namespace Witness

/-- A rational exponent strictly between the Student threshold and one. -/
noncomputable def momentPower : ℝ := (s+1)/(2*s)

theorem momentPower_bounds : 0 ≤ momentPower ∧ momentPower < 1 ∧ 1 < s*momentPower := by
  norm_num [momentPower, s]

noncomputable def pairMomentConstant : ℝ :=
  14*(2744+2/(1-momentPower)^2)*(14^momentPower)^2

/-- A pointwise estimate for the actual logarithmic energy, retaining the
actual reciprocal displacement and replacing only the decay exponent. -/
theorem pair_first_energy_sq_bound (w : ℝ × (ℂ × ℂ)) :
    (pairEnergy w.2)^2 * pairOverlapIntegrand w ≤
      pairMomentConstant * studentPairOverlap a (s*momentPower) w := by
  let x := pairProfile w.2
  let y := pairProfile (w.2+reciprocalPairStep w.1)
  let q := momentPower
  let C := 2744+2/(1-q)^2
  have hx : 0 < x := pairProfile_pos _
  have hy : 0 < y := pairProfile_pos _
  have hq0 : 0 ≤ q := momentPower_bounds.1
  have hq1 : q < 1 := momentPower_bounds.2.1
  have hlog := log_square_mul_le_fractional hx (pairProfile_le_fourteen _) hq0 hq1
  have hyfrac := bounded_profile_le_fractional hy (pairProfile_le_fourteen _) hq0 hq1.le
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hxy := mul_le_mul hlog hyfrac hy.le (mul_nonneg hC (Real.rpow_nonneg hx.le q))
  have hxg := pairProfile_rpow_le w.2 hq0
  have hyg := pairProfile_rpow_le (w.2+reciprocalPairStep w.1) hq0
  have hg (z : ℂ) : 0 ≤ studentWeight a (s*q) z := studentWeight_nonneg witness_basic.2.1.le _ _
  have hprod := mul_le_mul hxg hyg (Real.rpow_nonneg hy.le q)
    (mul_nonneg (mul_nonneg (hg _) (hg _)) (by positivity : 0 ≤ (14:ℝ)^q))
  have hcoeff : 0 ≤ 14*C := mul_nonneg (by norm_num) hC
  calc
    (pairEnergy w.2)^2 * pairOverlapIntegrand w = (-Real.log x)^2*x*y := by
      simp only [pairEnergy, pairOverlapIntegrand, x, y]
      ring
    _ ≤ (C*x^q)*(14*y^q) := hxy
    _ = (14*C)*(x^q*y^q) := by ring
    _ ≤ (14*C)*(((studentWeight a (s*q) w.2.1 * studentWeight a (s*q) w.2.2)*14^q)*
        ((studentWeight a (s*q) (w.2+reciprocalPairStep w.1).1 *
          studentWeight a (s*q) (w.2+reciprocalPairStep w.1).2)*14^q)) :=
      mul_le_mul_of_nonneg_left hprod hcoeff
    _ = pairMomentConstant * studentPairOverlap a (s*momentPower) w := by
      dsimp [pairMomentConstant, studentPairOverlap, reciprocalPairStep, q, C]
      ring

/-- The first endpoint has finite unnormalized second energy moment over
both logarithmic displacement and the two complex coordinates. -/
theorem integrable_pair_first_energy_sq_weight : Integrable (fun w : ℝ × (ℂ × ℂ) =>
    (pairEnergy w.2)^2 * pairOverlapIntegrand w) := by
  have hm : Measurable (fun w : ℝ × (ℂ × ℂ) =>
      (pairEnergy w.2)^2 * pairOverlapIntegrand w) :=
    ((measurable_pairEnergy.comp measurable_snd).pow_const 2).mul measurable_pairOverlapIntegrand
  apply ((integrable_studentPairOverlap witness_basic.2.1 momentPower_bounds.2.2).const_mul
    pairMomentConstant).mono' hm.aestronglyMeasurable
  filter_upwards with w
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (sq_nonneg _) (pairOverlapIntegrand_pos w).le)]
  exact pair_first_energy_sq_bound w

/-- The normalized actual pair overlap probability law. -/
noncomputable def pairOverlapLaw : Measure (ℝ × (ℂ × ℂ)) :=
  overlapLaw volume (fun w => pairEnergy w.2)
    (fun w => pairEnergy (w.2+reciprocalPairStep w.1)) pairOverlap

theorem pair_first_endpoint_memLp :
    MemLp (fun w : ℝ × (ℂ × ℂ) => pairEnergy w.2) 2 pairOverlapLaw := by
  have hm : Measurable (fun w : ℝ × (ℂ × ℂ) => pairEnergy w.2) :=
    measurable_pairEnergy.comp measurable_snd
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  have hlaw : pairOverlapLaw = (volume : Measure (ℝ × (ℂ × ℂ))).withDensity
      (fun w => ENNReal.ofReal (pairOverlapIntegrand w/pairOverlap)) := by
    unfold pairOverlapLaw overlapLaw
    simp only [pairEnergy_overlap_weight]
  rw [hlaw, integrable_withDensity_iff_integrable_smul'
    (show Measurable (fun w => ENNReal.ofReal (pairOverlapIntegrand w/pairOverlap)) from
      (measurable_pairOverlapIntegrand.div_const pairOverlap).ennreal_ofReal)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [smul_eq_mul]
  apply (integrable_pair_first_energy_sq_weight.div_const pairOverlap).congr
  filter_upwards with w
  rw [ENNReal.toReal_ofReal (div_nonneg (pairOverlapIntegrand_pos w).le pairOverlap_pos.le)]
  ring

/-- The normalization uses the independently defined actual overlap integral. -/
theorem pairOverlapLaw_probability : IsProbabilityMeasure pairOverlapLaw :=
  overlapLaw_probability volume _ _ pairOverlap_pos
    integrable_pairEnergy_overlap pairEnergy_overlap_mass

/-- Both actual endpoint energies have finite second moments, and their
means and variances agree by the explicit Haar-preserving reflection. -/
theorem pair_endpoint_moments :
    MemLp (fun w : ℝ × (ℂ × ℂ) => pairEnergy w.2) 2 pairOverlapLaw ∧
    MemLp (fun w : ℝ × (ℂ × ℂ) => pairEnergy (w.2+reciprocalPairStep w.1)) 2 pairOverlapLaw ∧
    (∫ w, pairEnergy (w.2+reciprocalPairStep w.1) ∂pairOverlapLaw) =
      (∫ w, pairEnergy w.2 ∂pairOverlapLaw) ∧
    ProbabilityTheory.variance (fun w => pairEnergy (w.2+reciprocalPairStep w.1)) pairOverlapLaw =
      ProbabilityTheory.variance (fun w => pairEnergy w.2) pairOverlapLaw := by
  have hstep : Measurable reciprocalPairStep := by unfold reciprocalPairStep; fun_prop
  have hm : supportedOverlapMeasure (volume : Measure ℝ) (volume : Measure (ℂ × ℂ))
      reciprocalPairStep Set.univ = volume := by
    simp [supportedOverlapMeasure, ← Measure.volume_eq_prod]
  letI : (volume : Measure (ℂ × ℂ)).IsAddLeftInvariant := by
    rw [Measure.volume_eq_prod]
    infer_instance
  letI : (volume : Measure (ℂ × ℂ)).IsNegInvariant := by
    constructor
    exact ((Measure.measurePreserving_neg (volume : Measure ℂ)).prod
      (Measure.measurePreserving_neg (volume : Measure ℂ))).map_eq
  have h := even_supported_endpoint_moments (volume : Measure ℝ)
    (volume : Measure (ℂ × ℂ)) reciprocalPairStep hstep Set.univ MeasurableSet.univ
    (by simp) pairEnergy pairEnergy_neg pairOverlap
  simp only [hm, firstEnergy, secondEnergy] at h
  exact ⟨pair_first_endpoint_memLp, h pair_first_endpoint_memLp⟩

end Witness
end UnitDistance
