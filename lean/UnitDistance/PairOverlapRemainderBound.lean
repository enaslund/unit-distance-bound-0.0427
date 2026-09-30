module

public import UnitDistance.PairOverlapHyperbolaLeading
public import UnitDistance.PairOverlapBetaHyperbola
public import UnitDistance.PairOverlapBetaLogMoments
public import UnitDistance.PairOverlapExpansion
public import UnitDistance.LogBounds
public import UnitDistance.PairOverlapLeadingBetaIntegral

@[expose] public section
set_option backward.privateInPublic true


/-! Uniform integration of the elementary pair-hyperbola remainder. -/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped BigOperators

namespace UnitDistance.Witness

private def pairOverlapSmallLogQuadratic (x : ℝ) : ℝ :=
  -(x^2 * Real.log x)

private theorem pairOverlapSmallLogQuadratic_monotone :
    MonotoneOn pairOverlapSmallLogQuadratic (Ioc (0:ℝ) (1/4)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 (1/4))
  · intro x hx
    unfold pairOverlapSmallLogQuadratic
    exact ContinuousAt.continuousWithinAt
      (((continuousAt_id.pow 2).mul (Real.continuousAt_log hx.1.ne')).neg)
  · rw [interior_Ioc]
    intro x hx
    unfold pairOverlapSmallLogQuadratic
    exact (((hasDerivAt_pow 2 x).mul
      (Real.hasDerivAt_log hx.1.ne')).neg).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ioc] at hx
    have hd := (((hasDerivAt_pow 2 x).mul
      (Real.hasDerivAt_log hx.1.ne')).neg)
    have hderiv : deriv pairOverlapSmallLogQuadratic x =
        -(2 * x ^ (2-1) * Real.log x + x^2 * x⁻¹) := by
      change deriv (fun x : ℝ => -(x^2 * Real.log x)) x = _
      exact hd.deriv
    rw [hderiv]
    have hlog4 : (1/2:ℝ) ≤ Real.log 4 := by
      have h := Real.le_log_one_add_of_nonneg (show (0:ℝ) ≤ 3 by norm_num)
      norm_num at h ⊢
      linarith
    have hlogx : Real.log x ≤ -(1/2:ℝ) := by
      have h := Real.log_le_log hx.1 (by simpa using hx.2.le)
      rw [Real.log_inv] at h
      linarith
    have hx0 : 0 ≤ x := hx.1.le
    rw [show (2:ℕ) - 1 = 1 by norm_num, pow_one]
    have hcancel : x^2 * x⁻¹ = x := by field_simp [hx.1.ne']
    rw [hcancel]
    nlinarith

private theorem pairOverlapSmallLogQuadratic_eq {x : ℝ} (hx : 0 < x) :
    pairOverlapSmallLogQuadratic x = x^2 * Real.log (1/x) := by
  unfold pairOverlapSmallLogQuadratic
  rw [one_div, Real.log_inv]
  ring

private theorem pairOverlap_log_a_coarse_lower :
    (-23:ℝ)/2 ≤ Real.log a := by
  let q : ℝ := 257266483516 / 152587890625
  have hqpos : 0 < q := by norm_num [q]
  have hq15 : (3:ℝ)/2 ≤ q := by norm_num [q]
  have hlog15 : (2:ℝ)/5 ≤ Real.log ((3:ℝ)/2) := by
    have h := Real.le_log_one_add_of_nonneg (show (0:ℝ) ≤ 1/2 by norm_num)
    norm_num at h ⊢
    linarith
  have hlogq : (2:ℝ)/5 ≤ Real.log q :=
    hlog15.trans (Real.log_le_log (by norm_num) hq15)
  have h2 := UnitDistance.log_two_precise.2
  simp only [div_one] at h2
  have hs := log_scale_two a q (-17)
    (by norm_num) (by norm_num [a, q])
  rw [hs]
  norm_num at h2 ⊢
  linarith

theorem pairOverlap_log_four_div_a_upper :
    Real.log (4/a) ≤ 13 := by
  have ha := witness_basic.2.1
  have h2 := UnitDistance.log_two_precise.2
  simp only [div_one] at h2
  rw [Real.log_div (by norm_num) ha.ne', show (4:ℝ) = 2^2 by norm_num,
    Real.log_pow]
  norm_num at h2 ⊢
  linarith [pairOverlap_log_a_coarse_lower]

theorem pairOverlap_a_quarter_sq_upper :
    (a/4)^2 ≤ (105:ℝ)/10^13 := by
  norm_num [a]

/-- The beta-dependent hyperbola scale lies in `(0, a/4]` on the open square. -/
theorem pairOverlap_betaScale_pos_le_quarter
    {t v : ℝ} (ht : t ∈ Ioo (0:ℝ) 1) (hv : v ∈ Ioo (0:ℝ) 1) :
    0 < a * Real.sqrt (t*(1-t)*v*(1-v)) ∧
      a * Real.sqrt (t*(1-t)*v*(1-v)) ≤ a/4 := by
  have ha := witness_basic.2.1
  have ht0 : 0 < t*(1-t) := mul_pos ht.1 (sub_pos.mpr ht.2)
  have hv0 : 0 < v*(1-v) := mul_pos hv.1 (sub_pos.mpr hv.2)
  have ht4 : t*(1-t) ≤ (1:ℝ)/4 := by nlinarith [sq_nonneg (t-1/2)]
  have hv4 : v*(1-v) ≤ (1:ℝ)/4 := by nlinarith [sq_nonneg (v-1/2)]
  have hp0 : 0 < t*(1-t)*v*(1-v) := by
    positivity [ht.1, sub_pos.mpr ht.2, hv.1, sub_pos.mpr hv.2]
  have hp4 : t*(1-t)*v*(1-v) ≤ (1:ℝ)/16 := by
    nlinarith [mul_le_mul ht4 hv4 hv0.le (by norm_num : (0:ℝ) ≤ 1/4)]
  have hs4 : Real.sqrt (t*(1-t)*v*(1-v)) ≤ (1:ℝ)/4 := by
    rw [Real.sqrt_le_iff]
    constructor
    · norm_num
    · nlinarith
  constructor
  · exact mul_pos ha (Real.sqrt_pos.2 hp0)
  · exact (mul_le_mul_of_nonneg_left hs4 ha.le).trans_eq (by ring)

private theorem pairOverlap_betaExponent_one_le (i k : Fin 4) :
    1 ≤ pairOverlapBetaExponent i k := by
  unfold pairOverlapBetaExponent
  have hi : (0:ℝ) ≤ (i:ℕ) := Nat.cast_nonneg _
  have hk : (0:ℝ) ≤ (k:ℕ) := Nat.cast_nonneg _
  norm_num [s] at ⊢
  linarith

private theorem pairOverlap_small_log_bound {b : ℝ}
    (hb : 0 < b) (hba : b ≤ a/4) :
    b^2 * Real.log (1/b) ≤ (a/4)^2 * 13 := by
  have ha := witness_basic.2.1
  have ha1 : a ≤ 1 := by norm_num [a]
  have hbmem : b ∈ Ioc (0:ℝ) (1/4) :=
    ⟨hb, hba.trans (div_le_div_of_nonneg_right ha1 (by norm_num))⟩
  have hamem : a/4 ∈ Ioc (0:ℝ) (1/4) :=
    ⟨div_pos ha (by norm_num), div_le_div_of_nonneg_right ha1 (by norm_num)⟩
  have hmono := pairOverlapSmallLogQuadratic_monotone hbmem hamem hba
  rw [pairOverlapSmallLogQuadratic_eq hb,
    pairOverlapSmallLogQuadratic_eq (div_pos ha (by norm_num))] at hmono
  have hlog : Real.log (1/(a/4)) ≤ 13 := by
    convert pairOverlap_log_four_div_a_upper using 1 <;>
      field_simp [ha.ne'] <;> ring
  have hsq : 0 ≤ (a/4)^2 := sq_nonneg _
  exact hmono.trans (mul_le_mul_of_nonneg_left hlog hsq)

/-- After division by the two beta exponents, every pointwise hyperbola
remainder in the actual four-index family is below `1.47e-10`. -/
theorem pairOverlap_betaRemainder_normalized_le
    (i j k l : Fin 4) {t v : ℝ}
    (ht : t ∈ Ioo (0:ℝ) 1) (hv : v ∈ Ioo (0:ℝ) 1) :
    pairHyperbolaRemainder (pairOverlapBetaExponent i k)
        (pairOverlapBetaExponent j l)
        (a * Real.sqrt (t*(1-t)*v*(1-v))) /
      (pairOverlapBetaExponent i k * pairOverlapBetaExponent j l) ≤
        (147:ℝ)/10^12 := by
  let A := pairOverlapBetaExponent i k
  let B := pairOverlapBetaExponent j l
  let b := a * Real.sqrt (t*(1-t)*v*(1-v))
  have hA : 0 < A := pairOverlapBetaExponent_pos i k
  have hB : 0 < B := pairOverlapBetaExponent_pos j l
  have hA1 : 1 ≤ A := pairOverlap_betaExponent_one_le i k
  have hB1 : 1 ≤ B := pairOverlap_betaExponent_one_le j l
  have hb := pairOverlap_betaScale_pos_le_quarter ht hv
  have hb1 : b ≤ 1 := hb.2.trans (by norm_num [a])
  have hrem := (pairHyperbolaRemainder_nonneg_le hA.le hB.le hb.1 hb1).2
  have hdiv : pairHyperbolaRemainder A B b / (A*B) ≤
      b^2 * (Real.log (1/b) + (1/(2*A) + 1/(2*B))) := by
    apply (div_le_iff₀ (mul_pos hA hB)).2
    calc
      pairHyperbolaRemainder A B b ≤
          b^2 * (A*B*Real.log (1/b) + (A+B)/2) := hrem
      _ = (b^2 * (Real.log (1/b) + (1/(2*A) + 1/(2*B)))) *
          (A*B) := by field_simp [hA.ne', hB.ne']; ring
  have hrecA : 1/(2*A) ≤ (1:ℝ)/2 := by
    rw [div_le_iff₀ (by positivity : 0 < 2*A)]
    nlinarith
  have hrecB : 1/(2*B) ≤ (1:ℝ)/2 := by
    rw [div_le_iff₀ (by positivity : 0 < 2*B)]
    nlinarith
  have hblog := pairOverlap_small_log_bound hb.1 hb.2
  have hb2 : b^2 ≤ (a/4)^2 := by nlinarith [sq_nonneg ((a/4)-b)]
  have hnonlog : b^2 * (1/(2*A) + 1/(2*B)) ≤ (a/4)^2 := by
    have hs : 1/(2*A) + 1/(2*B) ≤ 1 := by linarith
    have hs0 : 0 ≤ 1/(2*A) + 1/(2*B) := by positivity
    exact (mul_le_mul hb2 hs hs0 (sq_nonneg _)).trans_eq (mul_one _)
  calc
    pairHyperbolaRemainder A B b / (A*B) ≤
        b^2 * (Real.log (1/b) + (1/(2*A) + 1/(2*B))) := hdiv
    _ = b^2*Real.log (1/b) + b^2*(1/(2*A) + 1/(2*B)) := by ring
    _ ≤ (a/4)^2*13 + (a/4)^2 := add_le_add hblog hnonlog
    _ ≤ (147:ℝ)/10^12 := by
      nlinarith [pairOverlap_a_quarter_sq_upper]

def pairOverlapBetaLeadingKernel (i j k l : Fin 4) (tv : ℝ × ℝ) : ℝ :=
  pairOverlapBetaDensity i k tv.1 * pairOverlapBetaDensity j l tv.2 *
    pairHyperbolaLeading (pairOverlapBetaExponent i k) (pairOverlapBetaExponent j l)
      (a * Real.sqrt (tv.1*(1-tv.1)*tv.2*(1-tv.2)))

theorem integrable_pairOverlapBetaLeadingKernel (i j k l : Fin 4) :
    Integrable (pairOverlapBetaLeadingKernel i j k l) pairOverlapBetaSquareMeasure := by
  let μ : Measure ℝ := volume.restrict (Ioo (0:ℝ) 1)
  let C : ℝ := Real.log (1/a) - Real.eulerMascheroniConstant -
    ((Complex.digamma (pairOverlapBetaExponent i k : ℂ)).re +
      (Complex.digamma (pairOverlapBetaExponent j l : ℂ)).re)/2
  have hi : Integrable (pairOverlapBetaDensity i k) μ :=
    integrableOn_pairOverlapBetaDensity i k
  have hj : Integrable (pairOverlapBetaDensity j l) μ :=
    integrableOn_pairOverlapBetaDensity j l
  have hli : Integrable
      (fun t => pairOverlapBetaDensity i k t * Real.log (t*(1-t))) μ :=
    integrableOn_pairOverlapBetaDensity_mul_log_product i k
  have hlj : Integrable
      (fun v => pairOverlapBetaDensity j l v * Real.log (v*(1-v))) μ :=
    integrableOn_pairOverlapBetaDensity_mul_log_product j l
  have hconst := (hi.mul_prod hj).const_mul C
  have hleft := (hli.mul_prod hj).const_mul (-(1:ℝ)/2)
  have hright := (hi.mul_prod hlj).const_mul (-(1:ℝ)/2)
  have haffine : Integrable (fun tv : ℝ×ℝ =>
      pairOverlapBetaDensity i k tv.1 * pairOverlapBetaDensity j l tv.2 *
        (C + (-1/2)*Real.log (tv.1*(1-tv.1)) +
          (-1/2)*Real.log (tv.2*(1-tv.2)))) (μ.prod μ) := by
    apply (hconst.add hleft |>.add hright).congr
    filter_upwards with tv
    simp only [Pi.add_apply]
    ring
  have hA := pairOverlapBetaExponent_pos i k
  have hB := pairOverlapBetaExponent_pos j l
  unfold pairOverlapBetaSquareMeasure
  apply haffine.congr
  have hp : ∀ᵐ tv ∂(μ.prod μ), tv ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1 := by
    dsimp [μ]
    rw [Measure.prod_restrict]
    exact self_mem_ae_restrict (measurableSet_Ioo.prod measurableSet_Ioo)
  filter_upwards [hp] with tv htv
  unfold pairOverlapBetaLeadingKernel
  have hb := pairOverlap_betaScale_pos_le_one htv.1 htv.2
  rw [pairHyperbolaLeading_eq_log_digamma hA hB hb.1 hb.2,
    log_inverse_beta_scale htv.1 htv.2, Complex.digamma_one]
  dsimp [C]
  ring

def pairOverlapBetaNormalizedRemainderKernel
    (i j k l : Fin 4) (tv : ℝ × ℝ) : ℝ :=
  pairOverlapBetaDensity i k tv.1 * pairOverlapBetaDensity j l tv.2 *
    (pairHyperbolaRemainder (pairOverlapBetaExponent i k)
        (pairOverlapBetaExponent j l)
        (a * Real.sqrt (tv.1*(1-tv.1)*tv.2*(1-tv.2))) /
      (pairOverlapBetaExponent i k * pairOverlapBetaExponent j l))

theorem integrable_pairOverlapBetaNormalizedRemainderKernel
    (i j k l : Fin 4) :
    Integrable (pairOverlapBetaNormalizedRemainderKernel i j k l)
      pairOverlapBetaSquareMeasure := by
  have hactual := integrable_pairOverlapBetaHyperbolaKernel i j k l
  have hleading := integrable_pairOverlapBetaLeadingKernel i j k l
  have hdiff := hactual.sub hleading
  let A := pairOverlapBetaExponent i k
  let B := pairOverlapBetaExponent j l
  have hscaled := hdiff.const_mul (1/(A*B))
  apply hscaled.congr
  have hp : ∀ᵐ tv ∂pairOverlapBetaSquareMeasure,
      tv ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1 := by
    unfold pairOverlapBetaSquareMeasure
    rw [Measure.prod_restrict]
    exact self_mem_ae_restrict (measurableSet_Ioo.prod measurableSet_Ioo)
  filter_upwards [hp] with tv htv
  have hA : 0 < A := pairOverlapBetaExponent_pos i k
  have hB : 0 < B := pairOverlapBetaExponent_pos j l
  have hb := pairOverlap_betaScale_pos_le_one htv.1 htv.2
  unfold pairOverlapBetaHyperbolaKernel pairOverlapBetaLeadingKernel
    pairOverlapBetaNormalizedRemainderKernel
  dsimp only [A, B]
  simp only [Pi.sub_apply]
  rw [pairHyperbola_eq_leading_add_remainder hA hB hb.1 hb.2]
  field_simp [hA.ne', hB.ne']
  ring

def pairOverlapRemainderMean (i j k l : Fin 4) : ℝ :=
  ∫ tv : ℝ × ℝ, pairOverlapBetaNormalizedRemainderKernel i j k l tv
    ∂pairOverlapBetaSquareMeasure

/-- Every normalized monomial remainder lies in `[0, 1.47e-10]`. -/
theorem pairOverlapRemainderMean_nonneg_le (i j k l : Fin 4) :
    0 ≤ pairOverlapRemainderMean i j k l ∧
      pairOverlapRemainderMean i j k l ≤ (147:ℝ)/10^12 := by
  let μ : Measure ℝ := volume.restrict (Ioo (0:ℝ) 1)
  let ε : ℝ := 147/10^12
  have hrem := integrable_pairOverlapBetaNormalizedRemainderKernel i j k l
  have hi : Integrable (pairOverlapBetaDensity i k) μ :=
    integrableOn_pairOverlapBetaDensity i k
  have hj : Integrable (pairOverlapBetaDensity j l) μ :=
    integrableOn_pairOverlapBetaDensity j l
  have hmajorant : Integrable (fun tv : ℝ×ℝ =>
      ε * (pairOverlapBetaDensity i k tv.1 * pairOverlapBetaDensity j l tv.2))
      pairOverlapBetaSquareMeasure := by
    unfold pairOverlapBetaSquareMeasure
    exact (hi.mul_prod hj).const_mul ε
  have hp : ∀ᵐ tv ∂pairOverlapBetaSquareMeasure,
      tv ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (0:ℝ) 1 := by
    unfold pairOverlapBetaSquareMeasure
    rw [Measure.prod_restrict]
    exact self_mem_ae_restrict (measurableSet_Ioo.prod measurableSet_Ioo)
  have hnonneg : ∀ᵐ tv ∂pairOverlapBetaSquareMeasure,
      0 ≤ pairOverlapBetaNormalizedRemainderKernel i j k l tv := by
    filter_upwards [hp] with tv htv
    unfold pairOverlapBetaNormalizedRemainderKernel
    have hd1 := pairOverlapBetaDensity_nonneg i k htv.1
    have hd2 := pairOverlapBetaDensity_nonneg j l htv.2
    have hA := pairOverlapBetaExponent_pos i k
    have hB := pairOverlapBetaExponent_pos j l
    have hb := pairOverlap_betaScale_pos_le_one htv.1 htv.2
    exact mul_nonneg (mul_nonneg hd1 hd2)
      (div_nonneg (pairHyperbolaRemainder_nonneg_le hA.le hB.le hb.1 hb.2).1
        (mul_nonneg hA.le hB.le))
  have hle : ∀ᵐ tv ∂pairOverlapBetaSquareMeasure,
      pairOverlapBetaNormalizedRemainderKernel i j k l tv ≤
        ε * (pairOverlapBetaDensity i k tv.1 * pairOverlapBetaDensity j l tv.2) := by
    filter_upwards [hp] with tv htv
    unfold pairOverlapBetaNormalizedRemainderKernel
    have hd : 0 ≤ pairOverlapBetaDensity i k tv.1 *
        pairOverlapBetaDensity j l tv.2 :=
      mul_nonneg (pairOverlapBetaDensity_nonneg i k htv.1)
        (pairOverlapBetaDensity_nonneg j l htv.2)
    have hr := pairOverlap_betaRemainder_normalized_le i j k l htv.1 htv.2
    dsimp [ε] at hr ⊢
    nlinarith
  constructor
  · unfold pairOverlapRemainderMean
    exact integral_nonneg_of_ae hnonneg
  · unfold pairOverlapRemainderMean
    calc
      (∫ tv : ℝ×ℝ, pairOverlapBetaNormalizedRemainderKernel i j k l tv
          ∂pairOverlapBetaSquareMeasure) ≤
          ∫ tv : ℝ×ℝ,
            ε * (pairOverlapBetaDensity i k tv.1 * pairOverlapBetaDensity j l tv.2)
              ∂pairOverlapBetaSquareMeasure :=
        integral_mono_ae hrem hmajorant hle
      _ = ε := by
        unfold pairOverlapBetaSquareMeasure
        rw [integral_const_mul, integral_prod_mul,
          integral_pairOverlapBetaDensity, integral_pairOverlapBetaDensity]
        ring
      _ = (147:ℝ)/10^12 := rfl


end UnitDistance.Witness
