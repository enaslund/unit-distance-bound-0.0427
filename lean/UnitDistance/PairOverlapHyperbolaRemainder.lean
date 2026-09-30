module

public import UnitDistance.PairOverlapHyperbolaIntegrable

@[expose] public section
set_option backward.privateInPublic true


/-!
# An elementary leading term and remainder for the hyperbola integral

The reciprocal hyperbola integrand is the product of two smoothed step
functions.  Expanding that product around the two steps isolates a leading
integral and a nonnegative remainder.  Splitting the real line at the two
step locations gives an explicit `O(b^2 log (1 / b))` bound, without using a
hypergeometric series.
-/

noncomputable section

open MeasureTheory Set

namespace UnitDistance

def pairHyperbolaFirstFactor (A b u : ℝ) : ℝ :=
  (1 + b * Real.exp (2 * u)) ^ (-A)

def pairHyperbolaSecondFactor (B b u : ℝ) : ℝ :=
  (1 + b * Real.exp (-2 * u)) ^ (-B)

def pairHyperbolaLeadingIntegrand (A B b u : ℝ) : ℝ :=
  pairHyperbolaFirstFactor A b u + pairHyperbolaSecondFactor B b u - 1

def pairHyperbolaRemainderIntegrand (A B b u : ℝ) : ℝ :=
  (1 - pairHyperbolaFirstFactor A b u) *
    (1 - pairHyperbolaSecondFactor B b u)

def pairHyperbolaLeading (A B b : ℝ) : ℝ :=
  ∫ u : ℝ, pairHyperbolaLeadingIntegrand A B b u

def pairHyperbolaRemainder (A B b : ℝ) : ℝ :=
  ∫ u : ℝ, pairHyperbolaRemainderIntegrand A B b u

theorem one_sub_one_add_rpow_neg_nonneg_le {A x : ℝ}
    (hA : 0 ≤ A) (hx : 0 ≤ x) :
    0 ≤ 1 - (1 + x) ^ (-A) ∧ 1 - (1 + x) ^ (-A) ≤ A * x := by
  have hbase : 1 ≤ 1 + x := by linarith
  have hbasepos : 0 < 1 + x := lt_of_lt_of_le zero_lt_one hbase
  have hrpow0 : 0 ≤ (1 + x) ^ (-A) := Real.rpow_nonneg hbasepos.le _
  have hrpow1 : (1 + x) ^ (-A) ≤ 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hbase (neg_nonpos.mpr hA)
  constructor
  · linarith
  · rw [Real.rpow_def_of_pos hbasepos]
    have hlog0 : 0 ≤ Real.log (1 + x) := Real.log_nonneg hbase
    have hexp := Real.add_one_le_exp (-(A * Real.log (1 + x)))
    have hlog : Real.log (1 + x) ≤ x := by
      have := Real.log_le_sub_one_of_pos hbasepos
      linarith
    have hmul : A * Real.log (1 + x) ≤ A * x :=
      mul_le_mul_of_nonneg_left hlog hA
    rw [show Real.log (1 + x) * -A = -(A * Real.log (1 + x)) by ring]
    linarith

theorem pairHyperbolaRemainderIntegrand_nonneg {A B b u : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hb : 0 ≤ b) :
    0 ≤ pairHyperbolaRemainderIntegrand A B b u := by
  unfold pairHyperbolaRemainderIntegrand pairHyperbolaFirstFactor
    pairHyperbolaSecondFactor
  exact mul_nonneg
    (one_sub_one_add_rpow_neg_nonneg_le hA (by positivity)).1
    (one_sub_one_add_rpow_neg_nonneg_le hB (by positivity)).1

theorem pairHyperbolaRemainderIntegrand_le_first {A B b u : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hb : 0 ≤ b) :
    pairHyperbolaRemainderIntegrand A B b u ≤ A * b * Real.exp (2*u) := by
  have hfirst := one_sub_one_add_rpow_neg_nonneg_le hA
    (show 0 ≤ b * Real.exp (2*u) by positivity)
  have hsecond := one_sub_one_add_rpow_neg_nonneg_le hB
    (show 0 ≤ b * Real.exp (-2*u) by positivity)
  have hsecond_one : 1 - (1 + b * Real.exp (-2*u)) ^ (-B) ≤ 1 := by
    have hp : 0 ≤ (1 + b * Real.exp (-2*u)) ^ (-B) := by positivity
    linarith
  unfold pairHyperbolaRemainderIntegrand pairHyperbolaFirstFactor
    pairHyperbolaSecondFactor
  calc
    (1 - (1 + b * Real.exp (2*u)) ^ (-A)) *
        (1 - (1 + b * Real.exp (-2*u)) ^ (-B)) ≤
        (A * (b * Real.exp (2*u))) * 1 :=
      mul_le_mul hfirst.2 hsecond_one hsecond.1 (by positivity)
    _ = A * b * Real.exp (2*u) := by ring

theorem pairHyperbolaRemainderIntegrand_le_second {A B b u : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hb : 0 ≤ b) :
    pairHyperbolaRemainderIntegrand A B b u ≤ B * b * Real.exp (-2*u) := by
  have hfirst := one_sub_one_add_rpow_neg_nonneg_le hA
    (show 0 ≤ b * Real.exp (2*u) by positivity)
  have hsecond := one_sub_one_add_rpow_neg_nonneg_le hB
    (show 0 ≤ b * Real.exp (-2*u) by positivity)
  have hfirst_one : 1 - (1 + b * Real.exp (2*u)) ^ (-A) ≤ 1 := by
    have hp : 0 ≤ (1 + b * Real.exp (2*u)) ^ (-A) := by positivity
    linarith
  unfold pairHyperbolaRemainderIntegrand pairHyperbolaFirstFactor
    pairHyperbolaSecondFactor
  calc
    (1 - (1 + b * Real.exp (2*u)) ^ (-A)) *
        (1 - (1 + b * Real.exp (-2*u)) ^ (-B)) ≤
        1 * (B * (b * Real.exp (-2*u))) :=
      mul_le_mul hfirst_one hsecond.2 hsecond.1 (by positivity)
    _ = B * b * Real.exp (-2*u) := by ring

theorem pairHyperbolaRemainderIntegrand_le_middle {A B b u : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hb : 0 ≤ b) :
    pairHyperbolaRemainderIntegrand A B b u ≤ A * B * b^2 := by
  have hfirst := one_sub_one_add_rpow_neg_nonneg_le hA
    (show 0 ≤ b * Real.exp (2*u) by positivity)
  have hsecond := one_sub_one_add_rpow_neg_nonneg_le hB
    (show 0 ≤ b * Real.exp (-2*u) by positivity)
  unfold pairHyperbolaRemainderIntegrand pairHyperbolaFirstFactor
    pairHyperbolaSecondFactor
  calc
    (1 - (1 + b * Real.exp (2*u)) ^ (-A)) *
        (1 - (1 + b * Real.exp (-2*u)) ^ (-B)) ≤
        (A * (b * Real.exp (2*u))) * (B * (b * Real.exp (-2*u))) :=
      mul_le_mul hfirst.2 hsecond.2 hsecond.1 (by positivity)
    _ = A * B * b^2 := by
      calc
        (A * (b * Real.exp (2*u))) * (B * (b * Real.exp (-2*u))) =
            A*B*b^2 * (Real.exp (2*u) * Real.exp (-2*u)) := by ring
        _ = A*B*b^2 * Real.exp (2*u + -2*u) := by rw [Real.exp_add]
        _ = A*B*b^2 := by simp

private def pairHyperbolaRemainderMajorant (A B b : ℝ) (u : ℝ) : ℝ :=
  let L := Real.log (1 / b)
  (Iic (-L/2)).indicator (fun u => A*b*Real.exp (2*u)) u +
    (Ioc (-L/2) (L/2)).indicator (fun _ => A*B*b^2) u +
      (Ioi (L/2)).indicator (fun u => B*b*Real.exp (-2*u)) u

private theorem integrable_pairHyperbolaRemainderMajorant
    (A B b : ℝ) : Integrable (pairHyperbolaRemainderMajorant A B b) := by
  have hleft : IntegrableOn (fun u : ℝ => A*b*Real.exp (2*u))
      (Iic (-Real.log (1/b)/2)) := by
    exact (integrableOn_exp_mul_Iic (show (0 : ℝ) < 2 by norm_num) _).const_mul (A*b)
  have hmid : IntegrableOn (fun _ : ℝ => A*B*b^2)
      (Ioc (-Real.log (1/b)/2) (Real.log (1/b)/2)) := by
    exact integrableOn_const (hs := by simp [Real.volume_Ioc])
      (hC := enorm_ne_top)
  have hright : IntegrableOn (fun u : ℝ => B*b*Real.exp (-2*u))
      (Ioi (Real.log (1/b)/2)) := by
    exact (integrableOn_exp_mul_Ioi (show (-2 : ℝ) < 0 by norm_num) _).const_mul (B*b)
  unfold pairHyperbolaRemainderMajorant
  dsimp only
  exact (((integrable_indicator_iff measurableSet_Iic).2 hleft).add
    ((integrable_indicator_iff measurableSet_Ioc).2 hmid)).add
      ((integrable_indicator_iff measurableSet_Ioi).2 hright)

private theorem pairHyperbolaRemainderIntegrand_le_majorant
    {A B b u : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hb : 0 < b) (hb1 : b ≤ 1) :
    pairHyperbolaRemainderIntegrand A B b u ≤
      pairHyperbolaRemainderMajorant A B b u := by
  let L := Real.log (1/b)
  have hL : 0 ≤ L := by
    apply Real.log_nonneg
    exact (le_div_iff₀ hb).2 (by simpa using hb1)
  have hc : -L/2 ≤ L/2 := by linarith
  by_cases hu : u ≤ -L/2
  · have hleftmem : u ∈ Iic (-L/2) := hu
    have hnotmid : u ∉ Ioc (-L/2) (L/2) := fun h => (not_lt_of_ge hu) h.1
    have hnotright : u ∉ Ioi (L/2) := fun h => not_lt_of_ge (hu.trans hc) h
    rw [pairHyperbolaRemainderMajorant]
    change pairHyperbolaRemainderIntegrand A B b u ≤
      (Iic (-L/2)).indicator (fun u => A*b*Real.exp (2*u)) u +
        (Ioc (-L/2) (L/2)).indicator (fun _ => A*B*b^2) u +
          (Ioi (L/2)).indicator (fun u => B*b*Real.exp (-2*u)) u
    simp [Set.indicator_of_mem hleftmem, Set.indicator_of_notMem hnotmid,
      Set.indicator_of_notMem hnotright]
    exact pairHyperbolaRemainderIntegrand_le_first hA hB hb.le
  · have hclt : -L/2 < u := lt_of_not_ge hu
    by_cases hud : u ≤ L/2
    · have hnotleft : u ∉ Iic (-L/2) := hu
      have hmidmem : u ∈ Ioc (-L/2) (L/2) := ⟨hclt, hud⟩
      have hnotright : u ∉ Ioi (L/2) := fun h => not_lt_of_ge hud h
      rw [pairHyperbolaRemainderMajorant]
      change pairHyperbolaRemainderIntegrand A B b u ≤
        (Iic (-L/2)).indicator (fun u => A*b*Real.exp (2*u)) u +
          (Ioc (-L/2) (L/2)).indicator (fun _ => A*B*b^2) u +
            (Ioi (L/2)).indicator (fun u => B*b*Real.exp (-2*u)) u
      simp [Set.indicator_of_notMem hnotleft,
        Set.indicator_of_mem hmidmem, Set.indicator_of_notMem hnotright]
      exact pairHyperbolaRemainderIntegrand_le_middle hA hB hb.le
    · have hnotleft : u ∉ Iic (-L/2) := hu
      have hnotmid : u ∉ Ioc (-L/2) (L/2) := fun h => hud h.2
      have hright : u ∈ Ioi (L/2) := lt_of_not_ge hud
      rw [pairHyperbolaRemainderMajorant]
      change pairHyperbolaRemainderIntegrand A B b u ≤
        (Iic (-L/2)).indicator (fun u => A*b*Real.exp (2*u)) u +
          (Ioc (-L/2) (L/2)).indicator (fun _ => A*B*b^2) u +
            (Ioi (L/2)).indicator (fun u => B*b*Real.exp (-2*u)) u
      simp [Set.indicator_of_notMem hnotleft,
        Set.indicator_of_notMem hnotmid, Set.indicator_of_mem hright]
      convert pairHyperbolaRemainderIntegrand_le_second
        (u := u) hA hB hb.le using 1 <;> ring

theorem integrable_pairHyperbolaRemainderIntegrand {A B b : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hb : 0 < b) (hb1 : b ≤ 1) :
    Integrable (pairHyperbolaRemainderIntegrand A B b) := by
  apply (integrable_pairHyperbolaRemainderMajorant A B b).mono'
  · unfold pairHyperbolaRemainderIntegrand pairHyperbolaFirstFactor
      pairHyperbolaSecondFactor
    fun_prop
  · filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg
      (pairHyperbolaRemainderIntegrand_nonneg hA hB hb.le)]
    exact pairHyperbolaRemainderIntegrand_le_majorant hA hB hb hb1

private theorem integral_pairHyperbolaRemainderMajorant
    {A B b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    (∫ u : ℝ, pairHyperbolaRemainderMajorant A B b u) =
      b^2 * (A*B*Real.log (1/b) + (A+B)/2) := by
  let L := Real.log (1/b)
  have hL : 0 ≤ L := by
    apply Real.log_nonneg
    exact (le_div_iff₀ hb).2 (by simpa using hb1)
  have hexpneg : Real.exp (-L) = b := by
    dsimp [L]
    rw [Real.exp_neg, Real.exp_log (by positivity : 0 < 1/b)]
    field_simp
  have hleft : Integrable
      ((Iic (-L/2)).indicator (fun u : ℝ => A*b*Real.exp (2*u))) := by
    rw [integrable_indicator_iff measurableSet_Iic]
    exact (integrableOn_exp_mul_Iic (show (0 : ℝ) < 2 by norm_num) _).const_mul (A*b)
  have hmid : Integrable
      ((Ioc (-L/2) (L/2)).indicator (fun _ : ℝ => A*B*b^2)) := by
    rw [integrable_indicator_iff measurableSet_Ioc]
    exact integrableOn_const (hs := by simp [Real.volume_Ioc])
      (hC := enorm_ne_top)
  have hright : Integrable
      ((Ioi (L/2)).indicator (fun u : ℝ => B*b*Real.exp (-2*u))) := by
    rw [integrable_indicator_iff measurableSet_Ioi]
    exact (integrableOn_exp_mul_Ioi (show (-2 : ℝ) < 0 by norm_num) _).const_mul (B*b)
  have hiLeft : (∫ u : ℝ, (Iic (-L/2)).indicator
      (fun u : ℝ => A*b*Real.exp (2*u)) u) = A*b^2/2 := by
    rw [integral_indicator measurableSet_Iic, integral_const_mul,
      integral_exp_mul_Iic (show (0 : ℝ) < 2 by norm_num)]
    rw [show 2 * (-L/2) = -L by ring, hexpneg]
    ring
  have hiMid : (∫ u : ℝ, (Ioc (-L/2) (L/2)).indicator
      (fun _ : ℝ => A*B*b^2) u) = A*B*b^2*L := by
    rw [integral_indicator measurableSet_Ioc, setIntegral_const]
    simp [Measure.real, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith : 0 ≤ L/2 - -L/2)]
    ring
  have hiRight : (∫ u : ℝ, (Ioi (L/2)).indicator
      (fun u : ℝ => B*b*Real.exp (-2*u)) u) = B*b^2/2 := by
    rw [integral_indicator measurableSet_Ioi, integral_const_mul,
      integral_exp_mul_Ioi (show (-2 : ℝ) < 0 by norm_num)]
    rw [show -2 * (L/2) = -L by ring, hexpneg]
    ring
  unfold pairHyperbolaRemainderMajorant
  dsimp only
  change (∫ u : ℝ,
      (Iic (-L/2)).indicator (fun u => A*b*Real.exp (2*u)) u +
        (Ioc (-L/2) (L/2)).indicator (fun _ => A*B*b^2) u +
          (Ioi (L/2)).indicator (fun u => B*b*Real.exp (-2*u)) u) =
    b^2 * (A*B*L + (A+B)/2)
  calc
    (∫ u : ℝ,
        (Iic (-L/2)).indicator (fun u => A*b*Real.exp (2*u)) u +
          (Ioc (-L/2) (L/2)).indicator (fun _ => A*B*b^2) u +
            (Ioi (L/2)).indicator (fun u => B*b*Real.exp (-2*u)) u) =
        (∫ u : ℝ,
          (Iic (-L/2)).indicator (fun u => A*b*Real.exp (2*u)) u +
            (Ioc (-L/2) (L/2)).indicator (fun _ => A*B*b^2) u) +
          ∫ u : ℝ, (Ioi (L/2)).indicator
            (fun u => B*b*Real.exp (-2*u)) u :=
      integral_add (hleft.add hmid) hright
    _ = ((∫ u : ℝ, (Iic (-L/2)).indicator
            (fun u => A*b*Real.exp (2*u)) u) +
          ∫ u : ℝ, (Ioc (-L/2) (L/2)).indicator
            (fun _ => A*B*b^2) u) +
          ∫ u : ℝ, (Ioi (L/2)).indicator
            (fun u => B*b*Real.exp (-2*u)) u := by
      rw [integral_add hleft hmid]
    _ = b^2 * (A*B*L + (A+B)/2) := by
      rw [hiLeft, hiMid, hiRight]
      ring

theorem pairHyperbolaRemainder_nonneg_le {A B b : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hb : 0 < b) (hb1 : b ≤ 1) :
    0 ≤ pairHyperbolaRemainder A B b ∧
      pairHyperbolaRemainder A B b ≤
        b^2 * (A*B*Real.log (1/b) + (A+B)/2) := by
  have hrem := integrable_pairHyperbolaRemainderIntegrand hA hB hb hb1
  have hmaj := integrable_pairHyperbolaRemainderMajorant A B b
  constructor
  · unfold pairHyperbolaRemainder
    exact integral_nonneg (fun u => pairHyperbolaRemainderIntegrand_nonneg hA hB hb.le)
  · unfold pairHyperbolaRemainder
    rw [← integral_pairHyperbolaRemainderMajorant hb hb1]
    exact integral_mono hrem hmaj
      (fun u => pairHyperbolaRemainderIntegrand_le_majorant hA hB hb hb1)

theorem pairHyperbola_eq_leading_add_remainder {A B b : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hb : 0 < b) (hb1 : b ≤ 1) :
    pairHyperbola A B b =
      pairHyperbolaLeading A B b + pairHyperbolaRemainder A B b := by
  have hprod := integrable_pairHyperbolaIntegrand hA hB hb
  have hrem := integrable_pairHyperbolaRemainderIntegrand hA.le hB.le hb hb1
  have hlead : Integrable (pairHyperbolaLeadingIntegrand A B b) := by
    apply (hprod.sub hrem).congr
    filter_upwards with u
    change pairHyperbolaIntegrand A B b u -
        pairHyperbolaRemainderIntegrand A B b u =
      pairHyperbolaLeadingIntegrand A B b u
    unfold pairHyperbolaIntegrand pairHyperbolaLeadingIntegrand
      pairHyperbolaRemainderIntegrand pairHyperbolaFirstFactor
      pairHyperbolaSecondFactor
    ring
  unfold pairHyperbola pairHyperbolaLeading pairHyperbolaRemainder
  rw [← integral_add hlead hrem]
  apply integral_congr_ae
  filter_upwards with u
  unfold pairHyperbolaIntegrand pairHyperbolaLeadingIntegrand
    pairHyperbolaRemainderIntegrand pairHyperbolaFirstFactor
    pairHyperbolaSecondFactor
  ring

theorem integrable_pairHyperbolaLeadingIntegrand {A B b : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hb : 0 < b) (hb1 : b ≤ 1) :
    Integrable (pairHyperbolaLeadingIntegrand A B b) := by
  have hprod := integrable_pairHyperbolaIntegrand hA hB hb
  have hrem := integrable_pairHyperbolaRemainderIntegrand hA.le hB.le hb hb1
  apply (hprod.sub hrem).congr
  filter_upwards with u
  change pairHyperbolaIntegrand A B b u -
      pairHyperbolaRemainderIntegrand A B b u =
    pairHyperbolaLeadingIntegrand A B b u
  unfold pairHyperbolaIntegrand pairHyperbolaLeadingIntegrand
    pairHyperbolaRemainderIntegrand pairHyperbolaFirstFactor
    pairHyperbolaSecondFactor
  ring

theorem pairHyperbolaLeading_le_pairHyperbola {A B b : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hb : 0 < b) (hb1 : b ≤ 1) :
    pairHyperbolaLeading A B b ≤ pairHyperbola A B b := by
  rw [pairHyperbola_eq_leading_add_remainder hA hB hb hb1]
  exact le_add_of_nonneg_right (pairHyperbolaRemainder_nonneg_le hA.le hB.le hb hb1).1

end UnitDistance
