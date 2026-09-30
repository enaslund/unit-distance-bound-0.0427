module

public import UnitDistance.GaussianProfiles
public import UnitDistance.EnergyWindow

@[expose] public section
set_option backward.privateInPublic true


/-! # Finite endpoint second moments for the actual compact Gaussian profile -/

open MeasureTheory
open scoped ENNReal

namespace UnitDistance

theorem sq_mul_exp_neg_le {t : ℝ} (ht : 0 ≤ t) :
    t^2 * Real.exp (-t) ≤ 8 * Real.exp (-t/2) := by
  have h := Real.pow_div_factorial_le_exp (t/2) (show 0 ≤ t/2 by positivity) 2
  norm_num at h
  have hh : t^2 ≤ 8*Real.exp (t/2) := by nlinarith
  calc
    t^2 * Real.exp (-t) ≤ (8*Real.exp (t/2))*Real.exp (-t) :=
      mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
    _ = 8*Real.exp (-t/2) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem gaussian_shifted_energy_memLp (b Z : ℝ) (hb : 0 < b) (hZ : 0 < Z)
    (shift : ℂ) (w : ℂ → ℝ) (hw : Measurable w)
    (hw0 : ∀ z, 0 ≤ w z) (hw1 : ∀ z, w z ≤ 1) :
    MemLp (fun z : ℂ => b*‖z+shift‖^2) 2
      ((volume : Measure ℂ).withDensity
        (fun z => ENNReal.ofReal (complexGaussian b (z+shift)*w z/Z))) := by
  have hm : Measurable (fun z : ℂ => b*‖z+shift‖^2) := by fun_prop
  apply (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).mpr
  rw [integrable_withDensity_iff_integrable_smul'
    (show Measurable (fun z => ENNReal.ofReal (complexGaussian b (z+shift)*w z/Z)) by
      unfold complexGaussian; fun_prop)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [smul_eq_mul]
  have hg := complexGaussian_integrable (b := b/2) (by positivity)
  have hgshift := ((measurePreserving_add_right (volume : Measure ℂ) shift).integrable_comp
    hg.aestronglyMeasurable).mpr hg
  apply (hgshift.const_mul (8/Z)).mono'
  · unfold complexGaussian
    fun_prop
  · filter_upwards [] with z
    have hgauss : 0 ≤ complexGaussian b (z+shift) := (Real.exp_pos _).le
    rw [ENNReal.toReal_ofReal (div_nonneg
      (mul_nonneg hgauss (hw0 z)) hZ.le)]
    have ht : 0 ≤ b*‖z+shift‖^2 := mul_nonneg hb.le (sq_nonneg _)
    have hdom := sq_mul_exp_neg_le ht
    have hweight : complexGaussian b (z+shift) * w z ≤ complexGaussian b (z+shift) := by
      exact mul_le_of_le_one_right (Real.exp_pos _).le (hw1 z)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (div_nonneg (mul_nonneg hgauss (hw0 z)) hZ.le) (sq_nonneg _))]
    calc
      (complexGaussian b (z+shift)*w z/Z) * (b*‖z+shift‖^2)^2 ≤
          (complexGaussian b (z+shift)/Z) * (b*‖z+shift‖^2)^2 := by gcongr
      _ = ((b*‖z+shift‖^2)^2 * Real.exp (-(b*‖z+shift‖^2)))/Z := by
        simp only [complexGaussian, neg_mul]
        ring
      _ ≤ (8*Real.exp (-(b*‖z+shift‖^2)/2))/Z :=
        div_le_div_of_nonneg_right hdom hZ.le
      _ = (8/Z)*complexGaussian (b/2) (z+shift) := by
        unfold complexGaussian
        rw [show -(b*‖z+shift‖^2)/2 = -(b/2)*‖z+shift‖^2 by ring]
        ring

theorem complexGaussian_le_one {b : ℝ} (hb : 0 ≤ b) (z : ℂ) :
    complexGaussian b z ≤ 1 :=
  Real.exp_le_one_iff.mpr (by exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb) (sq_nonneg _))

theorem gaussian_endpoint_memLp {b Z : ℝ} (hb : 0 < b) (hZ : 0 < Z) :
    let μ := overlapLaw (volume : Measure ℂ) (fun z => b*‖z‖^2)
      (fun z => b*‖z+1‖^2) Z
    MemLp (fun z : ℂ => b*‖z‖^2) 2 μ ∧
      MemLp (fun z : ℂ => b*‖z+1‖^2) 2 μ := by
  have hfirst := gaussian_shifted_energy_memLp b Z hb hZ 0
    (fun z => complexGaussian b (z+1)) (by unfold complexGaussian; fun_prop)
    (fun _ => (Real.exp_pos _).le) (fun z => complexGaussian_le_one hb.le (z+1))
  have hsecond := gaussian_shifted_energy_memLp b Z hb hZ 1
    (complexGaussian b) (by unfold complexGaussian; fun_prop)
    (fun _ => (Real.exp_pos _).le) (fun z => complexGaussian_le_one hb.le z)
  dsimp only
  simp only [add_zero] at hfirst
  have heq : overlapLaw (volume : Measure ℂ) (fun z => b*‖z‖^2)
      (fun z => b*‖z+1‖^2) Z =
      (volume : Measure ℂ).withDensity
        (fun z => ENNReal.ofReal (complexGaussian b z * complexGaussian b (z+1)/Z)) := by
    unfold overlapLaw
    congr 1
    funext z
    simp [complexGaussian, Real.exp_add, neg_add_rev, neg_mul, mul_comm]
  rw [heq]
  exact ⟨hfirst, by simpa only [mul_comm] using hsecond⟩

namespace Witness

theorem compact_endpoint_memLp :
    let E := fun z : ℂ => -Real.log (compactProfile z)
    let μ := overlapLaw (volume : Measure ℂ) E (fun z => E (z+1)) compactOverlap
    MemLp E 2 μ ∧ MemLp (fun z => E (z+1)) 2 μ := by
  have heq : (fun z : ℂ => -Real.log (compactProfile z)) =
      (fun z : ℂ => (2*increment)*‖z‖^2) := by
    funext z
    rw [compactProfile_gaussian, complexGaussian, Real.log_exp]
    ring
  dsimp only
  simp_rw [show ∀ z, -Real.log (compactProfile z) = (2*increment)*‖z‖^2
    from fun z => congrFun heq z]
  exact gaussian_endpoint_memLp (b := 2*increment) (Z := compactOverlap)
    (mul_pos (by norm_num) increment_pos) compactOverlap_pos

end Witness

end UnitDistance
