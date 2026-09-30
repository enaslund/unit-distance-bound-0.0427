module

public import UnitDistance.TsfasmanVladutKernelBoundary

@[expose] public section
set_option backward.privateInPublic true


/-!
# Positivity of the Tsfasman–Vlăduţ transform on the closed critical strip

The Phragmén–Lindelöf principle is applied to `exp (-tvTransform e s)`.
The boundary real parts are computed from the actual kernel, and the growth
condition follows from its uniform absolute integral bound. There is no
positivity assumption on the transform or on the zeros of a zeta function.
-/

noncomputable section
open MeasureTheory Set Filter Complex Asymptotics
open scoped Topology

namespace UnitDistance.NumberFieldAnalysis

theorem tvTransform_re_boundary_zero {e : ℝ} (he : 0 < e) {s : ℂ}
    (hs : s.re = 0) : (tvTransform e s).re = 2*e/(e^2+s.im^2) := by
  have hz : s = (s.im:ℂ)*I := by apply Complex.ext <;> simp [hs]
  conv_lhs => rw [hz]
  exact tvTransform_re_mul_I he s.im

theorem tvTransform_re_boundary_one {e : ℝ} (he : 0 < e) {s : ℂ}
    (hs : s.re = 1) : (tvTransform e s).re = 2*e/(e^2+s.im^2) := by
  have hz : s = 1+(s.im:ℂ)*I := by apply Complex.ext <;> simp [hs]
  conv_lhs => rw [hz]
  exact tvTransform_re_one_add_mul_I he s.im

theorem norm_exp_neg_tvTransform_le {e : ℝ} (he : 0 < e) {s : ℂ}
    (h₀ : 0 ≤ s.re) (h₁ : s.re ≤ 1) :
    ‖Complex.exp (-tvTransform e s)‖ ≤ Real.exp (4/e) := by
  rw [Complex.norm_exp, Complex.neg_re]
  apply Real.exp_le_exp.mpr
  exact (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans
    (norm_tvTransform_le_closed_strip he h₀ h₁))

/-- Positivity on the entire closed strip, proved analytically from the kernel. -/
theorem tvTransform_re_nonneg {e : ℝ} (he : 0 < e) {s : ℂ}
    (h₀ : 0 ≤ s.re) (h₁ : s.re ≤ 1) : 0 ≤ (tvTransform e s).re := by
  let f : ℂ → ℂ := fun z => Complex.exp (-tvTransform e z)
  have hd : DiffContOnCl ℂ f (Complex.re ⁻¹' Ioo (0:ℝ) 1) := by
    exact ⟨(tvTransform_diffContOnCl he).differentiableOn.neg.cexp,
      (tvTransform_diffContOnCl he).continuousOn.neg.cexp⟩
  have hb : ∃ c < Real.pi/((1:ℝ)-0), ∃ B,
      f =O[comap (abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo (0:ℝ) 1)]
        (fun z => Real.exp (B*Real.exp (c*|z.im|))) := by
    refine ⟨0, by simpa using Real.pi_pos, 0, IsBigO.of_bound (Real.exp (4/e)) ?_⟩
    have hstrip : ∀ᶠ z : ℂ in
        comap (abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo (0:ℝ) 1),
        z ∈ Complex.re ⁻¹' Ioo (0:ℝ) 1 :=
      (eventually_principal.mpr (fun z hz => hz)).filter_mono inf_le_right
    filter_upwards [hstrip] with z hz
    simpa only [zero_mul, Real.exp_zero, norm_one, mul_one] using
      norm_exp_neg_tvTransform_le he hz.1.le hz.2.le
  have hboundary : ∀ z : ℂ, z.re = 0 ∨ z.re = 1 → ‖f z‖ ≤ 1 := by
    intro z hz
    change ‖Complex.exp (-tvTransform e z)‖ ≤ 1
    rw [Complex.norm_exp, Complex.neg_re, Real.exp_le_one_iff]
    have hr : (tvTransform e z).re = 2*e/(e^2+z.im^2) :=
      hz.elim (tvTransform_re_boundary_zero he) (tvTransform_re_boundary_one he)
    rw [hr]
    exact neg_nonpos.mpr (div_nonneg (by positivity) (by positivity))
  have h := PhragmenLindelof.vertical_strip hd hb
    (fun z hz => hboundary z (Or.inl hz)) (fun z hz => hboundary z (Or.inr hz)) h₀ h₁
  change ‖Complex.exp (-tvTransform e s)‖ ≤ 1 at h
  rw [Complex.norm_exp, Complex.neg_re, Real.exp_le_one_iff] at h
  linarith

end UnitDistance.NumberFieldAnalysis
