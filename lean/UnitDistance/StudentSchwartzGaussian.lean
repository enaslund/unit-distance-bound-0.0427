module

public import UnitDistance.StudentSchwartzGrowth
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public section
set_option backward.privateInPublic true


/-!
# A Gaussian Schwartz multiplier

The proof bounds derivatives of the exponential of a quadratic using
Mathlib's iterated chain-rule estimate. Polynomial factors are absorbed by
an elementary, kernel-proved exponential-series inequality. This establishes
Schwartzness without a supplied rapid-decay or smoothness hypothesis.
-/

open scoped ContDiff BigOperators

namespace UnitDistance

/-- A uniform elementary bound for a polynomial times a decaying Gaussian. -/
theorem polynomial_gaussian_bound {ε : ℝ} (hε : 0 < ε) (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (1+t)^m * Real.exp (-ε*t^2) ≤
      2^m * (1 + (m.factorial : ℝ) / ε^m) := by
  have hfac : 0 < (m.factorial : ℝ) := by positivity
  have he : 0 < Real.exp (-ε*t^2) := Real.exp_pos _
  have he1 : Real.exp (-ε*t^2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hε.le (sq_nonneg t)])
  have hfrac : 0 ≤ (m.factorial : ℝ) / ε^m := by positivity
  by_cases ht1 : t ≤ 1
  · calc
      (1+t)^m * Real.exp (-ε*t^2) ≤ 2^m * 1 := by gcongr; linarith
      _ ≤ _ := by gcongr; linarith
  · have ht1 : 1 ≤ t := by linarith
    have hseries := Real.pow_div_factorial_le_exp (ε*t^2) (by positivity) m
    have hpower : t^(2*m) * Real.exp (-ε*t^2) ≤ (m.factorial : ℝ) / ε^m := by
      have hseries' : ε^m * t^(2*m) ≤ (m.factorial : ℝ) * Real.exp (ε*t^2) := by
        simpa only [mul_pow, ← pow_mul, mul_comm (Real.exp _) _] using (div_le_iff₀ hfac).mp hseries
      apply (le_div_iff₀ (pow_pos hε m)).mpr
      calc
        t^(2*m) * Real.exp (-ε*t^2) * ε^m =
            (ε^m*t^(2*m))*Real.exp (-ε*t^2) := by ring
        _ ≤ ((m.factorial : ℝ)*Real.exp (ε*t^2))*Real.exp (-ε*t^2) :=
          mul_le_mul_of_nonneg_right hseries' he.le
        _ = m.factorial := by rw [mul_assoc, ← Real.exp_add]; ring_nf; simp
    calc
      (1+t)^m * Real.exp (-ε*t^2) ≤ (2*t)^m * Real.exp (-ε*t^2) := by
        gcongr; linarith
      _ = 2^m * (t^m * Real.exp (-ε*t^2)) := by rw [mul_pow]; ring
      _ ≤ 2^m * (t^(2*m) * Real.exp (-ε*t^2)) := by
        gcongr
        omega
      _ ≤ 2^m * ((m.factorial : ℝ) / ε^m) := mul_le_mul_of_nonneg_left hpower (by positivity)
      _ ≤ _ := by gcongr; linarith

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Gaussian damping is Schwartz on any real inner product space. In finite
dimension this uses its ordinary Euclidean norm and hence the usual Fourier
Gaussian. -/
noncomputable def gaussianSchwartz (ε : ℝ) (hε : 0 < ε) : SchwartzMap V ℝ where
  toFun x := Real.exp (-ε*‖x‖^2)
  smooth' := by
    have hq : (fun x : V => -ε*‖x‖^2).HasTemperateGrowth := by fun_prop
    exact Real.contDiff_exp.comp hq.1
  decay' k n := by
    have hq : (fun x : V => -ε*‖x‖^2).HasTemperateGrowth := by fun_prop
    obtain ⟨l, C, hC, hbound⟩ := hq.norm_iteratedFDeriv_le_uniform n
    refine ⟨(n.factorial : ℝ)*(1+C)^n *
      (2^(k+l*n) * (1+((k+l*n).factorial : ℝ)/ε^(k+l*n))), ?_⟩
    intro x
    have hD (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
        ‖iteratedFDeriv ℝ i (fun x : V => -ε*‖x‖^2) x‖ ≤
          ((1+C)*(1+‖x‖)^l)^i := by
      calc
        _ ≤ C*(1+‖x‖)^l := hbound i hin x
        _ ≤ (1+C)*(1+‖x‖)^l := by gcongr; linarith
        _ ≤ _ := le_self_pow₀
          (one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ (by linarith [norm_nonneg x]))) (by omega)
    have hE (i : ℕ) (_hin : i ≤ n) :
        ‖iteratedFDeriv ℝ i Real.exp (-ε*‖x‖^2)‖ ≤ Real.exp (-ε*‖x‖^2) := by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate,
        Real.iter_deriv_exp, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hcomp := norm_iteratedFDeriv_comp_le Real.contDiff_exp hq.1
      (show (n : ℕ∞ω) ≤ ∞ from mod_cast le_top) x hE hD
    change ‖iteratedFDeriv ℝ n (fun x : V => Real.exp (-ε*‖x‖^2)) x‖ ≤ _ at hcomp
    calc
      _ ≤ ‖x‖^k * ((n.factorial : ℝ)*Real.exp (-ε*‖x‖^2)*
          ((1+C)*(1+‖x‖)^l)^n) := mul_le_mul_of_nonneg_left hcomp (by positivity)
      _ ≤ (1+‖x‖)^k * ((n.factorial : ℝ)*Real.exp (-ε*‖x‖^2)*
          ((1+C)*(1+‖x‖)^l)^n) := by gcongr; linarith [norm_nonneg x]
      _ = (n.factorial : ℝ)*(1+C)^n *
          ((1+‖x‖)^(k+l*n)*Real.exp (-ε*‖x‖^2)) := by
        rw [mul_pow, ← pow_mul, pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (polynomial_gaussian_bound hε _ (norm_nonneg x))
        (by positivity)

@[simp] theorem gaussianSchwartz_apply (ε : ℝ) (hε : 0 < ε) (x : V) :
    gaussianSchwartz ε hε x = Real.exp (-ε*‖x‖^2) := rfl

end UnitDistance
