module

public import UnitDistance.RelativeEuler
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

@[expose] public section
set_option backward.privateInPublic true


/-!
# The archimedean part of the relative Hecke comparison

The correction here is the actual gamma expression in `analytic.tex`. Its
uniform disappearance at the boundary is proved from continuity of Gamma.
The comparison theorem states its completed-function premise explicitly;
neither analytic continuation nor a Hecke functional equation follows from
the definitions in this file.
-/

noncomputable section
open Filter Topology NumberField NumberField.InfinitePlace

namespace UnitDistance.NumberFieldAnalysis

/-- Logarithm of the positive completion factor on the positive real axis.
`ell` is the logarithmic root discriminant, and `b,c` are the real and complex
place counts of the base field. -/
def relativeGammaLog (ell b c s : ℝ) : ℝ :=
  (b + 2*c)*s/2*ell - b*s/2*Real.log Real.pi - c*s*Real.log (2*Real.pi) +
    b*Real.log (Real.Gamma ((s+1)/2)) + c*Real.log (Real.Gamma s)

/-- The completion factor in the manuscript, written as ordinary powers and
Gamma functions rather than logarithms. -/
def relativeGammaFactor (lambda : ℝ) (b c : ℕ) (s : ℝ) : ℝ :=
  lambda ^ (((b:ℝ)+2*c)*s/2) * Real.pi ^ (-(b:ℝ)*s/2) *
    (2*Real.pi) ^ (-(c:ℝ)*s) * Real.Gamma ((s+1)/2)^b * Real.Gamma s^c

theorem relativeGammaFactor_pos {lambda s : ℝ} (hlambda : 0 < lambda)
    (b c : ℕ) (hs : 0 < s) : 0 < relativeGammaFactor lambda b c s := by
  unfold relativeGammaFactor
  have hg : 0 < Real.Gamma ((s+1)/2) := Real.Gamma_pos_of_pos (by linarith)
  have hg' := Real.Gamma_pos_of_pos hs
  positivity

/-- The logarithmic completion used in the comparisons is exactly the
ordinary positive completion factor; it is not an arbitrary correction. -/
theorem log_relativeGammaFactor {lambda s : ℝ} (hlambda : 0 < lambda)
    (b c : ℕ) (hs : 0 < s) :
    Real.log (relativeGammaFactor lambda b c s) =
      relativeGammaLog (Real.log lambda) b c s := by
  unfold relativeGammaFactor relativeGammaLog
  have hg : 0 < Real.Gamma ((s+1)/2) := Real.Gamma_pos_of_pos (by linarith)
  have hg' := Real.Gamma_pos_of_pos hs
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_rpow hlambda, Real.log_rpow Real.pi_pos,
    Real.log_rpow (by positivity : (0:ℝ)<2*Real.pi), Real.log_pow, Real.log_pow]
  ring

theorem exp_relativeGammaLog {lambda s : ℝ} (hlambda : 0 < lambda)
    (b c : ℕ) (hs : 0 < s) :
    Real.exp (relativeGammaLog (Real.log lambda) b c s) =
      relativeGammaFactor lambda b c s := by
  rw [← log_relativeGammaFactor hlambda b c hs,
    Real.exp_log (relativeGammaFactor_pos hlambda b c hs)]

/-- The normalized correction in equation `an:gamma`. -/
def relativeGammaCorrection (ell epsilon theta : ℝ) : ℝ :=
  epsilon/2*(ell-Real.log Real.pi) - epsilon*theta*Real.log 2 +
    (1-2*theta)*Real.log (Real.Gamma (1+epsilon/2)) +
    theta*Real.log (Real.Gamma (1+epsilon))

@[simp] theorem relativeGammaCorrection_zero (ell theta : ℝ) :
    relativeGammaCorrection ell 0 theta = 0 := by
  simp [relativeGammaCorrection, Real.Gamma_one]

theorem relativeGammaCorrection_affine (ell epsilon theta : ℝ) :
    relativeGammaCorrection ell epsilon theta =
      (1-2*theta)*relativeGammaCorrection ell epsilon 0 +
        2*theta*relativeGammaCorrection ell epsilon (1/2) := by
  unfold relativeGammaCorrection
  ring

/-- The gamma quotient has exactly the normalization in the manuscript. -/
theorem relativeGammaLog_sub_one (ell b c epsilon : ℝ) (hd : b+2*c ≠ 0) :
    (relativeGammaLog ell b c (1+epsilon)-relativeGammaLog ell b c 1)/(b+2*c) =
      relativeGammaCorrection ell epsilon (c/(b+2*c)) := by
  unfold relativeGammaLog relativeGammaCorrection
  rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) Real.pi_ne_zero]
  rw [show (1+(1:ℝ))/2 = 1 by norm_num,
    show (1+epsilon+1)/2 = 1+epsilon/2 by ring, Real.Gamma_one, Real.log_one]
  field_simp
  ring

private theorem continuousAt_logGamma_one :
    ContinuousAt (fun x : ℝ => Real.log (Real.Gamma x)) 1 := by
  refine (Real.differentiableAt_Gamma ?_).continuousAt.log ?_
  · intro n
    have hn := Nat.cast_nonneg (α := ℝ) n
    linarith
  · simp [Real.Gamma_one]

theorem continuousAt_relativeGammaCorrection_zero (ell theta : ℝ) :
    ContinuousAt (fun epsilon => relativeGammaCorrection ell epsilon theta) 0 := by
  have hhalf : ContinuousAt (fun epsilon : ℝ =>
      Real.log (Real.Gamma (1+epsilon/2))) 0 := by
    exact ContinuousAt.comp (f := fun e : ℝ => 1+e/2) (x := 0)
      (by simpa using continuousAt_logGamma_one)
      (continuousAt_const.add (continuousAt_id.div_const 2))
  have hone : ContinuousAt (fun epsilon : ℝ =>
      Real.log (Real.Gamma (1+epsilon))) 0 := by
    exact ContinuousAt.comp (f := fun e : ℝ => 1+e) (x := 0)
      (by simpa using continuousAt_logGamma_one)
      (continuousAt_const.add continuousAt_id)
  exact (((continuousAt_id.div_const 2).mul_const _).sub
    ((continuousAt_id.mul_const theta).mul_const _)).add
      ((continuousAt_const.mul hhalf)) |>.add (continuousAt_const.mul hone)

/-- A bound independent of signature, determined only by the two endpoints. -/
def relativeGammaError (ell epsilon : ℝ) : ℝ :=
  |relativeGammaCorrection ell epsilon 0| +
    |relativeGammaCorrection ell epsilon (1/2)|

theorem abs_relativeGammaCorrection_le (ell epsilon : ℝ) {theta : ℝ}
    (htheta : theta ∈ Set.Icc 0 (1/2 : ℝ)) :
    |relativeGammaCorrection ell epsilon theta| ≤ relativeGammaError ell epsilon := by
  rw [relativeGammaCorrection_affine]
  have ha : 0 ≤ 1-2*theta := by linarith [htheta.2]
  have hb : 0 ≤ 2*theta := by linarith [htheta.1]
  calc
    _ ≤ |(1-2*theta)*relativeGammaCorrection ell epsilon 0| +
        |2*theta*relativeGammaCorrection ell epsilon (1/2)| := abs_add_le _ _
    _ = (1-2*theta)*|relativeGammaCorrection ell epsilon 0| +
        (2*theta)*|relativeGammaCorrection ell epsilon (1/2)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ _ := by
      unfold relativeGammaError
      nlinarith [abs_nonneg (relativeGammaCorrection ell epsilon 0),
        abs_nonneg (relativeGammaCorrection ell epsilon (1/2))]

theorem tendsto_relativeGammaError_zero (ell : ℝ) :
    Tendsto (relativeGammaError ell) (𝓝 0) (𝓝 0) := by
  have h := ((continuousAt_relativeGammaCorrection_zero ell 0).abs.add
    (continuousAt_relativeGammaCorrection_zero ell (1/2)).abs).tendsto
  change Tendsto (fun epsilon => |relativeGammaCorrection ell epsilon 0| +
    |relativeGammaCorrection ell epsilon (1/2)|) (𝓝 0) (𝓝 0)
  simp only [Pi.add_apply, relativeGammaCorrection_zero, abs_zero, add_zero] at h
  exact h.congr (fun _ => rfl)

/-- Uniform vanishing for every signature ratio in `[0,1/2]`, allowing the
signature to vary arbitrarily with the fields in a family. -/
theorem relativeGammaCorrection_uniform_zero (ell : ℝ) {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ epsilon in 𝓝 (0 : ℝ), ∀ theta ∈ Set.Icc 0 (1/2 : ℝ),
      |relativeGammaCorrection ell epsilon theta| < delta := by
  filter_upwards [(tendsto_relativeGammaError_zero ell).eventually_lt_const hdelta] with epsilon he
  intro theta htheta
  exact (abs_relativeGammaCorrection_le ell epsilon htheta).trans_lt he

variable (K F : Type*) [Field K] [NumberField K] [Field F] [NumberField F]

/-- Every actual number-field signature gives a ratio in the whole interval
on which the archimedean error was bounded uniformly. -/
theorem complexPlaceRatio_mem :
    (nrComplexPlaces F : ℝ)/(Module.finrank ℚ F : ℝ) ∈ Set.Icc 0 (1/2 : ℝ) := by
  have hd : (0:ℝ) < Module.finrank ℚ F := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := F)
  have hsig : (nrRealPlaces F : ℝ)+2*(nrComplexPlaces F : ℝ) = Module.finrank ℚ F := by
    exact_mod_cast card_add_two_mul_card_eq_rank F
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hd.le
  · apply (div_le_iff₀ hd).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) (nrRealPlaces F)]

/-- The positive real relative zeta value, with the pole quotient replaced by
its proved boundary residue. Only its values for `s ≥ 1` are used below. -/
def relativeZetaReal (s : ℝ) : ℝ :=
  if s = 1 then relativeResidue K F else (relativeZeta K F s).re

@[simp] theorem relativeZetaReal_one : relativeZetaReal K F 1 = relativeResidue K F := by
  simp [relativeZetaReal]

theorem relativeZetaReal_gt_one {s : ℝ} (hs : 1 < s) :
    relativeZetaReal K F s = (relativeZeta K F s).re := by
  simp [relativeZetaReal, hs.ne']

theorem relativeZetaReal_pos {s : ℝ} (hs : 1 ≤ s) : 0 < relativeZetaReal K F s := by
  rcases eq_or_lt_of_le hs with rfl | hs
  · simpa using relativeResidue_pos K F
  · rw [relativeZetaReal_gt_one K F hs]
    exact (Complex.pos_iff.mp (relativeZeta_positive K F hs)).1

/-- The ordinary real completion of the relative quotient on `[1,∞)`. The
definition itself makes no continuation or monotonicity assertion. -/
def relativeCompletedReal (ell s : ℝ) : ℝ :=
  Real.exp (relativeGammaLog ell (nrRealPlaces F) (nrComplexPlaces F) s) *
    relativeZetaReal K F s

theorem relativeCompletedReal_pos (ell : ℝ) {s : ℝ} (hs : 1 ≤ s) :
    0 < relativeCompletedReal K F ell s :=
  mul_pos (Real.exp_pos _) (relativeZetaReal_pos K F hs)

/-- A comparison of the actual completed values gives the normalized finite
gamma estimate. The completion comparison is an explicit mathematical
premise, rather than an unproved assertion hidden in a definition. -/
theorem normalized_log_relativeResidue_le_of_completion_le (ell : ℝ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hcomp : relativeCompletedReal K F ell 1 ≤ relativeCompletedReal K F ell (1+epsilon)) :
    Real.log (relativeResidue K F)/(Module.finrank ℚ F : ℝ) ≤
      Real.log (relativeZeta K F (1+epsilon)).re/(Module.finrank ℚ F : ℝ) +
        relativeGammaCorrection ell epsilon
          ((nrComplexPlaces F : ℝ)/(Module.finrank ℚ F : ℝ)) := by
  have hs : 1 < 1+epsilon := by linarith
  have hlog := Real.log_le_log (relativeCompletedReal_pos K F ell (by rfl : 1 ≤ (1:ℝ))) hcomp
  unfold relativeCompletedReal at hlog
  rw [Real.log_mul (Real.exp_ne_zero _) (relativeZetaReal_pos K F (le_refl 1)).ne',
    Real.log_mul (Real.exp_ne_zero _) (relativeZetaReal_pos K F hs.le).ne',
    Real.log_exp, Real.log_exp, relativeZetaReal_one,
    relativeZetaReal_gt_one K F hs] at hlog
  have hd : (0:ℝ) < Module.finrank ℚ F := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := F)
  have hsig : (nrRealPlaces F : ℝ)+2*(nrComplexPlaces F : ℝ) = Module.finrank ℚ F := by
    exact_mod_cast card_add_two_mul_card_eq_rank F
  have hgamma := relativeGammaLog_sub_one ell (nrRealPlaces F) (nrComplexPlaces F)
    epsilon (by rw [hsig]; exact hd.ne')
  rw [hsig] at hgamma
  rw [← hgamma]
  rw [← add_div, div_le_div_iff_of_pos_right hd]
  push_cast at hlog
  linarith

variable [Algebra F K]

/-- The finite-field estimate `an:finite-gamma`, conditional only at this stage
on comparison of the two actual completed values. -/
theorem normalized_log_relativeResidue_le_zeta_of_completion_le
    (hdegree : Module.finrank F K = 2) (ell : ℝ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hcomp : relativeCompletedReal K F ell 1 ≤ relativeCompletedReal K F ell (1+epsilon)) :
    Real.log (relativeResidue K F)/(Module.finrank ℚ F : ℝ) ≤
      Real.log (dedekindZeta K (1+epsilon)).re/(2*(Module.finrank ℚ F : ℝ)) +
        relativeGammaCorrection ell epsilon
          ((nrComplexPlaces F : ℝ)/(Module.finrank ℚ F : ℝ)) := by
  exact (normalized_log_relativeResidue_le_of_completion_le K F ell hepsilon hcomp).trans
    (add_le_add (by
      simpa only [Complex.ofReal_add, Complex.ofReal_one] using
        normalized_log_relativeZeta_le F K hdegree (s := 1+epsilon) (by linarith)) le_rfl)

end UnitDistance.NumberFieldAnalysis
