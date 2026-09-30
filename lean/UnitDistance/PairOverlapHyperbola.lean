module

public import UnitDistance.PairOverlapGaussianReduction
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section
set_option backward.privateInPublic true


/-!
# The reciprocal hyperbola integral

After the two one-coordinate Student convolutions are combined, a translation
of the logarithmic displacement makes their two positive coefficients equal.
This file proves that normalization exactly; in particular the translation
has no spurious factor of two.
-/

noncomputable section

open MeasureTheory

namespace UnitDistance

def pairHyperbolaIntegrand (A B b u : ℝ) : ℝ :=
  (1 + b * Real.exp (2 * u)) ^ (-A) *
    (1 + b * Real.exp (-2 * u)) ^ (-B)

def pairHyperbola (A B b : ℝ) : ℝ :=
  ∫ u : ℝ, pairHyperbolaIntegrand A B b u

/-- A positive geometric mean expressed in the logarithmic coordinates used
by the translation proof. -/
def pairHyperbolaMean (X Y : ℝ) : ℝ :=
  Real.exp ((Real.log X + Real.log Y) / 2)

theorem pairHyperbolaMean_pos (X Y : ℝ) : 0 < pairHyperbolaMean X Y := by
  unfold pairHyperbolaMean
  positivity

theorem pairHyperbolaMean_sq {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) :
    pairHyperbolaMean X Y ^ 2 = X * Y := by
  unfold pairHyperbolaMean
  rw [← Real.exp_nat_mul, show (2 : ℕ) * ((Real.log X + Real.log Y) / 2) =
      Real.log X + Real.log Y by norm_num; ring,
    Real.exp_add, Real.exp_log hX, Real.exp_log hY]

private theorem pairHyperbola_shift_first {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (u : ℝ) :
    X * Real.exp (2 * (u + (Real.log Y - Real.log X) / 4)) =
      pairHyperbolaMean X Y * Real.exp (2 * u) := by
  rw [show 2 * (u + (Real.log Y - Real.log X) / 4) =
      2 * u + (Real.log Y - Real.log X) / 2 by ring,
    Real.exp_add]
  have hm : X * Real.exp ((Real.log Y - Real.log X) / 2) =
      pairHyperbolaMean X Y := by
    calc
      X * Real.exp ((Real.log Y - Real.log X) / 2) =
          Real.exp (Real.log X) *
            Real.exp ((Real.log Y - Real.log X) / 2) := by rw [Real.exp_log hX]
      _ = pairHyperbolaMean X Y := by
        unfold pairHyperbolaMean
        rw [← Real.exp_add]
        congr 1
        ring
  rw [← hm]
  ring

private theorem pairHyperbola_shift_second {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (u : ℝ) :
    Y * Real.exp (-2 * (u + (Real.log Y - Real.log X) / 4)) =
      pairHyperbolaMean X Y * Real.exp (-2 * u) := by
  rw [show -2 * (u + (Real.log Y - Real.log X) / 4) =
      -2 * u + (Real.log X - Real.log Y) / 2 by ring,
    Real.exp_add]
  have hm : Y * Real.exp ((Real.log X - Real.log Y) / 2) =
      pairHyperbolaMean X Y := by
    calc
      Y * Real.exp ((Real.log X - Real.log Y) / 2) =
          Real.exp (Real.log Y) *
            Real.exp ((Real.log X - Real.log Y) / 2) := by rw [Real.exp_log hY]
      _ = pairHyperbolaMean X Y := by
        unfold pairHyperbolaMean
        rw [← Real.exp_add]
        congr 1
        ring
  rw [← hm]
  ring

/-- Translating the logarithmic displacement balances arbitrary positive
coefficients.  The Lebesgue translation contributes no scale factor. -/
theorem integral_reciprocal_powers_eq_pairHyperbola
    {A B X Y : ℝ} (hX : 0 < X) (hY : 0 < Y) :
    (∫ u : ℝ, (1 + X * Real.exp (2 * u)) ^ (-A) *
      (1 + Y * Real.exp (-2 * u)) ^ (-B)) =
        pairHyperbola A B (pairHyperbolaMean X Y) := by
  let c := (Real.log Y - Real.log X) / 4
  let F : ℝ → ℝ := fun u => (1 + X * Real.exp (2 * u)) ^ (-A) *
    (1 + Y * Real.exp (-2 * u)) ^ (-B)
  have htranslate := integral_add_right_eq_self (μ := (volume : Measure ℝ)) F c
  rw [← htranslate]
  unfold pairHyperbola
  apply integral_congr_ae
  filter_upwards with u
  unfold F c pairHyperbolaIntegrand
  rw [pairHyperbola_shift_first hX hY,
    pairHyperbola_shift_second hX hY]

theorem pairHyperbola_symm (A B b : ℝ) :
    pairHyperbola A B b = pairHyperbola B A b := by
  unfold pairHyperbola
  rw [← integral_neg_eq_self (pairHyperbolaIntegrand B A b) volume]
  apply integral_congr_ae
  filter_upwards with u
  unfold pairHyperbolaIntegrand
  ring_nf

end UnitDistance
