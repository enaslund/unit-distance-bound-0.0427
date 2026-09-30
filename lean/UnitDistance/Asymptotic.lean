module

public import UnitDistance.Counting
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Order.Filter.AtTopBot.Field

@[expose] public section
set_option backward.privateInPublic true


/-!
# Exact energy cancellation and sequence quantifiers

This is assembly infrastructure. The exponential lower bound in the last
lemma must come from the proved geometric transfer; it is not an arithmetic
input or a replacement for constructing the windows.
-/

open Filter

namespace UnitDistance

theorem energy_cancellation (p δ mean r : ℝ) (hp : p*(1+δ) = 2) :
    Real.exp (2*(mean-r)) / (Real.exp (p*(mean+r)))^(1+δ) =
      Real.exp (-4*r) := by
  rw [← Real.exp_mul, ← Real.exp_sub]
  congr 1
  calc
    2*(mean-r) - p*(mean+r)*(1+δ) =
      2*(mean-r) - (p*(1+δ))*(mean+r) := by ring
    _ = -4*r := by rw [hp]; ring

/-- Exact cancellation of the mean energy, all factors two included.
`M` is the norm-one mass density and `D` the lattice covolume. -/
theorem weighted_ratio_identity (M Z A D p δ mean r : ℝ)
    (hA : 0 < A) (hD : 0 < D) (hp : p*(1+δ) = 2) :
    (M * Z * Real.exp (2*(mean-r)) / (2*A*Real.exp (p*(mean+r)))) /
      (2 * (2*A*Real.exp (p*(mean+r))/D)^δ) =
    M * D^δ / (2:ℝ)^(2+δ) * (Z/A^(1+δ)) * Real.exp (-4*r) := by
  have hT : 0 < Real.exp (p*(mean+r)) := Real.exp_pos _
  have h2 : (0:ℝ) < 2 := by norm_num
  rw [Real.div_rpow (by positivity) hD.le,
    Real.mul_rpow (by positivity) hT.le,
    Real.mul_rpow h2.le hA.le,
    Real.rpow_add h2, Real.rpow_two,
    Real.rpow_add hA, Real.rpow_one]
  have he := energy_cancellation p δ mean r hp
  rw [Real.rpow_add hT, Real.rpow_one] at he
  have hpowT := Real.rpow_pos_of_pos hT δ
  have he' : Real.exp (2*(mean-r)) =
      Real.exp (-4*r) * (Real.exp (p*(mean+r)) * Real.exp (p*(mean+r))^δ) :=
    (div_eq_iff (mul_ne_zero hT.ne' hpowT.ne')).mp he
  rw [he']
  field_simp

/-- A positive exponential margin implies both limits required for the
sequence conclusion, with exact real powers and unordered counts. -/
theorem sequence_limits_of_exponential_lower_bound
    (U : ℕ → Finset ℂ) (d : ℕ → ℝ) (a c η : ℝ)
    (ha : 0 ≤ a) (hc : 0 < c) (hη : 0 < η)
    (hd : Tendsto d atTop atTop)
    (hbound : ∀ᶠ j in atTop, c * Real.exp (η*d j) ≤
      unitPairs (U j) / ((U j).card : ℝ)^a) :
    Tendsto (fun j => (U j).card) atTop atTop ∧
    Tendsto (fun j => unitPairs (U j) / ((U j).card : ℝ)^a) atTop atTop := by
  have hgrowth : Tendsto (fun j => c * Real.exp (η*d j)) atTop atTop :=
    Tendsto.const_mul_atTop hc (Real.tendsto_exp_atTop.comp (Tendsto.const_mul_atTop hη hd))
  have hratio := tendsto_atTop_mono' atTop hbound hgrowth
  exact ⟨card_tendsto_of_ratio_tendsto U ha hratio, hratio⟩

end UnitDistance
