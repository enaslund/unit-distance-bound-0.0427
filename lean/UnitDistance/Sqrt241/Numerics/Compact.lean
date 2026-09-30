module

public import UnitDistance.Sqrt241.Witness
public import UnitDistance.GaussianProfiles

@[expose] public section
set_option backward.privateInPublic true


/-!
# The compact-place Gaussian functional of the ℚ(√241) witness

Adapted from the witness part of `UnitDistance.GaussianProfiles` and from
`UnitDistance.NumericalReduction.JCompact_log_eq`. The generic complex Gaussian
integrals (`UnitDistance.complexGaussian_*`) are reused; only the witness
constants change (`δ = 427/10000`, `p = 2/(1+δ)`). The result is the closed form

  `JCompact = −δ − δ log π + δ log(4δ) − (1+δ) log(1+δ)`.
-/

open MeasureTheory

namespace UnitDistance.Sqrt241.Witness

theorem compactProfile_gaussian (z : ℂ) :
    compactProfile z = UnitDistance.complexGaussian (2 * increment) z := by
  simp only [compactProfile, aCompact, UnitDistance.complexGaussian]
  congr 1
  have hp : p ≠ 0 := ne_of_gt witness_basic.2.2.1
  field_simp

theorem compactMass_integrable : Integrable (fun z : ℂ => compactProfile z ^ p) := by
  simp_rw [compactProfile_gaussian]
  exact UnitDistance.complexGaussian_moment_integrable (by positivity [increment_pos])
    witness_basic.2.2.1

theorem compactOverlap_integrable :
    Integrable (fun z : ℂ => compactProfile z * compactProfile (z + 1)) := by
  simp_rw [compactProfile_gaussian]
  exact UnitDistance.complexGaussian_overlap_integrable (by positivity [increment_pos])

theorem compactMass_eq : compactMass = Real.pi / (2 * increment * p) := by
  simp only [compactMass, compactProfile_gaussian]
  exact UnitDistance.complexGaussian_moment (by positivity [increment_pos]) witness_basic.2.2.1

theorem compactOverlap_eq :
    compactOverlap = Real.exp (-increment) * (Real.pi / (4 * increment)) := by
  simp only [compactOverlap, compactProfile_gaussian]
  rw [UnitDistance.complexGaussian_overlap (by positivity [increment_pos])]
  congr 1 <;> congr 1 <;> ring

theorem compactMass_pos : 0 < compactMass := by
  rw [compactMass_eq]
  positivity [increment_pos, witness_basic.2.2.1]

theorem compactOverlap_pos : 0 < compactOverlap := by
  rw [compactOverlap_eq]
  positivity [increment_pos, Real.pi_pos]

theorem JCompact_eq : JCompact =
    -increment + Real.log (Real.pi / (4 * increment)) -
      (1 + increment) * Real.log (Real.pi / (2 * increment * p)) := by
  rw [JCompact, compactMass_eq, compactOverlap_eq,
    Real.log_mul (Real.exp_ne_zero _) (ne_of_gt (by positivity [increment_pos, Real.pi_pos])),
    Real.log_exp]

/-- Closed form of the compact functional in three logarithms. -/
theorem JCompact_log_eq : JCompact =
    -increment - increment * Real.log Real.pi + increment * Real.log (4 * increment) -
      (1 + increment) * Real.log (1 + increment) := by
  have hd := increment_pos
  have h2 : Real.log (2 * increment * p) =
      Real.log (4 * increment) - Real.log (1 + increment) := by
    rw [show 2 * increment * p = 4 * increment / (1 + increment) by unfold p; ring,
      Real.log_div (by positivity) (by positivity)]
  rw [JCompact_eq, Real.log_div Real.pi_ne_zero (by positivity),
    Real.log_div Real.pi_ne_zero (by positivity [witness_basic.2.2.1]), h2]
  ring

end UnitDistance.Sqrt241.Witness
