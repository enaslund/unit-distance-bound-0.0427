module

public import UnitDistance.GaussianProfiles
public import UnitDistance.ProfileOverlap

@[expose] public section
set_option backward.privateInPublic true


/-! # Compact windows of the actual angular Gaussian profile -/

namespace UnitDistance

/-- Positive quadratic energies have compact sublevel windows. -/
theorem isCompact_quadratic_energyWindow {b : ℝ} (hb : 0 < b) (T : ℝ) :
    IsCompact (energyWindow (fun z : ℂ => b*‖z‖^2) T) := by
  let R := Real.sqrt (max T 0/b)
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have hsqR : R^2 = max T 0/b := Real.sq_sqrt (div_nonneg (le_max_right _ _) hb.le)
  have hm : Continuous (fun z : ℂ => b*‖z‖^2) := by fun_prop
  apply (isCompact_closedBall (0:ℂ) R).of_isClosed_subset
    (isClosed_le hm continuous_const)
  intro z hz
  have he : b*‖z‖^2 ≤ T := hz
  have hs : ‖z‖^2 ≤ max T 0/b := by
    apply (le_div_iff₀ hb).mpr
    nlinarith [le_max_left T 0]
  have hn : ‖z‖ ≤ R := (sq_le_sq₀ (norm_nonneg _) hR).mp (by simpa only [hsqR] using hs)
  simpa only [Metric.mem_closedBall, dist_zero_right] using hn

namespace Witness

/-- The actual compact-coordinate logarithmic profile energy is quadratic. -/
theorem compactProfile_energy (z : ℂ) :
    -Real.log (compactProfile z) = (2*increment)*‖z‖^2 := by
  rw [compactProfile_gaussian, complexGaussian, Real.log_exp]
  ring

theorem compactProfile_energy_nonneg (z : ℂ) : 0 ≤ -Real.log (compactProfile z) := by
  rw [compactProfile_energy]
  exact mul_nonneg (mul_nonneg (by norm_num) increment_pos.le) (sq_nonneg _)

theorem isCompact_compactProfile_energyWindow (T : ℝ) :
    IsCompact (energyWindow (fun z : ℂ => -Real.log (compactProfile z)) T) := by
  have he : (fun z : ℂ => -Real.log (compactProfile z)) =
      (fun z : ℂ => (2*increment)*‖z‖^2) := funext compactProfile_energy
  rw [he]
  exact isCompact_quadratic_energyWindow (mul_pos (by norm_num) increment_pos) T

end Witness
end UnitDistance
