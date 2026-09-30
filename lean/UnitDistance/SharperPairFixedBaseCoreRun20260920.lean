module

public import UnitDistance.PairFunctionalSharperThresholdAstra

@[expose] public section
set_option backward.privateInPublic true


/-!
# Scalar core of the sharper-pair fixed-base bridge

This lightweight research leaf isolates the only new terminal arithmetic in
the full bridge.  The existing internally proved sharper-pair margin absorbs
an additional `4e-6` in the residue ceiling.
-/

noncomputable section
set_option autoImplicit false

namespace UnitDistance.Witness

/-- The terminal scalar threshold supported by the proved sharper pair
margin. -/
def sharperFixedBaseCeilingRun20260920 : ℝ := ceiling + 4 / 10^6

theorem sharperFixedBaseCeilingRun20260920_eq :
    sharperFixedBaseCeilingRun20260920 = (42165819 : ℝ) / 10^9 := by
  norm_num [sharperFixedBaseCeilingRun20260920, ceiling]

/-- The full `4e-6` gap from the relaxed residue threshold is bounded by the
internally proved sharper-pair margin, uniformly over admissible signatures. -/
theorem sharperFixedBaseGap_le_shiftedMargin_run20260920
    {theta U : ℝ} (htheta : thetaMin ≤ theta) :
    sharperFixedBaseCeilingRun20260920 - U ≤
      margin theta - 4 * epsilon + ceiling - U := by
  have hmargin := uniform_margin_sharper_astra htheta
  unfold sharperFixedBaseCeilingRun20260920
  linarith

end UnitDistance.Witness
