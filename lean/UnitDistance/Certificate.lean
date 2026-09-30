module

public import UnitDistance.Witness

@[expose] public section
set_option backward.privateInPublic true


/-!
# Sound assembly from explicit numerical inequalities

These hypotheses are finite inequalities about the independently defined
profile integrals, finite shell expression, and ordinary logarithms in
`Witness.lean`. They are not certificate hashes or replay success flags.
This module proves only a positive margin; it supplies neither a tower nor
the analytic family ceiling nor the geometric construction.

The enclosures below deliberately use fewer digits than the publication.
They leave a uniform post-concentration margin greater than 0.00000533.
The integral interpretation still requires the separately tracked profile
integrability/positivity and normalization results.
-/

namespace UnitDistance.Witness

structure NumericalBounds : Prop where
  logTwo : (693147180559 : ℝ) / 10^12 ≤ Real.log 2 ∧
    Real.log 2 ≤ (693147180560 : ℝ) / 10^12
  logDiscriminantFactor : Real.log 15015 ≤ (9616804980418 : ℝ) / 10^12
  logPi : (1144729885849 : ℝ) / 10^12 ≤ Real.log Real.pi ∧
    Real.log Real.pi ≤ (1144729885850 : ℝ) / 10^12
  compactFunctional : -(207166792766 : ℝ) / 10^12 ≤ JCompact ∧
    JCompact ≤ -(207166792765 : ℝ) / 10^12
  pairFunctional : (1379635324335 : ℝ) / 10^12 ≤ JPair
  finiteFunctional : (1033566922503 : ℝ) / 10^12 ≤ finiteProfit

theorem signature_slope_pos (h : NumericalBounds) :
    0 < -Real.log Real.pi - 2*JCompact + JPair := by
  have hπ := h.logPi.2
  have hC := h.compactFunctional.2
  have hD := h.pairFunctional
  linarith

theorem margin_mono (h : NumericalBounds) : Monotone margin := by
  intro θ θ' hθ
  have hs := signature_slope_pos h
  have hx := mul_nonneg (sub_nonneg.mpr hθ) hs.le
  dsimp [margin]
  nlinarith

theorem margin_at_min (h : NumericalBounds) :
    (533 : ℝ) / 10^8 < margin thetaMin - 4*epsilon := by
  have h2l := h.logTwo.1
  have h2u := h.logTwo.2
  have h15 := h.logDiscriminantFactor
  have hπ := h.logPi.1
  have hC := h.compactFunctional.1
  have hD := h.pairFunctional
  have hF := h.finiteFunctional
  norm_num [margin, thetaMin, epsilon, logRD, ceiling, increment] at *
  linarith

/-- Exact uniform margin assembly over the signature range of the paper.
No claim of existence of fields with these signatures is made here. -/
theorem uniform_margin (h : NumericalBounds) {θ : ℝ} (hθ : thetaMin ≤ θ) :
    (533 : ℝ) / 10^8 < margin θ - 4*epsilon := by
  have hm := margin_mono h hθ
  have hb := margin_at_min h
  linarith

end UnitDistance.Witness
