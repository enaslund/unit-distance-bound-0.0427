module

public import UnitDistance.Sqrt241.Numerics.PairFunctional
public import UnitDistance.Sqrt241.Numerics.Compact
public import UnitDistance.Sqrt241.FiniteFunctionalCertificate

@[expose] public section
set_option backward.privateInPublic true


/-!
# The uniform margin of the ℚ(√241) witness

Port of `UnitDistance.Certificate` (`margin_mono`, `margin_at_min`,
`uniform_margin`) with every numerical input proved:

* `finiteProfit_lower` (`FiniteFunctionalCertificate.lean`): `0.721977083 ≤ finiteProfit`;
* `JCompact_bounds`: the closed form of the Gaussian functional;
* `JPair_lower`: `1.3564458712 ≤ JPair`;
* `logRD_bounds`, `log_two_bounds`, `log_pi_bounds` (`LogConstants.lean`).

At `θ = thetaMin = 65535/131072` the margin after the concentration loss `4ε`
exceeds `0.0496189 − ceiling` (`margin_at_min_threshold`, proved without
unfolding `ceiling`), hence `κ = 0.0001189` at `ceiling = 0.0495`; the θ-slope
`−log π − 2 JCompact + JPair` is positive, so the bounds hold for all
`θ ≥ thetaMin`. Floating-point value of the margin with the exact functionals:
`0.00011917` at `ceiling = 0.0495`.
-/

namespace UnitDistance.Sqrt241.Witness

/-- Enclosure of the compact functional `JCompact ≈ −0.21064099280801`. -/
theorem JCompact_bounds :
    (-2106409928080139 / 10 ^ 16 : ℝ) ≤ JCompact ∧ JCompact ≤ (-2106409928080137 / 10 ^ 16 : ℝ) := by
  have hπ := log_pi_bounds
  have h4 := log_four_increment_bounds
  have h1 := log_one_add_increment_bounds
  rw [JCompact_log_eq]
  norm_num [increment] at hπ h4 h1 ⊢
  constructor <;> nlinarith [hπ.1, hπ.2, h4.1, h4.2, h1.1, h1.2]

/-- The coefficient of `θ` in `margin θ` is positive. -/
theorem signature_slope_pos : 0 < -Real.log Real.pi - 2 * JCompact + JPair := by
  have hπ := log_pi_bounds
  have hC := JCompact_bounds
  have hD := JPair_lower
  linarith [hπ.2, hC.2]

/-- Explicit lower bound for the θ-slope. -/
theorem signature_slope_lower :
    (63 / 100 : ℝ) < -Real.log Real.pi - 2 * JCompact + JPair := by
  have hπ := log_pi_bounds
  have hC := JCompact_bounds
  have hD := JPair_lower
  linarith [hπ.2, hC.2]

theorem margin_mono : Monotone margin := by
  intro θ θ' hθ
  have hs := signature_slope_pos
  have hx := mul_nonneg (sub_nonneg.mpr hθ) hs.le
  dsimp [margin]
  nlinarith

/-- The margin at the minimal signature ratio, with the analytic ceiling kept
symbolic: every ceiling below the geometric threshold `0.0496189` leaves a
positive margin. The proof does not unfold `ceiling`. -/
theorem margin_at_min_threshold :
    (496189 / 10 ^ 7 : ℝ) - ceiling < margin thetaMin - 4 * epsilon := by
  have hF := finiteProfit_lower
  have hℓ := logRD_bounds
  have h2 := log_two_bounds
  have hπ := log_pi_bounds
  have hC := JCompact_bounds
  have hD := JPair_lower
  norm_num [margin, thetaMin, epsilon, increment] at hF hℓ h2 hπ hC hD ⊢
  linarith [hℓ.2, h2.1, hπ.1, hC.1]

/-- The threshold form for every signature ratio `θ ≥ thetaMin`. -/
theorem uniform_threshold (θ : ℝ) (hθ : thetaMin ≤ θ) :
    (496189 / 10 ^ 7 : ℝ) - ceiling < margin θ - 4 * epsilon := by
  have hm := margin_mono hθ
  have hb := margin_at_min_threshold
  linarith

/-- The margin at the minimal signature ratio and `ceiling = 0.0495`. -/
theorem margin_at_min : (1189 / 10 ^ 7 : ℝ) < margin thetaMin - 4 * epsilon := by
  have h := margin_at_min_threshold
  norm_num [ceiling] at h ⊢
  linarith

/-- **Uniform margin.** For every signature ratio `θ ≥ thetaMin`, the margin of
the ℚ(√241) witness after the concentration loss `4ε` exceeds `κ = 0.0001189`. -/
theorem uniform_margin (θ : ℝ) (hθ : thetaMin ≤ θ) :
    (1189 / 10 ^ 7 : ℝ) < margin θ - 4 * epsilon := by
  have hm := margin_mono hθ
  have hb := margin_at_min
  linarith

end UnitDistance.Sqrt241.Witness
