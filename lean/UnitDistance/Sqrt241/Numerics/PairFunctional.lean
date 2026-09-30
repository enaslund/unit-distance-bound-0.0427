module

public import UnitDistance.Sqrt241.Numerics.PairMassData
public import UnitDistance.Sqrt241.Numerics.LogConstants

@[expose] public section
set_option backward.privateInPublic true


/-!
# Lower bound for the pair functional of the ℚ(√241) witness

`JPair = log(overlap/(π²/a²)) + 2(1+δ) log q − 2δ log π + 2δ log a
− (1+δ) log(mass·q²/(π²/a²))` with `q = s·p − 1 = 12493117/10427000`.
The normalized overlap is at least `348.4186885` (the manuscript's certificate,
transferred in `PairTransfer.lean`) and the normalized mass is at most
`massUpper = 38.794821206` (the cell certificate of `PairMassData.lean`).
-/

open UnitDistance.Sqrt241.Numerics

namespace UnitDistance.Sqrt241.Witness

theorem normalizedPairOverlap_lower :
    pairOverlapNormalizedLower ≤ normalizedPairOverlap :=
  (le_div_iff₀ pairArchScale_pos).mpr pairOverlap_lower

theorem normalizedPairMass_le :
    normalizedPairMass ≤ ((MassCert.massUpper : ℚ) : ℝ) := by
  rw [normalizedPairMass_eq_betaIntegral]
  exact MassCert.pairMassBetaIntegral_le_massUpper

/-- The normalized pair mass lies below `38.794821206`. -/
theorem normalizedPairMass_le_decimal : normalizedPairMass ≤ (38794821206 / 10 ^ 9 : ℝ) := by
  have h := normalizedPairMass_le
  have hm : ((MassCert.massUpper : ℚ) : ℝ) = 38794821206 / 10 ^ 9 := by
    norm_num [MassCert.massUpper]
  rwa [hm] at h

private theorem log_overlap_lower :
    (5853404884469690049 / 10 ^ 18 : ℝ) ≤ Real.log normalizedPairOverlap := by
  have h1 := log_ge_of_le_logLo (y := 3484186885 / 10 ^ 7) (lo := 5853404884469690049 / 10 ^ 18)
    (by norm_num) (by decide +kernel)
  have hm := Real.log_le_log (by norm_num [pairOverlapNormalizedLower])
    normalizedPairOverlap_lower
  push_cast at h1
  rw [pairOverlapNormalizedLower] at hm
  linarith

private theorem log_mass_upper :
    Real.log normalizedPairMass ≤ (3658286763648606131 / 10 ^ 18 : ℝ) := by
  have h2 := log_le_of_logHi_le (y := MassCert.massUpper) (hi := 3658286763648606131 / 10 ^ 18)
    (by decide +kernel) (by decide +kernel)
  have hm := Real.log_le_log normalizedPairMass_pos normalizedPairMass_le
  push_cast at h2
  linarith

private theorem log_q_lower :
    (180779256842919415 / 10 ^ 18 : ℝ) ≤ Real.log (s * p - 1) := by
  have h1 := log_ge_of_le_logLo (y := 12493117 / 10427000) (lo := 180779256842919415 / 10 ^ 18)
    (by norm_num) (by decide +kernel)
  rw [pair_exponent_gap]
  push_cast at h1
  exact h1

private theorem log_a_lower :
    (-11261130382992931014 / 10 ^ 18 : ℝ) ≤ Real.log a := by
  have h1 := log_ge_of_le_logLo (y := 64316620879 / 5000000000000000)
    (lo := -11261130382992931014 / 10 ^ 18) (by norm_num) (by decide +kernel)
  push_cast at h1
  rw [a]
  exact h1

/-- The pair functional of the witness is at least `1.3564458712`
(floating-point value with the exact mass: `1.3564462857`). -/
theorem JPair_lower : (13564458712 / 10 ^ 10 : ℝ) ≤ JPair := by
  have hO := log_overlap_lower
  have hM := log_mass_upper
  have hq := log_q_lower
  have ha := log_a_lower
  have hπ := log_pi_bounds
  rw [JPair_eq_normalized]
  norm_num [increment] at hO hM hq ha hπ ⊢
  linarith [hπ.1, hπ.2]

end UnitDistance.Sqrt241.Witness
