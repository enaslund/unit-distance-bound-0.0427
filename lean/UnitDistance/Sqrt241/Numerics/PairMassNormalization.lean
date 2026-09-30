module

public import UnitDistance.Sqrt241.Numerics.PairTransfer
public import UnitDistance.PairBetaMoments

@[expose] public section
set_option backward.privateInPublic true


/-!
# Compact-domain normalization of the pair mass (ℚ(√241) witness)

Adapted from `UnitDistance.PairMassNormalization` for the mass exponent
`p = 2/(1+δ)` of the new witness. The profile is the manuscript's, so the
radial substitution is the same; the beta exponent is
`q = s·p − 1 = 12493117/10427000` instead of `6/5`. The result identifies the
normalized mass `pairMass / (π²/a² / q²)` with the beta-weighted unit-square
integral `∫∫ βq(t) βq(u) P(t,u)^p`, where `βq(t) = q t^(q-1)`.
-/

noncomputable section

open MeasureTheory Set

namespace UnitDistance.Sqrt241.Witness

/-- The compact radial coordinate. -/
def studentCoordinate (z : ℂ) : ℝ := (1 + a * ‖z‖ ^ 2)⁻¹

/-- One compact-coordinate slice of the exact mass integral. -/
def pairMassSlice (t : ℝ) : ℝ :=
  ∫ u in Icc (0 : ℝ) 1, u ^ (s * p - 2) * (polynomial t u) ^ p

/-- The unnormalized unit-square integral after both radial substitutions. -/
def pairMassUnitSquare : ℝ :=
  ∫ t in Icc (0 : ℝ) 1, t ^ (s * p - 2) * pairMassSlice t

/-- The beta-probability normalization of the mass. -/
def pairMassBetaIntegral : ℝ := (s * p - 1) ^ 2 * pairMassUnitSquare

/-- The literal mass with its exact radial scale removed. -/
def normalizedPairMass : ℝ := pairMass / (pairArchScale / (s * p - 1) ^ 2)

/-- The literal overlap with its exact radial scale removed. -/
def normalizedPairOverlap : ℝ := pairOverlap / pairArchScale

/-- The beta exponent `q = s·p − 1` as a real number. -/
def pairBetaExponent : ℝ := 12493117 / 10427000

theorem pairBetaExponent_eq : s * p - 1 = pairBetaExponent := by
  rw [pair_exponent_gap, pairBetaExponent]

theorem pairBetaExponent_pos : 0 < pairBetaExponent := by
  norm_num [pairBetaExponent]

theorem pairMassScale_pos : 0 < pairArchScale / (s * p - 1) ^ 2 := by
  rw [pairBetaExponent_eq]
  exact div_pos pairArchScale_pos (pow_pos pairBetaExponent_pos 2)

theorem normalizedPairMass_pos : 0 < normalizedPairMass :=
  div_pos pairMass_pos pairMassScale_pos

theorem normalizedPairOverlap_pos : 0 < normalizedPairOverlap :=
  div_pos pairOverlap_pos pairArchScale_pos

theorem student_coordinate_bounds (z : ℂ) :
    0 < (1 + a * ‖z‖ ^ 2)⁻¹ ∧ (1 + a * ‖z‖ ^ 2)⁻¹ ≤ 1 := by
  rw [a_eq_manuscript]
  exact _root_.UnitDistance.Witness.student_coordinate_bounds z

theorem complex_student_coordinate_integral (f : ℝ → ℝ) :
    (∫ z : ℂ, f (1 + a * ‖z‖ ^ 2)⁻¹) =
      (Real.pi / a) * ∫ t in Ioo (0 : ℝ) 1, (t ^ 2)⁻¹ * f t := by
  rw [a_eq_manuscript]
  exact _root_.UnitDistance.Witness.complex_student_coordinate_integral f

theorem pairProfile_rpow_radial (z : ℂ × ℂ) :
    pairProfile z ^ p =
      studentCoordinate z.1 ^ (s * p) * studentCoordinate z.2 ^ (s * p) *
        (polynomial (studentCoordinate z.1) (studentCoordinate z.2)) ^ p := by
  obtain ⟨ht0, ht1⟩ := student_coordinate_bounds z.1
  obtain ⟨hu0, hu1⟩ := student_coordinate_bounds z.2
  have hP := (polynomial_bounds ht0.le ht1 hu0.le hu1).1
  change ((1 + a * ‖z.1‖ ^ 2)⁻¹ ^ s * (1 + a * ‖z.2‖ ^ 2)⁻¹ ^ s *
      polynomial (1 + a * ‖z.1‖ ^ 2)⁻¹ (1 + a * ‖z.2‖ ^ 2)⁻¹) ^ p = _
  unfold studentCoordinate
  rw [Real.mul_rpow (mul_nonneg (Real.rpow_nonneg ht0.le _) (Real.rpow_nonneg hu0.le _))
      (by linarith), Real.mul_rpow (Real.rpow_nonneg ht0.le _) (Real.rpow_nonneg hu0.le _),
    ← Real.rpow_mul ht0.le, ← Real.rpow_mul hu0.le]

private theorem rpow_sub_two {t q : ℝ} (ht : 0 < t) :
    (t ^ 2)⁻¹ * t ^ q = t ^ (q - 2) := by
  rw [Real.rpow_sub ht, Real.rpow_two]
  field_simp

theorem pairMass_inner (z : ℂ) :
    (∫ w : ℂ, pairProfile (z, w) ^ p) =
      (Real.pi / a) * studentCoordinate z ^ (s * p) *
        pairMassSlice (studentCoordinate z) := by
  let t := studentCoordinate z
  let F : ℝ → ℝ := fun u => t ^ (s * p) * u ^ (s * p) * (polynomial t u) ^ p
  calc
    (∫ w : ℂ, pairProfile (z, w) ^ p) =
        ∫ w : ℂ, F (studentCoordinate w) := by
      apply integral_congr_ae
      filter_upwards with w
      exact pairProfile_rpow_radial (z, w)
    _ = (Real.pi / a) * ∫ u in Ioo (0 : ℝ) 1, (u ^ 2)⁻¹ * F u := by
      simpa only [studentCoordinate] using complex_student_coordinate_integral F
    _ = (Real.pi / a) * t ^ (s * p) * pairMassSlice t := by
      rw [pairMassSlice, integral_Icc_eq_integral_Ioc, integral_Ioc_eq_integral_Ioo, mul_assoc]
      congr 1
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro u hu
      simp only [F]
      calc
        _ = t ^ (s * p) * ((u ^ 2)⁻¹ * u ^ (s * p)) * (polynomial t u) ^ p := by ring
        _ = _ := by rw [rpow_sub_two hu.1]; ring

theorem pairMass_eq_pairArchScale_mul_unitSquare :
    pairMass = pairArchScale * pairMassUnitSquare := by
  unfold pairMass
  change (∫ z : ℂ × ℂ, pairProfile z ^ p ∂(volume.prod volume)) = _
  rw [integral_prod _ integrable_pairMass]
  calc
    (∫ z : ℂ, ∫ w : ℂ, pairProfile (z, w) ^ p) =
        ∫ z : ℂ, (Real.pi / a) *
          (studentCoordinate z ^ (s * p) * pairMassSlice (studentCoordinate z)) := by
      apply integral_congr_ae
      filter_upwards with z
      rw [pairMass_inner]
      ring
    _ = (Real.pi / a) *
        ∫ z : ℂ, studentCoordinate z ^ (s * p) * pairMassSlice (studentCoordinate z) := by
      rw [integral_const_mul]
    _ = (Real.pi / a) * ((Real.pi / a) *
        ∫ t in Ioo (0 : ℝ) 1,
          (t ^ 2)⁻¹ * (t ^ (s * p) * pairMassSlice t)) := by
      congr 1
      simpa only [studentCoordinate] using
        (complex_student_coordinate_integral
          (fun t => t ^ (s * p) * pairMassSlice t))
    _ = pairArchScale * pairMassUnitSquare := by
      have hcompact : (∫ t in Ioo (0 : ℝ) 1,
          (t ^ 2)⁻¹ * (t ^ (s * p) * pairMassSlice t)) = pairMassUnitSquare := by
        rw [pairMassUnitSquare, integral_Icc_eq_integral_Ioc, integral_Ioc_eq_integral_Ioo]
        apply setIntegral_congr_fun measurableSet_Ioo
        intro t ht
        change (t ^ 2)⁻¹ * (t ^ (s * p) * pairMassSlice t) =
          t ^ (s * p - 2) * pairMassSlice t
        calc
          _ = ((t ^ 2)⁻¹ * t ^ (s * p)) * pairMassSlice t := by ring
          _ = _ := by rw [rpow_sub_two ht.1]
      rw [hcompact]
      unfold pairArchScale
      field_simp

/-- The exact normalized mass is the beta-weighted unit-square integral. -/
theorem normalizedPairMass_eq_betaIntegral :
    normalizedPairMass = pairMassBetaIntegral := by
  rw [normalizedPairMass, pairMass_eq_pairArchScale_mul_unitSquare]
  unfold pairMassBetaIntegral
  have hscale := pairArchScale_pos.ne'
  have hgap : s * p - 1 ≠ 0 := by rw [pairBetaExponent_eq]; exact pairBetaExponent_pos.ne'
  field_simp

/-- The normalized mass as an iterated integral against two `Beta(q,1)`
densities, `q = 12493117/10427000`. -/
theorem pairMassBetaIntegral_eq_iterated :
    pairMassBetaIntegral =
      ∫ t in Icc (0 : ℝ) 1, ∫ u in Icc (0 : ℝ) 1,
        _root_.UnitDistance.Witness.betaDensity pairBetaExponent t *
          _root_.UnitDistance.Witness.betaDensity pairBetaExponent u *
            (polynomial t u) ^ p := by
  have hexp : s * p - 2 = pairBetaExponent - 1 := by
    rw [← pairBetaExponent_eq]; ring
  unfold pairMassBetaIntegral pairMassUnitSquare
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  change (s * p - 1) ^ 2 * (t ^ (s * p - 2) * pairMassSlice t) =
    ∫ u in Icc (0 : ℝ) 1,
      _root_.UnitDistance.Witness.betaDensity pairBetaExponent t *
        _root_.UnitDistance.Witness.betaDensity pairBetaExponent u * (polynomial t u) ^ p
  rw [pairMassSlice, ← integral_const_mul, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro u hu
  simp only [_root_.UnitDistance.Witness.betaDensity, pairBetaExponent_eq, hexp]
  ring

theorem JPair_eq_normalized :
    JPair = Real.log normalizedPairOverlap
      + 2 * (1 + increment) * Real.log (s * p - 1)
      - 2 * increment * Real.log Real.pi
      + 2 * increment * Real.log a
      - (1 + increment) * Real.log normalizedPairMass := by
  have ha : a ≠ 0 := ne_of_gt witness_basic.2.1
  have hgap : s * p - 1 ≠ 0 := by rw [pairBetaExponent_eq]; exact pairBetaExponent_pos.ne'
  have hscale : pairArchScale ≠ 0 := ne_of_gt pairArchScale_pos
  have hmassScale : pairArchScale / (s * p - 1) ^ 2 ≠ 0 :=
    div_ne_zero hscale (pow_ne_zero 2 hgap)
  have hO : pairOverlap = normalizedPairOverlap * pairArchScale := by
    rw [normalizedPairOverlap, div_mul_cancel₀ _ hscale]
  have hM : pairMass = normalizedPairMass *
      (pairArchScale / (s * p - 1) ^ 2) := by
    rw [normalizedPairMass, div_mul_cancel₀ _ hmassScale]
  have hscaleLog : Real.log pairArchScale =
      2 * Real.log Real.pi - 2 * Real.log a := by
    rw [pairArchScale, Real.log_div (pow_ne_zero 2 Real.pi_ne_zero) (pow_ne_zero 2 ha),
      Real.log_pow, Real.log_pow]
    ring
  have hmassScaleLog : Real.log (pairArchScale / (s * p - 1) ^ 2) =
      2 * Real.log Real.pi - 2 * Real.log a - 2 * Real.log (s * p - 1) := by
    rw [Real.log_div hscale (pow_ne_zero 2 hgap), Real.log_pow, hscaleLog]
    ring
  rw [JPair, hO, hM,
    Real.log_mul (ne_of_gt normalizedPairOverlap_pos) hscale,
    Real.log_mul (ne_of_gt normalizedPairMass_pos) hmassScale,
    hscaleLog, hmassScaleLog]
  ring

end UnitDistance.Sqrt241.Witness
