module

public import UnitDistance.PairFunctionalCertificate
public import UnitDistance.StudentComplexRealRestriction
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section
set_option backward.privateInPublic true


/-!
# Compact-domain normalization of the pair mass

This file identifies the dimensionless mass in
`PairFunctionalCertificate.lean` with the beta-weighted unit-square integral
used by the finite binomial certificate.
-/

noncomputable section

open MeasureTheory Set

namespace UnitDistance.Witness

/-- The compact radial coordinate used in the profile certificate. -/
def studentCoordinate (z : ℂ) : ℝ := (1 + a * ‖z‖ ^ 2)⁻¹

/-- One compact-coordinate slice of the exact mass integral. -/
def pairMassSlice (t : ℝ) : ℝ :=
  ∫ u in Icc (0 : ℝ) 1,
    u ^ (s * p - 2) * (polynomial t u) ^ p

/-- The unnormalized unit-square integral after both radial substitutions. -/
def pairMassUnitSquare : ℝ :=
  ∫ t in Icc (0 : ℝ) 1, t ^ (s * p - 2) * pairMassSlice t

/-- The beta-probability normalization used by the finite mass certificate. -/
def pairMassBetaIntegral : ℝ := (s * p - 1) ^ 2 * pairMassUnitSquare

/-- The `Beta(s*p-1, 1)` density on the unit interval. -/
def pairBetaDensity (t : ℝ) : ℝ := (s * p - 1) * t ^ (s * p - 2)

theorem pairBetaDensity_eq (t : ℝ) :
    pairBetaDensity t = (6 / 5 : ℝ) * t ^ (1 / 5 : ℝ) := by
  have hexp : s * p - 2 = (1 / 5 : ℝ) := by
    linarith [pairExponentGap]
  rw [pairBetaDensity, pairExponentGap, hexp]

private theorem complex_radial_integral (f : ℝ → ℝ) :
    (∫ z : ℂ, f ‖z‖) =
      2 * Real.pi * ∫ r in Ioi (0 : ℝ), r * f r := by
  rw [integral_fun_norm_addHaar (volume : Measure ℂ) f]
  simp [Complex.finrank_real_complex, Measure.real_def]
  ring_nf

private theorem complex_radial_sq_integral (f : ℝ → ℝ) :
    (∫ z : ℂ, f (‖z‖ ^ 2)) =
      Real.pi * ∫ x in Ioi (0 : ℝ), f x := by
  rw [complex_radial_integral (fun r => f (r ^ 2))]
  have h := integral_comp_rpow_Ioi_of_pos (g := f) (p := (2 : ℝ)) (by norm_num)
  norm_num [Real.rpow_two] at h
  calc
    _ = Real.pi * (∫ r in Ioi (0 : ℝ), 2 * (r * f (r ^ 2))) := by
      rw [integral_const_mul]
      ring
    _ = _ := by simpa only [mul_assoc] using congrArg (Real.pi * ·) h

private theorem complex_scaled_radial_sq_integral {c : ℝ} (hc : 0 < c) (f : ℝ → ℝ) :
    (∫ z : ℂ, f (c * ‖z‖ ^ 2)) =
      (Real.pi / c) * ∫ x in Ioi (0 : ℝ), f x := by
  rw [complex_radial_sq_integral (fun x => f (c * x)),
    integral_comp_mul_left_Ioi f 0 hc]
  simp only [mul_zero, smul_eq_mul]
  field_simp

private theorem integral_Ioi_one_add_inv (f : ℝ → ℝ) :
    (∫ x in Ioi (0 : ℝ), f (1 + x)⁻¹) =
      ∫ t in Ioo (0 : ℝ) 1, (t ^ 2)⁻¹ * f t := by
  let φ : ℝ → ℝ := fun t => t⁻¹ - 1
  have hφ : φ '' Ioo (0 : ℝ) 1 = Ioi 0 := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact sub_pos.mpr ((one_lt_inv₀ ht.1).mpr ht.2)
    · intro hx
      change 0 < x at hx
      refine ⟨(1 + x)⁻¹, ?_, ?_⟩
      · constructor
        · positivity
        · exact (inv_lt_one₀ (by linarith : 0 < 1 + x)).mpr (by linarith)
      · simp only [φ, inv_inv]
        ring
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivWithinAt φ (-(t ^ 2)⁻¹) (Ioo (0 : ℝ) 1) t := by
    intro t ht
    exact ((hasDerivAt_inv ht.1.ne').sub_const 1).hasDerivWithinAt
  have hinj : Set.InjOn φ (Ioo (0 : ℝ) 1) := by
    intro t ht u hu h
    apply inv_injective
    dsimp only [φ] at h
    linarith
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj
    (fun x => f (1 + x)⁻¹)
  rw [hφ] at h
  rw [h]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  change |(-(t ^ 2)⁻¹)| • f (1 + φ t)⁻¹ = (t ^ 2)⁻¹ * f t
  rw [abs_neg, abs_inv, abs_pow, abs_of_pos ht.1]
  simp only [smul_eq_mul, φ]
  congr 1
  field_simp [ht.1.ne']
  ring_nf

theorem complex_student_coordinate_integral (f : ℝ → ℝ) :
    (∫ z : ℂ, f (1 + a * ‖z‖ ^ 2)⁻¹) =
      (Real.pi / a) * ∫ t in Ioo (0 : ℝ) 1, (t ^ 2)⁻¹ * f t := by
  rw [complex_scaled_radial_sq_integral witness_basic.2.1
    (fun x => f (1 + x)⁻¹), integral_Ioi_one_add_inv]

theorem pairProfile_rpow_radial (z : ℂ × ℂ) :
    pairProfile z ^ p =
      studentCoordinate z.1 ^ (s * p) * studentCoordinate z.2 ^ (s * p) *
        (polynomial (studentCoordinate z.1) (studentCoordinate z.2)) ^ p := by
  rw [pairProfile_rpow_identity]
  have hbase (w : ℂ) : 0 ≤ 1 + a * ‖w‖ ^ 2 := by
    have ha := witness_basic.2.1
    positivity
  unfold studentCoordinate
  simp only [neg_mul]
  rw [Real.rpow_neg (hbase z.1), ← Real.inv_rpow (hbase z.1),
    Real.rpow_neg (hbase z.2), ← Real.inv_rpow (hbase z.2)]

private theorem rpow_sub_two {t q : ℝ} (ht : 0 < t) :
    (t ^ 2)⁻¹ * t ^ q = t ^ (q - 2) := by
  rw [Real.rpow_sub ht, Real.rpow_two]
  field_simp

theorem pairMass_inner (z : ℂ) :
    (∫ w : ℂ, pairProfile (z, w) ^ p) =
      (Real.pi / a) * studentCoordinate z ^ (s * p) * pairMassSlice (studentCoordinate z) := by
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

/-- The exact normalized mass is the beta-weighted bounded-square integral.
This is the analytic bridge from the literal integral in `Witness.lean` to
the quantity evaluated by the finite binomial certificate. -/
theorem normalizedPairMass_eq_betaIntegral :
    normalizedPairMass = pairMassBetaIntegral := by
  rw [normalizedPairMass, pairMass_eq_pairArchScale_mul_unitSquare]
  unfold pairMassBetaIntegral
  have hscale := pairArchScale_pos.ne'
  have hgap : s * p - 1 ≠ 0 := by rw [pairExponentGap]; norm_num
  field_simp

theorem pairMassBetaIntegral_eq_iterated :
    pairMassBetaIntegral =
      ∫ t in Icc (0 : ℝ) 1, ∫ u in Icc (0 : ℝ) 1,
        pairBetaDensity t * pairBetaDensity u * (polynomial t u) ^ p := by
  unfold pairMassBetaIntegral pairMassUnitSquare
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  change (s * p - 1) ^ 2 * (t ^ (s * p - 2) * pairMassSlice t) =
    ∫ u in Icc (0 : ℝ) 1,
      pairBetaDensity t * pairBetaDensity u * (polynomial t u) ^ p
  rw [pairMassSlice]
  simp only [pairBetaDensity]
  rw [show (fun u =>
      ((s * p - 1) * t ^ (s * p - 2)) *
        ((s * p - 1) * u ^ (s * p - 2)) * (polynomial t u) ^ p) =
      (fun u => ((s * p - 1) ^ 2 * t ^ (s * p - 2)) *
        (u ^ (s * p - 2) * (polynomial t u) ^ p)) by
      funext u; ring]
  rw [integral_const_mul]
  ring

theorem pairMassBetaIntegral_eq_explicit :
    pairMassBetaIntegral =
      ∫ t in Icc (0 : ℝ) 1, ∫ u in Icc (0 : ℝ) 1,
        ((6 / 5 : ℝ) * t ^ (1 / 5 : ℝ)) *
          ((6 / 5 : ℝ) * u ^ (1 / 5 : ℝ)) * (polynomial t u) ^ p := by
  rw [pairMassBetaIntegral_eq_iterated]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  apply setIntegral_congr_fun measurableSet_Icc
  intro u hu
  change pairBetaDensity t * pairBetaDensity u * (polynomial t u) ^ p =
    ((6 / 5 : ℝ) * t ^ (1 / 5 : ℝ)) *
      ((6 / 5 : ℝ) * u ^ (1 / 5 : ℝ)) * (polynomial t u) ^ p
  rw [pairBetaDensity_eq, pairBetaDensity_eq]

theorem normalizedPairMass_interval_iff_betaIntegral :
    normalizedPairMass ≤ normalizedPairMassUpper ↔
      pairMassBetaIntegral ≤ normalizedPairMassUpper := by
  rw [normalizedPairMass_eq_betaIntegral]

/-- A compact unit-square mass enclosure, together with the independently
normalized overlap enclosure, implies the original pair-functional premise. -/
theorem pairFunctional_of_betaMass_interval
    (hoverlap : normalizedPairOverlapLower ≤ normalizedPairOverlap)
    (hmass : pairMassBetaIntegral ≤ normalizedPairMassUpper) :
    (1379635324335 : ℝ) / 10 ^ 12 ≤ JPair :=
  pairFunctional_of_normalized_intervals hoverlap
    (normalizedPairMass_interval_iff_betaIntegral.mpr hmass)

theorem pairFunctional_of_explicitBetaMass_interval
    (hoverlap : normalizedPairOverlapLower ≤ normalizedPairOverlap)
    (hmass : (∫ t in Icc (0 : ℝ) 1, ∫ u in Icc (0 : ℝ) 1,
      ((6 / 5 : ℝ) * t ^ (1 / 5 : ℝ)) *
        ((6 / 5 : ℝ) * u ^ (1 / 5 : ℝ)) * (polynomial t u) ^ p) ≤
      normalizedPairMassUpper) :
    (1379635324335 : ℝ) / 10 ^ 12 ≤ JPair := by
  apply pairFunctional_of_betaMass_interval hoverlap
  rwa [pairMassBetaIntegral_eq_explicit]

/-- Final two-premise reduction: one lower bound for the literal overlap
integral and one upper bound for an explicit integral over the compact square
`[0,1]^2`. -/
theorem pairFunctional_of_overlapIntegral_and_explicitBetaMass
    (hoverlap : normalizedPairOverlapLower * pairArchScale ≤ pairOverlap)
    (hmass : (∫ t in Icc (0 : ℝ) 1, ∫ u in Icc (0 : ℝ) 1,
      ((6 / 5 : ℝ) * t ^ (1 / 5 : ℝ)) *
        ((6 / 5 : ℝ) * u ^ (1 / 5 : ℝ)) * (polynomial t u) ^ p) ≤
      normalizedPairMassUpper) :
    (1379635324335 : ℝ) / 10 ^ 12 ≤ JPair :=
  pairFunctional_of_explicitBetaMass_interval
    (normalizedPairOverlap_interval_iff.mpr hoverlap) hmass

end UnitDistance.Witness
