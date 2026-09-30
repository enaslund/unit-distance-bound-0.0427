module

public import UnitDistance.Upstream.AINTLIB.CompletedZeta.AnalyticControl
public import UnitDistance.Upstream.Hadamard.ComplexAnalysis.RealPartGrowth

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual global growth of completed Dedekind zeta

The Gamma recurrence, monotonicity above two and the elementary factorial
bound give a uniform right-half-plane estimate. The actual functional
equation and fixed-strip estimate from the attributed AINTLIB completion
then give `log ‖ξ_K(s)‖ ≤ C (‖s‖ + 4) log (‖s‖ + 4)` globally.
No entire-function growth premise or relative-Hecke continuation is assumed.
-/


open Complex Set Filter Asymptotics
open scoped Topology
namespace UnitDistance.NumberFieldAnalysis

/-- An elementary global upper bound, using only Γ recurrence and factorial bounds. -/
theorem realGamma_le_exp_mul_log {x : ℝ} (hx : 1 ≤ x) :
    Real.Gamma x ≤ Real.exp ((x + 3) * Real.log (x + 3)) := by
  let n : ℕ := ⌈x + 2⌉₊
  have hx0 : 0 < x := by linarith
  have hn : x + 2 ≤ (n : ℝ) := Nat.le_ceil _
  have hn' : (n : ℝ) < x + 3 := by
    simpa [n, add_assoc, show (2 : ℝ) + 1 = 3 by norm_num] using Nat.ceil_lt_add_one (show 0 ≤ x + 2 by linarith)
  have hn0 : 0 < (n : ℝ) := by linarith
  have hshift : Real.Gamma x ≤ Real.Gamma (x + 2) := by
    rw [show x + 2 = (x + 1) + 1 by ring,
      Real.Gamma_add_one (by linarith : x + 1 ≠ 0), Real.Gamma_add_one hx0.ne']
    have hΓ := (Real.Gamma_pos_of_pos hx0).le
    nlinarith [mul_nonneg hΓ (show 0 ≤ x - 1 by linarith)]
  calc
    Real.Gamma x ≤ Real.Gamma (x + 2) := hshift
    _ ≤ Real.Gamma ((n : ℝ) + 1) :=
      Real.Gamma_strictMonoOn_Ici.monotoneOn (by simp only [mem_Ici]; linarith)
        (by simp only [mem_Ici]; linarith) (by linarith)
    _ = (n.factorial : ℝ) := Real.Gamma_nat_eq_factorial n
    _ ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
    _ = Real.exp ((n : ℝ) * Real.log n) := by
      rw [Real.exp_nat_mul, Real.exp_log hn0]
    _ ≤ Real.exp ((x + 3) * Real.log (x + 3)) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul hn'.le
        (Real.log_le_log hn0 hn'.le) (Real.log_nonneg (by linarith))
        (by linarith)



/-- A convenient increasing envelope for the Gamma bound. -/
noncomputable def gammaGrowthEnvelope (r : ℝ) : ℝ := (r + 3) * Real.log (r + 3)

theorem gammaGrowthEnvelope_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    gammaGrowthEnvelope x ≤ gammaGrowthEnvelope y := by
  unfold gammaGrowthEnvelope
  apply mul_le_mul (by linarith) (Real.log_le_log (by linarith) (by linarith))
    (Real.log_nonneg (by linarith)) (by linarith)

theorem norm_Gamma_le_exp_gammaGrowthEnvelope {s : ℂ} (hs : 1 ≤ s.re) :
    ‖Complex.Gamma s‖ ≤ Real.exp (gammaGrowthEnvelope ‖s‖) := by
  exact (DedekindResidue.norm_Gamma_le_Gamma_re (by linarith)).trans <|
    (realGamma_le_exp_mul_log hs).trans <| Real.exp_le_exp.mpr <|
      gammaGrowthEnvelope_mono (by linarith) (Complex.re_le_norm s)

theorem norm_GammaR_le_exp_gammaGrowthEnvelope {s : ℂ} (hs : 2 ≤ s.re) :
    ‖Complex.Gammaℝ s‖ ≤ Real.exp (gammaGrowthEnvelope ‖s‖) := by
  rw [Complex.Gammaℝ_def, norm_mul]
  have hre : (s / 2).re = s.re / 2 := by simp
  have hpow : ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.two_le_pi] : (1 : ℝ) ≤ Real.pi) (by simp; linarith)
  calc
    ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖ ≤
        Real.exp (gammaGrowthEnvelope ‖s / 2‖) := by
      simpa only [one_mul] using mul_le_mul hpow
        (norm_Gamma_le_exp_gammaGrowthEnvelope (by rw [hre]; linarith))
        (norm_nonneg _) zero_le_one
    _ ≤ Real.exp (gammaGrowthEnvelope ‖s‖) := by
      apply Real.exp_le_exp.mpr
      apply gammaGrowthEnvelope_mono (norm_nonneg _)
      rw [norm_div, Complex.norm_ofNat]
      linarith [norm_nonneg s]

theorem norm_GammaC_le_exp_gammaGrowthEnvelope {s : ℂ} (hs : 2 ≤ s.re) :
    ‖Complex.Gammaℂ s‖ ≤ 2 * Real.exp (gammaGrowthEnvelope ‖s‖) := by
  rw [Complex.Gammaℂ_def, norm_mul, norm_mul, Complex.norm_ofNat]
  have hpow : ‖((2 : ℂ) * Real.pi) ^ (-s)‖ ≤ 1 := by
    rw [show ((2 : ℂ) * Real.pi) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [(by linarith [Real.two_le_pi] : (1 : ℝ) ≤ Real.pi)])
      (by simp; linarith)
  exact mul_le_mul (by linarith) (norm_Gamma_le_exp_gammaGrowthEnvelope (by linarith))
    (norm_nonneg _) (by norm_num)

theorem norm_gammaFactor_le_exp_gammaGrowthEnvelope (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 2 ≤ s.re) :
    ‖DedekindResidue.gammaFactor K s‖ ≤
      2 ^ NumberField.InfinitePlace.nrComplexPlaces K *
      Real.exp (((NumberField.InfinitePlace.nrRealPlaces K +
        NumberField.InfinitePlace.nrComplexPlaces K : ℕ) : ℝ) * gammaGrowthEnvelope ‖s‖) := by
  rw [DedekindResidue.gammaFactor, norm_mul, norm_pow, norm_pow]
  calc
    ‖Complex.Gammaℝ s‖ ^ NumberField.InfinitePlace.nrRealPlaces K *
        ‖Complex.Gammaℂ s‖ ^ NumberField.InfinitePlace.nrComplexPlaces K ≤
      (Real.exp (gammaGrowthEnvelope ‖s‖)) ^ NumberField.InfinitePlace.nrRealPlaces K *
        (2 * Real.exp (gammaGrowthEnvelope ‖s‖)) ^ NumberField.InfinitePlace.nrComplexPlaces K := by
      gcongr
      · exact norm_GammaR_le_exp_gammaGrowthEnvelope hs
      · exact norm_GammaC_le_exp_gammaGrowthEnvelope hs
    _ = _ := by
      rw [mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
      rw [← mul_assoc, mul_comm _ (2 ^ _), mul_assoc, ← Real.exp_add]
      congr 2
      push_cast
      ring



theorem le_gammaGrowthEnvelope {r : ℝ} (hr : 0 ≤ r) :
    r + 3 ≤ gammaGrowthEnvelope r := by
  have hlog : 1 ≤ Real.log (r + 3) := by
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 3) (show 3 ≤ r + 3 by linarith)
    linarith [Real.log_three_gt_d9]
  unfold gammaGrowthEnvelope
  nlinarith

theorem one_add_le_exp_gammaGrowthEnvelope {r : ℝ} (hr : 0 ≤ r) :
    1 + r ≤ Real.exp (gammaGrowthEnvelope r) := by
  have h := Real.add_one_le_exp r
  exact (by linarith : 1 + r ≤ Real.exp r).trans <|
    Real.exp_le_exp.mpr (by linarith [le_gammaGrowthEnvelope hr])

/-- Actual global right-half-plane estimate for the pole-cleared completion. -/
theorem exists_completedZeta_right_exp_bound (K : Type*) [Field K] [NumberField K] :
    ∃ A D : ℝ, 0 < A ∧ 0 ≤ D ∧ ∀ s : ℂ, 2 ≤ s.re →
      ‖DedekindResidue.completedDedekindZetaEntire K s‖ ≤
        A * Real.exp (D * gammaGrowthEnvelope ‖s‖) := by
  let T : ℝ := ∑' n : ℕ, ‖LSeries.term
    (fun n => (Nat.card {I : Ideal (NumberField.RingOfIntegers K) //
      Ideal.absNorm I = n} : ℂ)) 2 n‖
  let d : ℝ := |(NumberField.discr K : ℝ)|
  let N : ℕ := NumberField.InfinitePlace.nrRealPlaces K + NumberField.InfinitePlace.nrComplexPlaces K
  have hT : 0 ≤ T := tsum_nonneg (fun _ => norm_nonneg _)
  have hd : 0 < d := by
    apply abs_pos.mpr
    exact_mod_cast NumberField.discr_ne_zero K
  refine ⟨(T + 1) * 2 ^ NumberField.InfinitePlace.nrComplexPlaces K,
    |Real.log d| + N + 2, by positivity, by positivity, ?_⟩
  intro s hs
  have hs0 : s ≠ 0 := by intro h; subst s; norm_num at hs
  have hs1 : s ≠ 1 := by intro h; subst s; norm_num at hs
  have hΔ : ‖(d : ℂ) ^ (s / 2)‖ ≤
      Real.exp (|Real.log d| * gammaGrowthEnvelope ‖s‖) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hd, Real.rpow_def_of_pos hd]
    apply Real.exp_le_exp.mpr
    have hre : (s / 2).re = s.re / 2 := by simp
    rw [hre]
    calc
      Real.log d * (s.re / 2) ≤ |Real.log d| * ‖s‖ := by
        apply mul_le_mul (le_abs_self _) (by linarith [Complex.re_le_norm s])
          (by linarith) (abs_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by linarith [le_gammaGrowthEnvelope (norm_nonneg s)]) (abs_nonneg _)
  have hpoly : ‖s‖ * ‖s - 1‖ ≤ Real.exp (2 * gammaGrowthEnvelope ‖s‖) := by
    have hsn : ‖s - 1‖ ≤ 1 + ‖s‖ := by
      simpa only [norm_one, add_comm] using norm_sub_le s (1 : ℂ)
    have henv := one_add_le_exp_gammaGrowthEnvelope (norm_nonneg s)
    calc
      ‖s‖ * ‖s - 1‖ ≤ Real.exp (gammaGrowthEnvelope ‖s‖) *
          Real.exp (gammaGrowthEnvelope ‖s‖) :=
        mul_le_mul (by linarith) (hsn.trans henv) (norm_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hζ : ‖NumberField.dedekindZeta K s‖ ≤ T + 1 :=
    (DedekindResidue.norm_dedekindZeta_le_of_two_le_re K hs).trans (by dsimp [T]; linarith)
  rw [DedekindResidue.completedDedekindZetaEntire_eq K hs0 hs1,
    DedekindResidue.completedDedekindZeta_eq_of_one_lt_re K (by linarith),
    DedekindResidue.completedZetaPrefactor]
  rw [norm_mul, norm_mul, norm_mul, norm_mul]
  change ‖s‖ * ‖s - 1‖ * (‖(d : ℂ) ^ (s / 2)‖ * ‖DedekindResidue.gammaFactor K s‖ *
    ‖NumberField.dedekindZeta K s‖) ≤ _
  calc
    _ ≤ Real.exp (2 * gammaGrowthEnvelope ‖s‖) *
      (Real.exp (|Real.log d| * gammaGrowthEnvelope ‖s‖) *
        (2 ^ NumberField.InfinitePlace.nrComplexPlaces K *
          Real.exp ((N : ℝ) * gammaGrowthEnvelope ‖s‖)) * (T + 1)) := by
      gcongr
      exact norm_gammaFactor_le_exp_gammaGrowthEnvelope K hs
    _ = _ := by
      rw [show Real.exp (2 * gammaGrowthEnvelope ‖s‖) *
        (Real.exp (|Real.log d| * gammaGrowthEnvelope ‖s‖) *
          (2 ^ NumberField.InfinitePlace.nrComplexPlaces K *
            Real.exp ((N : ℝ) * gammaGrowthEnvelope ‖s‖)) * (T + 1)) =
        (T + 1) * 2 ^ NumberField.InfinitePlace.nrComplexPlaces K *
          (Real.exp (2 * gammaGrowthEnvelope ‖s‖) *
            Real.exp (|Real.log d| * gammaGrowthEnvelope ‖s‖) *
            Real.exp ((N : ℝ) * gammaGrowthEnvelope ‖s‖)) by ring]
      rw [← Real.exp_add, ← Real.exp_add]
      congr 2
      ring



private theorem log_norm_le_envelope {z : ℂ} {A D E : ℝ}
    (hA : 0 < A) (hD : 0 ≤ D) (hE : 1 ≤ E)
    (h : ‖z‖ ≤ A * Real.exp (D * E)) :
    Real.log ‖z‖ ≤ (|Real.log A| + D) * E := by
  by_cases hz : z = 0
  · subst z
    simp only [norm_zero, Real.log_zero]
    positivity
  have hlog := Real.log_le_log (norm_pos_iff.mpr hz) h
  rw [Real.log_mul hA.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  have hAbs : Real.log A ≤ |Real.log A| * E :=
    (le_abs_self _).trans (le_mul_of_one_le_right (abs_nonneg _) hE)
  nlinarith

/-- A global order-one envelope for the actual entire completed Dedekind zeta. -/
theorem exists_completedZeta_log_norm_bound (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ,
      Real.log ‖DedekindResidue.completedDedekindZetaEntire K s‖ ≤
        C * ((‖s‖ + 4) * Real.log (‖s‖ + 4)) := by
  obtain ⟨A, D, hA, hD, hright⟩ := exists_completedZeta_right_exp_bound K
  obtain ⟨B, hB, hstrip⟩ :=
    DedekindResidue.exists_completedDedekindZetaEntire_strip_bound K (-1) 2 (by norm_num)
  let C : ℝ := |Real.log A| + D + |Real.log (B + 1)| + 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hC₁ : |Real.log A| + D ≤ C := by dsimp [C]; linarith [abs_nonneg (Real.log (B+1))]
  have hC₂ : |Real.log (B+1)| + 2 ≤ C := by dsimp [C]; linarith [abs_nonneg (Real.log A)]
  refine ⟨C, hC, fun s => ?_⟩
  rw [show ‖s‖ + 4 = (‖s‖ + 1) + 3 by ring]
  change Real.log ‖DedekindResidue.completedDedekindZetaEntire K s‖ ≤
    C * gammaGrowthEnvelope (‖s‖ + 1)
  have henv : 1 ≤ gammaGrowthEnvelope ‖s‖ := by
    linarith [le_gammaGrowthEnvelope (norm_nonneg s), norm_nonneg s]
  have henv' : gammaGrowthEnvelope ‖s‖ ≤ gammaGrowthEnvelope (‖s‖ + 1) :=
    gammaGrowthEnvelope_mono (norm_nonneg s) (by linarith)
  by_cases hsR : 2 ≤ s.re
  · exact (log_norm_le_envelope hA hD henv (hright s hsR)).trans <|
      mul_le_mul hC₁ henv' (by positivity) hC
  by_cases hsL : s.re ≤ -1
  · have ht : 2 ≤ (1 - s).re := by simp; linarith
    have htE : 1 ≤ gammaGrowthEnvelope ‖(1 : ℂ) - s‖ := by
      linarith [le_gammaGrowthEnvelope (norm_nonneg ((1 : ℂ)-s)), norm_nonneg ((1 : ℂ)-s)]
    have h := log_norm_le_envelope hA hD htE (hright (1-s) ht)
    rw [DedekindResidue.completedDedekindZetaEntire_one_sub K s] at h
    refine h.trans (mul_le_mul hC₁ ?_ (by positivity) hC)
    apply gammaGrowthEnvelope_mono (norm_nonneg _)
    simpa only [norm_one, add_comm] using norm_sub_le (1 : ℂ) s
  have hbound : ‖DedekindResidue.completedDedekindZetaEntire K s‖ ≤
      (B + 1) * Real.exp (2 * gammaGrowthEnvelope ‖s‖) := by
    calc
      _ ≤ B * (1 + ‖s‖)^2 := hstrip s (by linarith) (by linarith)
      _ ≤ (B + 1) * (Real.exp (gammaGrowthEnvelope ‖s‖))^2 := by
        gcongr
        · linarith
        · exact one_add_le_exp_gammaGrowthEnvelope (norm_nonneg s)
      _ = _ := by rw [sq, ← Real.exp_add]; congr 2; ring
  exact (log_norm_le_envelope (by linarith) (by norm_num) henv hbound).trans <|
    mul_le_mul hC₂ henv' (by positivity) hC

/-- The elementary `r log r = o(r²)` estimate, with a fixed positive shift. -/
theorem exists_mul_shift_log_le_quadratic {C ε : ℝ} (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ r : ℝ, R ≤ r →
      C * ((r + 4) * Real.log (r + 4)) ≤ ε * r^2 := by
  let δ : ℝ := ε / (4 * (C + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.1 (Real.isLittleO_log_id_atTop.def hδ)
  refine ⟨max 4 R, by positivity, fun r hr => ?_⟩
  have hr4 : 4 ≤ r := (le_max_left _ _).trans hr
  have hrt : R ≤ r + 4 := by linarith [(le_max_right 4 R).trans hr]
  have hlog : Real.log (r+4) ≤ δ * (r+4) := by
    have h := hR (r+4) hrt
    simp only [Real.norm_eq_abs, id_eq, abs_of_nonneg (show 0 ≤ r+4 by linarith)] at h
    exact (le_abs_self _).trans h
  have hcoeff : 4 * C * δ ≤ ε := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (show 0 < 4 * (C+1) by positivity)).mpr
    nlinarith
  calc
    C * ((r+4) * Real.log (r+4)) ≤ C * (δ * (r+4)^2) := by
      have h := mul_le_mul_of_nonneg_left hlog (show 0 ≤ r+4 by linarith)
      have h' := mul_le_mul_of_nonneg_left h hC
      nlinarith
    _ ≤ C * (δ * (4 * r^2)) := by
      gcongr
      nlinarith
    _ = (4*C*δ) * r^2 := by ring
    _ ≤ ε * r^2 := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)

/-- No growth hypothesis is needed for the actual Dedekind completion. -/
theorem completedDedekindZetaEntire_subquadratic_log_norm_growth
    (K : Type*) [Field K] [NumberField K] :
    OverflowResidueRH.HasSubquadraticLogNormGrowthAtInfinity
      (DedekindResidue.completedDedekindZetaEntire K) := by
  obtain ⟨C, hC, hbound⟩ := exists_completedZeta_log_norm_bound K
  intro ε hε
  obtain ⟨R, hR, hquad⟩ := exists_mul_shift_log_le_quadratic hC hε
  exact ⟨R, hR, fun s hs => (hbound s).trans (hquad ‖s‖ hs)⟩

end UnitDistance.NumberFieldAnalysis
