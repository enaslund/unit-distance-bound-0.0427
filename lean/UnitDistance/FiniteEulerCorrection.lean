module

public import UnitDistance.RelativeEuler

@[expose] public section
set_option backward.privateInPublic true


/-!
# Finite strict corrections to the relative Euler comparison

`RelativeEuler` proves the degree-normalized monotonicity of Dedekind zeta in
an actual number-field extension.  This file retains the slack in that proof.
At each base prime the slack is a nonnegative, explicitly finite sum, and any
finite collection of certified local slacks may be subtracted from the base
zeta bound.

This is the interface needed by finite prime censuses: a census need only
certify lower bounds for the local defects on the primes it found.  No claim
about primes outside the finite certificate is required.
-/

noncomputable section
open NumberField IsDedekindDomain
open scoped BigOperators

namespace UnitDistance.NumberFieldAnalysis

variable (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K]
  [Algebra F K]

/-- The slack in the ordinary local Euler comparison above one prime of the
base field.  The inner sum is finite because a number-field prime has only
finitely many primes above it. -/
def primeFiberEulerDefect (p : HeightOneSpectrum (𝓞 F)) (s : ℝ) : ℝ :=
  (Module.finrank F K : ℝ) * primeEulerLog (Ideal.absNorm p.asIdeal) s -
    ∑ P : PrimeFiber F K p, primeEulerLog (Ideal.absNorm P.1.asIdeal) s

/-- Every local Euler defect is nonnegative. -/
theorem primeFiberEulerDefect_nonneg (p : HeightOneSpectrum (𝓞 F))
    {s : ℝ} (hs : 0 < s) : 0 ≤ primeFiberEulerDefect F K p s := by
  unfold primeFiberEulerDefect
  linarith [primeFiber_log_sum_le F K p hs]

/-- The global gap in the degree-times-base zeta comparison is exactly the
sum of the local prime-fiber defects. -/
theorem primeFiberEulerDefect_hasSum {s : ℝ} (hs : 1 < s) :
    HasSum (fun p : HeightOneSpectrum (𝓞 F) => primeFiberEulerDefect F K p s)
      ((Module.finrank F K : ℝ) * Real.log (dedekindZeta F s).re -
        Real.log (dedekindZeta K s).re) := by
  have hK := (dedekindZeta_log_hasSum K hs).tsum_fiberwise
    (HeightOneSpectrum.under (𝓞 F))
  change HasSum
    (fun p : HeightOneSpectrum (𝓞 F) =>
      ∑' P : PrimeFiber F K p, primeEulerLog (Ideal.absNorm P.1.asIdeal) s)
    (Real.log (dedekindZeta K s).re) at hK
  have hF := (dedekindZeta_log_hasSum F hs).mul_left (Module.finrank F K : ℝ)
  have hK' : HasSum
      (fun p : HeightOneSpectrum (𝓞 F) =>
        ∑ P : PrimeFiber F K p, primeEulerLog (Ideal.absNorm P.1.asIdeal) s)
      (Real.log (dedekindZeta K s).re) := by
    simpa only [tsum_fintype] using hK
  simpa only [primeFiberEulerDefect] using hF.sub hK'

/-- A finite list of base primes contributes at most the full global Euler
gap.  This is the sound boundary for a finite census. -/
theorem finite_primeFiberEulerDefect_le_gap {s : ℝ} (hs : 1 < s)
    (J : Finset (HeightOneSpectrum (𝓞 F))) :
    (∑ p ∈ J, primeFiberEulerDefect F K p s) ≤
      (Module.finrank F K : ℝ) * Real.log (dedekindZeta F s).re -
        Real.log (dedekindZeta K s).re := by
  have h := primeFiberEulerDefect_hasSum F K hs
  rw [← h.tsum_eq]
  exact h.summable.sum_le_tsum J fun p _ =>
    primeFiberEulerDefect_nonneg F K p (by linarith)

/-- Subtract any certified finite collection of local defects from the usual
degree-times-base upper bound. -/
theorem log_dedekindZeta_le_degree_mul_sub_finite_defects {s : ℝ} (hs : 1 < s)
    (J : Finset (HeightOneSpectrum (𝓞 F))) :
    Real.log (dedekindZeta K s).re ≤
      (Module.finrank F K : ℝ) * Real.log (dedekindZeta F s).re -
        ∑ p ∈ J, primeFiberEulerDefect F K p s := by
  linarith [finite_primeFiberEulerDefect_le_gap F K hs J]

/-- A certificate may provide simpler lower bounds for the local defects.
Only the finitely many inequalities indexed by `J` enter this theorem. -/
theorem log_dedekindZeta_le_degree_mul_sub_certificate {s : ℝ} (hs : 1 < s)
    (J : Finset (HeightOneSpectrum (𝓞 F))) (lower : HeightOneSpectrum (𝓞 F) → ℝ)
    (hlower : ∀ p ∈ J, lower p ≤ primeFiberEulerDefect F K p s) :
    Real.log (dedekindZeta K s).re ≤
      (Module.finrank F K : ℝ) * Real.log (dedekindZeta F s).re -
        ∑ p ∈ J, lower p := by
  have hsum : (∑ p ∈ J, lower p) ≤
      ∑ p ∈ J, primeFiberEulerDefect F K p s := by
    exact Finset.sum_le_sum fun p hp => hlower p hp
  linarith [log_dedekindZeta_le_degree_mul_sub_finite_defects F K hs J]

/-- Degree-normalized form of the finite-certificate comparison.  Its
subtracted correction is normalized by the absolute degree of the extension
field, exactly as in a fixed-field zeta certificate. -/
theorem normalized_log_dedekindZeta_le_sub_certificate {s : ℝ} (hs : 1 < s)
    (J : Finset (HeightOneSpectrum (𝓞 F))) (lower : HeightOneSpectrum (𝓞 F) → ℝ)
    (hlower : ∀ p ∈ J, lower p ≤ primeFiberEulerDefect F K p s) :
    Real.log (dedekindZeta K s).re / (Module.finrank ℚ K : ℝ) ≤
      Real.log (dedekindZeta F s).re / (Module.finrank ℚ F : ℝ) -
        (∑ p ∈ J, lower p) / (Module.finrank ℚ K : ℝ) := by
  have hraw := log_dedekindZeta_le_degree_mul_sub_certificate F K hs J lower hlower
  have hdF : (0 : ℝ) < Module.finrank ℚ F := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := F)
  have hdK : (0 : ℝ) < Module.finrank ℚ K := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hn : (0 : ℝ) < Module.finrank F K := by
    exact_mod_cast Module.finrank_pos (R := F) (M := K)
  have hdeg : (Module.finrank ℚ K : ℝ) =
      (Module.finrank ℚ F : ℝ) * (Module.finrank F K : ℝ) := by
    exact_mod_cast (Module.finrank_mul_finrank ℚ F K).symm
  calc
    Real.log (dedekindZeta K s).re / (Module.finrank ℚ K : ℝ) ≤
        ((Module.finrank F K : ℝ) * Real.log (dedekindZeta F s).re -
          ∑ p ∈ J, lower p) / (Module.finrank ℚ K : ℝ) :=
      div_le_div_of_nonneg_right hraw hdK.le
    _ = Real.log (dedekindZeta F s).re / (Module.finrank ℚ F : ℝ) -
        (∑ p ∈ J, lower p) / (Module.finrank ℚ K : ℝ) := by
      rw [hdeg]
      field_simp

/-- If every prime in a fiber has a certified norm and the fiber cardinality
is known, the local defect reduces to a closed scalar expression. -/
theorem primeFiberEulerDefect_eq_of_card_norm
    (p : HeightOneSpectrum (𝓞 F)) (s : ℝ) (q Q g : ℕ)
    (hbase : Ideal.absNorm p.asIdeal = q)
    (hcard : Fintype.card (PrimeFiber F K p) = g)
    (hnorm : ∀ P : PrimeFiber F K p, Ideal.absNorm P.1.asIdeal = Q) :
    primeFiberEulerDefect F K p s =
      (Module.finrank F K : ℝ) * primeEulerLog q s -
        (g : ℝ) * primeEulerLog Q s := by
  unfold primeFiberEulerDefect
  rw [hbase]
  have hfun : (fun P : PrimeFiber F K p =>
      primeEulerLog (Ideal.absNorm P.1.asIdeal) s) =
      fun _ : PrimeFiber F K p => primeEulerLog Q s := by
    funext P
    rw [hnorm P]
  rw [hfun, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]

end UnitDistance.NumberFieldAnalysis
