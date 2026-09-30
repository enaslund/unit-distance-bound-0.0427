module

public import Mathlib.NumberTheory.RamificationInertia.Basic
public import UnitDistance.DedekindEulerLog

@[expose] public section
set_option backward.privateInPublic true


/-!
# Relative Euler comparison for actual number-field extensions

Prime norms, residue degrees and primes above a prime are the ordinary
ring-of-integers quantities. The comparison uses their proved norm and
cardinality formulas, with no prescribed splitting-success predicate.
-/

noncomputable section
open NumberField IsDedekindDomain
open scoped BigOperators

namespace UnitDistance.NumberFieldAnalysis

theorem primeEulerLog_antitone {q Q : ℕ} (hq : 1 < q) (hQ : q ≤ Q)
    {s : ℝ} (hs : 0 < s) : primeEulerLog Q s ≤ primeEulerLog q s := by
  apply neg_le_neg
  apply Real.log_le_log (sub_pos.mpr (prime_rpow_lt_one hq hs))
  have h := Real.rpow_le_rpow_of_nonpos (x := (q : ℝ)) (y := (Q : ℝ))
    (by exact_mod_cast (lt_trans Nat.zero_lt_one hq))
    (by exact_mod_cast hQ) (neg_nonpos.mpr hs.le)
  linarith

variable (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K]
  [Algebra F K]

/-- The actual prime-ideal fiber above a nonzero prime of the base. -/
abbrev PrimeFiber (p : HeightOneSpectrum (𝓞 F)) :=
  {P : HeightOneSpectrum (𝓞 K) // P.under (𝓞 F) = p}

omit [NumberField F] [NumberField K] in
theorem primeFiber_liesOver (p : HeightOneSpectrum (𝓞 F)) (P : PrimeFiber F K p) :
    P.1.asIdeal.LiesOver p.asIdeal := by
  constructor
  exact congrArg HeightOneSpectrum.asIdeal P.2 |>.symm

/-- The prime fiber is the actual finite set of prime ideals lying over `p`. -/
def primeFiberEquiv (p : HeightOneSpectrum (𝓞 F)) :
    PrimeFiber F K p ≃ ↥(IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 K)) where
  toFun P := ⟨P.1.asIdeal,
    (IsDedekindDomain.mem_primesOverFinset_iff p.ne_bot (𝓞 K)).mpr
      ⟨P.1.isPrime, primeFiber_liesOver F K p P⟩⟩
  invFun Q := by
    have hQ := (IsDedekindDomain.mem_primesOverFinset_iff p.ne_bot (𝓞 K)).mp Q.2
    letI := hQ.1
    letI := hQ.2
    exact ⟨⟨Q.1, hQ.1, Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot Q.1⟩,
      HeightOneSpectrum.ext hQ.2.over.symm⟩
  left_inv P := by apply Subtype.ext; rfl
  right_inv Q := rfl

instance (p : HeightOneSpectrum (𝓞 F)) : Fintype (PrimeFiber F K p) :=
  Fintype.ofEquiv _ (primeFiberEquiv F K p).symm

theorem primeFiber_card_le (p : HeightOneSpectrum (𝓞 F)) :
    Fintype.card (PrimeFiber F K p) ≤ Module.finrank F K := by
  letI : NoZeroSMulDivisors (𝓞 F) (𝓞 K) := ⟨fun {r x} h => by
    rw [Algebra.smul_def] at h
    rcases mul_eq_zero.mp h with hr | hx
    · exact Or.inl ((FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K))
        (hr.trans (map_zero _).symm))
    · exact Or.inr hx⟩
  rw [Fintype.card_congr (primeFiberEquiv F K p), Fintype.card_coe]
  exact Ideal.card_primesOverFinset_le_finrank (𝓞 K) F K p.ne_bot

theorem primeFiber_norm_le (p : HeightOneSpectrum (𝓞 F)) (P : PrimeFiber F K p) :
    Ideal.absNorm p.asIdeal ≤ Ideal.absNorm P.1.asIdeal := by
  letI := primeFiber_liesOver F K p P
  rw [Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P.1.asIdeal p.asIdeal p.isPrime p.ne_bot]
  exact Nat.le_self_pow (Ideal.inertiaDeg'_pos p.asIdeal P.1.asIdeal).ne' _

theorem primeFiber_log_sum_le (p : HeightOneSpectrum (𝓞 F))
    {s : ℝ} (hs : 0 < s) :
    (∑ P : PrimeFiber F K p, primeEulerLog (Ideal.absNorm P.1.asIdeal) s) ≤
      (Module.finrank F K : ℝ) * primeEulerLog (Ideal.absNorm p.asIdeal) s := by
  calc
    (∑ P : PrimeFiber F K p, primeEulerLog (Ideal.absNorm P.1.asIdeal) s) ≤
        ∑ _P : PrimeFiber F K p, primeEulerLog (Ideal.absNorm p.asIdeal) s := by
      apply Finset.sum_le_sum
      intro P _
      exact primeEulerLog_antitone (primeIdeal_absNorm_gt_one F p)
        (primeFiber_norm_le F K p P) hs
    _ = (Fintype.card (PrimeFiber F K p) : ℝ) *
        primeEulerLog (Ideal.absNorm p.asIdeal) s := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast primeFiber_card_le F K p)
      (primeEulerLog_nonneg (primeIdeal_absNorm_gt_one F p) hs)

/-- The ordinary zeta logarithm of an actual finite extension is bounded by
its relative degree times the base zeta logarithm, throughout the real
half-line of absolute convergence. No unramifiedness or Galois premise is needed. -/
theorem log_dedekindZeta_le_degree_mul {s : ℝ} (hs : 1 < s) :
    Real.log (dedekindZeta K s).re ≤
      (Module.finrank F K : ℝ) * Real.log (dedekindZeta F s).re := by
  have hK := (dedekindZeta_log_hasSum K hs).tsum_fiberwise
    (HeightOneSpectrum.under (𝓞 F))
  have hF := (dedekindZeta_log_hasSum F hs).mul_left (Module.finrank F K : ℝ)
  apply hasSum_le _ hK hF
  intro p
  change (∑' P : PrimeFiber F K p, primeEulerLog (Ideal.absNorm P.1.asIdeal) s) ≤ _
  rw [tsum_fintype]
  exact primeFiber_log_sum_le F K p (by linarith : 0 < s)

omit [Algebra F K] in
theorem log_relativeZeta_re_eq {s : ℝ} (hs : 1 < s) :
    Real.log (relativeZeta K F s).re =
      Real.log (dedekindZeta K s).re - Real.log (dedekindZeta F s).re := by
  rw [relativeZeta_eq_ofReal_div K F hs, Complex.ofReal_re,
    Real.log_div (dedekindZeta_re_pos K hs).ne' (dedekindZeta_re_pos F hs).ne']

/-- The exact relative Euler comparison in `an:relative-euler`, prior to
division by the positive base degree. -/
theorem log_relativeZeta_le_half_log_upper (hdegree : Module.finrank F K = 2)
    {s : ℝ} (hs : 1 < s) :
    Real.log (relativeZeta K F s).re ≤ Real.log (dedekindZeta K s).re / 2 := by
  rw [log_relativeZeta_re_eq F K hs]
  have h := log_dedekindZeta_le_degree_mul F K hs
  rw [hdegree] at h
  norm_num at h
  linarith

/-- The manuscript's normalization uses the base absolute degree, with the
factor two coming only from the relative degree. -/
theorem normalized_log_relativeZeta_le (hdegree : Module.finrank F K = 2)
    {s : ℝ} (hs : 1 < s) :
    Real.log (relativeZeta K F s).re / (Module.finrank ℚ F : ℝ) ≤
      Real.log (dedekindZeta K s).re / (2 * (Module.finrank ℚ F : ℝ)) := by
  simpa only [div_div] using div_le_div_of_nonneg_right
    (log_relativeZeta_le_half_log_upper F K hdegree hs)
    (Nat.cast_nonneg (Module.finrank ℚ F) : (0 : ℝ) ≤ Module.finrank ℚ F)

end UnitDistance.NumberFieldAnalysis
