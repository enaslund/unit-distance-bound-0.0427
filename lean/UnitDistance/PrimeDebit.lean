module

public import UnitDistance.TsfasmanVladutPrimeRegroup
public import UnitDistance.Upstream.AINTLIB.ExplicitFormula.PrimeSide

@[expose] public section
set_option backward.privateInPublic true


/-!
# The actual convergent quadratic prime remainder

The remainder is summed over the ordinary nonzero prime ideals. Its
normalization decreases under actual number-field extension, by grouping
primes over their contractions. No splitting or unramifiedness hypothesis
is used.
-/

noncomputable section
open NumberField IsDedekindDomain Filter Topology
open scoped BigOperators
namespace UnitDistance.NumberFieldAnalysis

/-- The elementary quadratic remainder in the unconditional prime budget. -/
def primeDebitWeight (q : ℝ) : ℝ := Real.log q/(q^2-1)

theorem primeDebitWeight_nonneg {q : ℝ} (hq : 1 < q) :
    0 ≤ primeDebitWeight q := by
  exact div_nonneg (Real.log_nonneg hq.le) (by nlinarith)

theorem primeDebitWeight_antitoneOn : AntitoneOn primeDebitWeight (Set.Ioi 1) := by
  intro q hq Q hQ hqQ
  change 1 < q at hq
  change 1 < Q at hQ
  have hq0 : 0 < q := by linarith
  have hQ0 : 0 < Q := by linarith
  have hqd : 0 < q^2-1 := by nlinarith
  have hQd : 0 < Q^2-1 := by nlinarith
  have hupper := Real.log_le_sub_one_of_pos (div_pos hQ0 hq0)
  rw [Real.log_div hQ0.ne' hq0.ne'] at hupper
  have hu := mul_le_mul_of_nonneg_right hupper hq0.le
  have hu' : q*(Real.log Q-Real.log q) ≤ Q-q := by
    have hi : (Q/q-1)*q = Q-q := by field_simp
    rw [hi] at hu
    nlinarith
  have hl := mul_le_mul_of_nonneg_right (Real.one_sub_inv_le_log_of_pos hq0) hq0.le
  have hl' : q-1 ≤ q*Real.log q := by
    have hi : (1-q⁻¹)*q = q-1 := by field_simp
    rw [hi] at hl
    nlinarith
  have hu2 := mul_le_mul_of_nonneg_right hu' hqd.le
  have hl2 := mul_le_mul_of_nonneg_right hl' (show 0 ≤ Q^2-q^2 by nlinarith)
  have hn := mul_nonneg (mul_nonneg (sub_nonneg.mpr hqQ) (sub_nonneg.mpr hq.le))
    (sub_nonneg.mpr hQ.le)
  unfold primeDebitWeight
  apply (div_le_div_iff₀ hQd hqd).mpr
  apply (mul_le_mul_iff_right₀ hq0).mp
  nlinarith

theorem primeDebitWeight_le_log_rpow {q : ℝ} (hq : 2 ≤ q) :
    primeDebitWeight q ≤ 2*(Real.log q*q^(-(2:ℝ))) := by
  have hq0 : 0 < q := by linarith
  have hden : 0 < q^2-1 := by nlinarith
  rw [primeDebitWeight, Real.rpow_neg hq0.le, Real.rpow_two]
  apply (div_le_iff₀ hden).mpr
  have hlog := Real.log_nonneg (by linarith : 1 ≤ q)
  field_simp
  nlinarith [mul_nonneg hlog (show 0 ≤ q^2-2 by nlinarith)]

variable (K : Type*) [Field K] [NumberField K]

/-- The literal convergent remainder normalized by the actual field degree. -/
def normalizedPrimeDebit : ℝ :=
  (∑' P : HeightOneSpectrum (𝓞 K), primeDebitWeight (Ideal.absNorm P.asIdeal)) /
    (Module.finrank ℚ K : ℝ)

theorem summable_primeDebit :
    Summable (fun P : HeightOneSpectrum (𝓞 K) => primeDebitWeight (Ideal.absNorm P.asIdeal)) := by
  have hs := (DedekindResidue.summable_primeIdeal_log_rpow K (by norm_num : (1:ℝ)<2)).mul_left 2
  have ht : Summable (fun P : HeightOneSpectrum (𝓞 K) =>
      2*(Real.log (Ideal.absNorm P.asIdeal)*(Ideal.absNorm P.asIdeal : ℝ)^(-(2:ℝ)))) :=
    (tvPrimeIdealEquiv K).summable_iff.mp hs
  apply ht.of_nonneg_of_le
  · intro P
    exact primeDebitWeight_nonneg (by exact_mod_cast primeIdeal_absNorm_gt_one K P)
  · intro P
    exact primeDebitWeight_le_log_rpow (by exact_mod_cast primeIdeal_absNorm_gt_one K P)

theorem normalizedPrimeDebit_hasSum :
    HasSum (fun q : ℕ => normalizedPrimeNormCount K (q+2)*primeDebitWeight (q+2))
      (normalizedPrimeDebit K) := by
  have h := (tv_primeNormCount_hasSum_shift K
    (weight := fun q : ℕ => primeDebitWeight q) (summable_primeDebit K).hasSum).div_const
      (Module.finrank ℚ K : ℝ)
  simpa only [normalizedPrimeDebit, normalizedPrimeNormCount, Nat.cast_add,
    Nat.cast_ofNat, div_mul_eq_mul_div] using h

theorem finite_normalizedPrimeDebit_le (J : Finset ℕ) :
    (∑ q ∈ J, normalizedPrimeNormCount K (q+2)*primeDebitWeight (q+2)) ≤
      normalizedPrimeDebit K := by
  have h := normalizedPrimeDebit_hasSum K
  rw [← h.tsum_eq]
  apply h.summable.sum_le_tsum J
  intro q _
  exact mul_nonneg (normalizedPrimeNormCount_mem K (by omega : 1<q+2)).1
    (primeDebitWeight_nonneg (by have := Nat.cast_nonneg (α := ℝ) q; linarith : (1:ℝ)<q+2))

variable (F : Type*) [Field F] [NumberField F] [Algebra F K]

theorem primeFiber_debit_sum_le (p : HeightOneSpectrum (𝓞 F)) :
    (∑ P : PrimeFiber F K p, primeDebitWeight (Ideal.absNorm P.1.asIdeal)) ≤
      (Module.finrank F K : ℝ)*primeDebitWeight (Ideal.absNorm p.asIdeal) := by
  have hp : (1:ℝ) < Ideal.absNorm p.asIdeal := by
    exact_mod_cast primeIdeal_absNorm_gt_one F p
  calc
    _ ≤ ∑ _P : PrimeFiber F K p, primeDebitWeight (Ideal.absNorm p.asIdeal) := by
      apply Finset.sum_le_sum
      intro P _
      exact primeDebitWeight_antitoneOn hp
        (by change (1:ℝ) < Ideal.absNorm P.1.asIdeal; exact_mod_cast primeIdeal_absNorm_gt_one K P.1)
        (by exact_mod_cast primeFiber_norm_le F K p P)
    _ = (Fintype.card (PrimeFiber F K p) : ℝ)*primeDebitWeight (Ideal.absNorm p.asIdeal) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast primeFiber_card_le F K p)
      (primeDebitWeight_nonneg hp)

theorem normalizedPrimeDebit_le_base : normalizedPrimeDebit K ≤ normalizedPrimeDebit F := by
  have hK := (summable_primeDebit K).hasSum.tsum_fiberwise (HeightOneSpectrum.under (𝓞 F))
  have hF := (summable_primeDebit F).hasSum.mul_left (Module.finrank F K : ℝ)
  have h := hasSum_le (fun p => by
    change (∑' P : PrimeFiber F K p, primeDebitWeight (Ideal.absNorm P.1.asIdeal)) ≤ _
    rw [tsum_fintype]
    exact primeFiber_debit_sum_le K F p) hK hF
  have hdeg : (Module.finrank ℚ K : ℝ) =
      (Module.finrank ℚ F : ℝ)*(Module.finrank F K : ℝ) := by
    exact_mod_cast (Module.finrank_mul_finrank ℚ F K).symm
  have hdF : (0:ℝ) < Module.finrank ℚ F := by exact_mod_cast Module.finrank_pos (R:=ℚ) (M:=F)
  have hdR : (0:ℝ) < Module.finrank F K := by exact_mod_cast Module.finrank_pos (R:=F) (M:=K)
  unfold normalizedPrimeDebit
  rw [hdeg]
  apply (div_le_div_iff₀ (mul_pos hdF hdR) hdF).mpr
  nlinarith [mul_le_mul_of_nonneg_right h hdF.le]

/-- Absolute-degree normalized Euler logarithms decrease under actual finite
extension, with no prescribed splitting assumptions. -/
theorem normalized_log_dedekindZeta_le_base {s : ℝ} (hs : 1 < s) :
    Real.log (dedekindZeta K s).re/(Module.finrank ℚ K : ℝ) ≤
      Real.log (dedekindZeta F s).re/(Module.finrank ℚ F : ℝ) := by
  have h := log_dedekindZeta_le_degree_mul F K hs
  have hdeg : (Module.finrank ℚ K : ℝ) =
      (Module.finrank ℚ F : ℝ)*(Module.finrank F K : ℝ) := by
    exact_mod_cast (Module.finrank_mul_finrank ℚ F K).symm
  have hdF : (0:ℝ) < Module.finrank ℚ F := by exact_mod_cast Module.finrank_pos (R:=ℚ) (M:=F)
  have hdR : (0:ℝ) < Module.finrank F K := by exact_mod_cast Module.finrank_pos (R:=F) (M:=K)
  rw [hdeg]
  apply (div_le_div_iff₀ (mul_pos hdF hdR) hdF).mpr
  nlinarith [mul_le_mul_of_nonneg_right h hdF.le]

end UnitDistance.NumberFieldAnalysis
