module

public import UnitDistance.Sqrt241.Analytic.WideNumerics
public import UnitDistance.Sqrt241.Analytic.Bridge

@[expose] public section
set_option backward.privateInPublic true


/-!
# From the wide-field hypothesis to the fixed-base ceiling (version 2)

`fixedBaseCeiling_lt_of_wide_types` is the version-2 analytic bridge for an abstract field
`E'` of degree 8192 (the wide field `E_W` of `papers/0.043171`) inside a Galois number field
`M` (the fixed base): the fixed-base ceiling of `M` at `ε = 1/4411` and `ℓ = Witness.logRD`
is below `X - 8469/1000000` as soon as

* the displayed zeta/log-derivative expression of `E'` (the H241 form with `E'`, `8192` and
  `σ_W = 1 + 1/4411`) is below `X`;
* `M` has the exact type `(8,4)` at 2 and residue degree at least 4 at the fifty census
  primes of `wideCensusOne ∪ wideCensusTwo`;
* `E'` has the local data `WideLocalTypes` (lower bounds of its normalized local
  contributions; `E'` need not be Galois over `ℚ`).

The proof subtracts the local drops of `M/E'` at 2 and the fifty census primes for
`log ζ(σ_W)`, and at 2 for the prime debit, and uses the certified enclosures of
`Analytic.WideNumerics`.  `fixedBaseCeiling_lt_425_of_wide_types` is the instance
`X = 50969/1000000`, with ceiling `425/10000`.
-/

noncomputable section
open NumberField IsDedekindDomain
open scoped BigOperators

namespace UnitDistance.Sqrt241.Analytic

open UnitDistance.NumberFieldAnalysis WideNumerics

section M

variable (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]

/-- The normalized contribution of a Galois field at `p` is at most `φ(p^k)/k` when its
residue degree at `p` is at least `k`. -/
theorem contrib_le_of_le_inertiaDeg {φ : ℕ → ℝ} (hφ : IsNormWeight φ) (p : Nat.Primes)
    (k : ℕ) (hk : 0 < k) (hf : k ≤ (rationalPrimeIdeal p.val).inertiaDegIn (𝓞 L)) :
    normalizedRationalPrimeContribution L φ p ≤ φ (p.val ^ k) / k := by
  rw [normalizedRationalPrimeContribution_eq L φ p]
  have he := ramificationIdxIn_pos L p
  set e := (rationalPrimeIdeal p.val).ramificationIdxIn (𝓞 L)
  set f := (rationalPrimeIdeal p.val).inertiaDegIn (𝓞 L)
  have hp1 := p.property.one_lt
  have hmono : φ (p.val ^ f) ≤ φ (p.val ^ k) :=
    hφ.anti _ _ (Nat.one_lt_pow hk.ne' hp1) (Nat.pow_le_pow_right (by omega) hf)
  have h0 : 0 ≤ φ (p.val ^ f) := hφ.nonneg _ (Nat.one_lt_pow (by omega) hp1)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hle : (k : ℝ) ≤ (e : ℝ) * f := by
    have : k ≤ e * f := le_trans hf (Nat.le_mul_of_pos_left f he)
    exact_mod_cast this
  calc φ (p.val ^ f) / ((e : ℝ) * f) ≤ φ (p.val ^ f) / k :=
        div_le_div_of_nonneg_left h0 hkpos hle
    _ ≤ φ (p.val ^ k) / k := div_le_div_of_nonneg_right hmono hkpos.le

end M

section Bridge

variable {E M : Type*} [Field E] [NumberField E] [Field M] [NumberField M] [IsGalois ℚ M]

/-- The facts used at one correction prime of each kind. -/
def KindFacts (k : WideKind) (p : Nat.Primes) : Prop :=
  (k = .dyadic → p.val = 2) ∧ (k = .one → p.val ∈ wideCensusOne) ∧
    (k = .two → p.val ∈ wideCensusTwo)

/-- The local drop at one correction prime. -/
theorem lowerDropW_le {φ : ℕ → ℝ} (hφ : IsNormWeight φ) (hE : WideLocalTypes E)
    (h2 : (rationalPrimeIdeal 2).ramificationIdxIn (𝓞 M) = 8 ∧
      (rationalPrimeIdeal 2).inertiaDegIn (𝓞 M) = 4)
    (hcensus : ∀ p ∈ wideCensusOne ∪ wideCensusTwo,
      4 ≤ (rationalPrimeIdeal p).inertiaDegIn (𝓞 M))
    (k : WideKind) (p : Nat.Primes) (hk : KindFacts k p) :
    lowerDropW k φ p.val ≤ normalizedRationalPrimeContribution E φ p -
      normalizedRationalPrimeContribution M φ p := by
  obtain ⟨hd, h1, htwo⟩ := hk
  cases k with
  | dyadic =>
    have hp2 := hd rfl
    have hp : p = ⟨2, Nat.prime_two⟩ := Subtype.ext hp2
    have hEc := hE.two φ hφ
    rw [← hp] at hEc
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hEc
    have hMc := normalizedRationalPrimeContribution_eq_of_indices M φ p 8 4 (by norm_num)
      (by norm_num) (by rw [hp2]; exact h2.1) (by rw [hp2]; exact h2.2)
    unfold lowerDropW kindLower kindUpper
    rw [hMc]
    push_cast at hEc ⊢
    linarith
  | one =>
    have hp := h1 rfl
    have hEc := hE.censusOne p hp φ hφ
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hEc
    have hMc := contrib_le_of_le_inertiaDeg M hφ p 4 (by norm_num)
      (hcensus _ (Finset.mem_union_left _ hp))
    unfold lowerDropW kindLower kindUpper
    push_cast at hEc hMc ⊢
    linarith
  | two =>
    have hp := htwo rfl
    have hEc := hE.censusTwo p hp φ hφ
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hEc
    have hMc := contrib_le_of_le_inertiaDeg M hφ p 4 (by norm_num)
      (hcensus _ (Finset.mem_union_right _ hp))
    unfold lowerDropW kindLower kindUpper
    push_cast at hEc hMc ⊢
    linarith

/-- The prime 2. -/
def twoPrime : Nat.Primes := ⟨2, Nat.prime_two⟩

/-- The correction primes as a finite set. -/
def wideCorrectionPrimes : Finset Nat.Primes :=
  Finset.univ.map ⟨widePrimes, widePrimes_injective⟩

theorem sum_wideCorrectionPrimes (g : Nat.Primes → ℝ) :
    ∑ p ∈ wideCorrectionPrimes, g p = ∑ i, g (widePrimes i) := by
  rw [wideCorrectionPrimes, Finset.sum_map]
  rfl

/-- The local drops at the correction primes are at least the certified values. -/
theorem wideLower_sum_le (hE : WideLocalTypes E)
    (h2 : (rationalPrimeIdeal 2).ramificationIdxIn (𝓞 M) = 8 ∧
      (rationalPrimeIdeal 2).inertiaDegIn (𝓞 M) = 4)
    (hcensus : ∀ p ∈ wideCensusOne ∪ wideCensusTwo,
      4 ≤ (rationalPrimeIdeal p).inertiaDegIn (𝓞 M)) :
    ∑ i, (wideLower i : ℝ) ≤ ∑ p ∈ wideCorrectionPrimes,
      (normalizedRationalPrimeContribution E eulerWeightW p -
        normalizedRationalPrimeContribution M eulerWeightW p) := by
  rw [sum_wideCorrectionPrimes]
  apply Finset.sum_le_sum
  intro i _
  exact (wideLower_le i).trans (lowerDropW_le eulerWeightW_isNormWeight hE h2 hcensus
    (wideKinds i) (widePrimes i) (wideKinds_spec i))

/-- **Analytic bridge, version 2.** -/
theorem fixedBaseCeiling_lt_of_wide_types [Algebra E M]
    (hdeg : Module.finrank ℚ E = 8192) (hE : WideLocalTypes E)
    (h2 : (rationalPrimeIdeal 2).ramificationIdxIn (𝓞 M) = 8 ∧
      (rationalPrimeIdeal 2).inertiaDegIn (𝓞 M) = 4)
    (hcensus : ∀ p ∈ wideCensusOne ∪ wideCensusTwo,
      4 ≤ (rationalPrimeIdeal p).inertiaDegIn (𝓞 M))
    (X : ℝ)
    (H : Real.log (dedekindZeta E ((1 + (1 / 4411 : ℝ) : ℝ) : ℂ)).re / 8192 +
        (1 / 4411 : ℝ) * ((Witness.logRD - Real.eulerMascheroniConstant -
          Real.log (4 * Real.pi)) / 4 - (logDeriv (dedekindZeta E) 2).re / 8192) < X) :
    fixedBaseResidueCeiling M Witness.logRD (1 / 4411) < X - 8469 / 1000000 := by
  have hs : (1 : ℝ) < sigmaW := by norm_num [sigmaW]
  -- Euler logarithms at σ_W
  have hz := normalized_weight_le_sub_contributions E M eulerWeightW_isNormWeight
    (dedekindZeta_log_hasSum E hs) (dedekindZeta_log_hasSum M hs) wideCorrectionPrimes
  have hzsum := wideLower_sum_le hE h2 hcensus (E := E) (M := M)
  -- prime debit at 2
  have hd := normalized_weight_le_sub_contributions E M debitWeight_isNormWeight
    (summable_primeDebit E).hasSum (summable_primeDebit M).hasSum {twoPrime}
  have hdrop := lowerDropW_le debitWeight_isNormWeight hE h2 hcensus .dyadic
    twoPrime (by unfold KindFacts twoPrime; decide) (E := E) (M := M)
  simp only [Finset.sum_singleton] at hd
  replace hdrop : primeDebitWeight (((2 ^ 2 : ℕ) : ℝ)) / 32 + primeDebitWeight (((2 ^ 4 : ℕ) : ℝ)) / 64 -
      primeDebitWeight (((2 ^ 4 : ℕ) : ℝ)) / 32 ≤
      normalizedRationalPrimeContribution E debitWeight twoPrime -
        normalizedRationalPrimeContribution M debitWeight twoPrime := hdrop
  have hnum := wide_corrections_ge
  have hdE := normalizedPrimeDebit_eq_neg_logDeriv E
  have hdegR : (Module.finrank ℚ E : ℝ) = 8192 := by exact_mod_cast hdeg
  unfold normalizedPrimeDebit at hdE
  rw [hdegR] at hz hd hdE
  rw [← sigmaW_eq] at H
  unfold fixedBaseResidueCeiling
  rw [← sigmaW_eq]
  unfold normalizedPrimeDebit
  linarith [hz, hzsum, hd, hdrop, hnum, hdE, H]

/-- The instance `X = 50969/1000000` of the version-2 bridge: ceiling `425/10000`. -/
theorem fixedBaseCeiling_lt_425_of_wide_types [Algebra E M]
    (hdeg : Module.finrank ℚ E = 8192) (hE : WideLocalTypes E)
    (h2 : (rationalPrimeIdeal 2).ramificationIdxIn (𝓞 M) = 8 ∧
      (rationalPrimeIdeal 2).inertiaDegIn (𝓞 M) = 4)
    (hcensus : ∀ p ∈ wideCensusOne ∪ wideCensusTwo,
      4 ≤ (rationalPrimeIdeal p).inertiaDegIn (𝓞 M))
    (H : Real.log (dedekindZeta E ((1 + (1 / 4411 : ℝ) : ℝ) : ℂ)).re / 8192 +
        (1 / 4411 : ℝ) * ((Witness.logRD - Real.eulerMascheroniConstant -
          Real.log (4 * Real.pi)) / 4 - (logDeriv (dedekindZeta E) 2).re / 8192) <
        50969 / 1000000) :
    fixedBaseResidueCeiling M Witness.logRD (1 / 4411) < 425 / 10000 := by
  have h := fixedBaseCeiling_lt_of_wide_types hdeg hE h2 hcensus _ H
  norm_num at h ⊢
  linarith

end Bridge

end UnitDistance.Sqrt241.Analytic
