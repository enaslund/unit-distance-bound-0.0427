module

public import UnitDistance.Sqrt241.Analytic.Fibers
public import UnitDistance.Sqrt241.Analytic.Numerics
public import UnitDistance.PrimeDebitLogDerivative
public import UnitDistance.Sqrt241.Witness

@[expose] public section
set_option backward.privateInPublic true


/-!
# From the genus-field hypothesis to the tower ceiling

`fixedBaseCeiling_lt_of_local_types` is the analytic bridge for
an abstract pair of Galois number fields `E ⊆ M` (with `[E:ℚ] = 512`):
the fixed-base ceiling of `M` at `ε = 1/300` and `ℓ = Witness.logRD` is below
`495/10000` (version 1's ceiling; version 2's `Witness.ceiling` is `425/10000`) as soon as

* the displayed zeta/log-derivative expression of `E` is below `852/10000`;
* `M` has the exact local types `(8,4)` at 2, `(1,4)` at 29, `(1,8)` at 7
  and residue degree at least 4 at the nine census primes;
* `E` has at most the types used in the design: at 2, `f ∣ 2` and `e f ≤ 8`;
  at 29 and at the census primes, `e = 1` and `f ∣ 2`; at 7, `e = 1` and
  `f ∣ 4`.

The proof subtracts the exact local Euler defects of `M/E` at these twelve
rational primes (`Analytic.Fibers`), both for `log ζ(1+ε)` and for the prime
debit at 2, and uses the certified enclosures of `Analytic.Numerics`.
-/

noncomputable section
open NumberField IsDedekindDomain
open scoped BigOperators

namespace UnitDistance.Sqrt241.Analytic

open UnitDistance.NumberFieldAnalysis

/-- The Euler-logarithm weight at `σ = 1 + 1/300`. -/
def eulerWeight : ℕ → ℝ := fun q => primeEulerLog q sigma

/-- The prime-debit weight `log q/(q²-1)`. -/
def debitWeight : ℕ → ℝ := fun q => primeDebitWeight (q : ℝ)

theorem eulerWeight_isNormWeight : IsNormWeight eulerWeight where
  nonneg q hq := primeEulerLog_nonneg hq (by norm_num [sigma])
  anti q Q hq hqQ := primeEulerLog_antitone hq hqQ (by norm_num [sigma])

theorem debitWeight_isNormWeight : IsNormWeight debitWeight where
  nonneg q hq := primeDebitWeight_nonneg (by exact_mod_cast hq)
  anti q Q hq hqQ := by
    have hq' : (1 : ℝ) < q := by exact_mod_cast hq
    have hQ' : (1 : ℝ) < Q := by exact_mod_cast (lt_of_lt_of_le hq hqQ)
    exact primeDebitWeight_antitoneOn hq' hQ' (by exact_mod_cast hqQ)

theorem eulerWeight_sq_le {q : ℕ} (hq : 1 < q) : eulerWeight (q ^ 2) ≤ 2 * eulerWeight q := by
  unfold eulerWeight primeEulerLog
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  set x := (q : ℝ) ^ (-sigma) with hx
  have hx0 : 0 ≤ x := Real.rpow_nonneg hq0 _
  have hx1 : x < 1 := prime_rpow_lt_one hq (by norm_num [sigma])
  have hsq : ((q ^ 2 : ℕ) : ℝ) ^ (-sigma) = x ^ 2 := by
    rw [hx, Nat.cast_pow, ← Real.rpow_natCast ((q : ℝ) ^ (-sigma)) 2,
      ← Real.rpow_mul hq0, ← Real.rpow_natCast (q : ℝ) 2, ← Real.rpow_mul hq0]
    ring_nf
  rw [hsq]
  have h1 : 0 < 1 - x := by linarith
  have h2 : 1 - x ^ 2 = (1 - x) * (1 + x) := by ring
  rw [h2, Real.log_mul h1.ne' (by linarith)]
  have h3 : Real.log (1 - x) ≤ Real.log (1 + x) := Real.log_le_log h1 (by linarith)
  linarith

theorem debitWeight_sq_le {q : ℕ} (hq : 1 < q) : debitWeight (q ^ 2) ≤ 2 * debitWeight q := by
  unfold debitWeight primeDebitWeight
  have hq' : (1 : ℝ) < q := by exact_mod_cast hq
  push_cast
  rw [Real.log_pow]
  have hlog : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq'.le
  have hd1 : 0 < (q : ℝ) ^ 2 - 1 := by nlinarith
  have hd2 : (q : ℝ) ^ 2 - 1 ≤ ((q : ℝ) ^ 2) ^ 2 - 1 := by nlinarith
  have hd2' : 0 < ((q : ℝ) ^ 2) ^ 2 - 1 := by nlinarith
  rw [show ((2 : ℕ) : ℝ) * Real.log q / (((q : ℝ) ^ 2) ^ 2 - 1) =
    2 * (Real.log q / (((q : ℝ) ^ 2) ^ 2 - 1)) by push_cast; ring]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact div_le_div_of_nonneg_left hlog hd1 hd2

section Types

variable {φ : ℕ → ℝ} (hφ : IsNormWeight φ) (hsq : ∀ q : ℕ, 1 < q → φ (q ^ 2) ≤ 2 * φ q)
include hφ hsq

omit hφ in
theorem contrib_ge_of_dvd_two {p e f : ℕ} (hp : 1 < p) (he : e = 1) (hf : f ∣ 2) :
    φ (p ^ 2) / 2 ≤ φ (p ^ f) / ((e : ℝ) * f) := by
  subst he
  rcases (Nat.dvd_prime Nat.prime_two).1 hf with rfl | rfl
  · have := hsq p hp
    norm_num
    linarith
  · norm_num

omit hφ in
theorem contrib_ge_of_dvd_four {p e f : ℕ} (hp : 1 < p) (he : e = 1) (hf : f ∣ 4) :
    φ (p ^ 4) / 4 ≤ φ (p ^ f) / ((e : ℝ) * f) := by
  subst he
  have hf4 : f ≤ 4 := Nat.le_of_dvd (by norm_num) hf
  have h1 := hsq p hp
  have h2 := hsq (p ^ 2) (Nat.one_lt_pow (by norm_num) hp)
  rw [← pow_mul] at h2
  interval_cases f
  · norm_num at hf
  · norm_num
    linarith
  · norm_num
    linarith
  · norm_num at hf
  · norm_num

omit hsq in
theorem contrib_ge_dyadic {e f : ℕ} (he : 0 < e) (hf : f ∣ 2) (hef : e * f ≤ 8) :
    φ (2 ^ 2) / 8 ≤ φ (2 ^ f) / ((e : ℝ) * f) := by
  have hfpos : 0 < f := Nat.pos_of_dvd_of_pos hf (by norm_num)
  have hf2 : f ≤ 2 := Nat.le_of_dvd (by norm_num) hf
  have hmono : φ (2 ^ 2) ≤ φ (2 ^ f) :=
    hφ.anti _ _ (Nat.one_lt_pow hfpos.ne' (by norm_num)) (Nat.pow_le_pow_right (by norm_num) hf2)
  have h0 : 0 ≤ φ (2 ^ 2) := hφ.nonneg _ (by norm_num)
  have hpos : (0 : ℝ) < (e : ℝ) * f := by positivity
  have hle : (e : ℝ) * f ≤ 8 := by exact_mod_cast hef
  calc φ (2 ^ 2) / 8 ≤ φ (2 ^ 2) / ((e : ℝ) * f) :=
        div_le_div_of_nonneg_left h0 hpos hle
    _ ≤ φ (2 ^ f) / ((e : ℝ) * f) := div_le_div_of_nonneg_right hmono hpos.le

omit hsq in
theorem contrib_le_of_four_le {p e f : ℕ} (hp : 1 < p) (he : 0 < e) (hf : 4 ≤ f) :
    φ (p ^ f) / ((e : ℝ) * f) ≤ φ (p ^ 4) / 4 := by
  have hmono : φ (p ^ f) ≤ φ (p ^ 4) :=
    hφ.anti _ _ (Nat.one_lt_pow (by norm_num) hp) (Nat.pow_le_pow_right (by omega) hf)
  have h0 : 0 ≤ φ (p ^ f) := hφ.nonneg _ (Nat.one_lt_pow (by omega) hp)
  have hle : (4 : ℝ) ≤ (e : ℝ) * f := by
    have : 4 ≤ e * f := le_trans hf (Nat.le_mul_of_pos_left f he)
    exact_mod_cast this
  calc φ (p ^ f) / ((e : ℝ) * f) ≤ φ (p ^ f) / 4 :=
        div_le_div_of_nonneg_left h0 (by norm_num) hle
    _ ≤ φ (p ^ 4) / 4 := div_le_div_of_nonneg_right hmono (by norm_num)

end Types

/-- The nine census primes (all split in `ℚ(√241)`). -/
def censusPrimes : Finset ℕ := {41, 47, 53, 59, 61, 67, 79, 83, 97}

/-- The twelve rational primes whose local defects are subtracted. -/
def correctionPrimeList : Fin 12 → Nat.Primes :=
  ![⟨2, by norm_num⟩, ⟨29, by norm_num⟩, ⟨7, by norm_num⟩, ⟨41, by norm_num⟩,
    ⟨47, by norm_num⟩, ⟨53, by norm_num⟩, ⟨59, by norm_num⟩, ⟨61, by norm_num⟩,
    ⟨67, by norm_num⟩, ⟨79, by norm_num⟩, ⟨83, by norm_num⟩, ⟨97, by norm_num⟩]

theorem correctionPrimeList_injective : Function.Injective correctionPrimeList := by
  decide

/-- The rational primes whose local defects are subtracted. -/
def correctionPrimes : Finset Nat.Primes :=
  Finset.univ.map ⟨correctionPrimeList, correctionPrimeList_injective⟩

/-- The design primes, used for the prime-debit correction. -/
def designPrimes : Finset Nat.Primes :=
  (Finset.univ : Finset (Fin 3)).map
    ⟨fun i => correctionPrimeList (Fin.castLE (by norm_num) i), by
      intro i j h
      exact Fin.castLE_injective _ (correctionPrimeList_injective h)⟩

theorem mem_correctionPrimes {p : Nat.Primes} (hp : p ∈ correctionPrimes) :
    p.val ∈ ({2, 29, 7} : Finset ℕ) ∪ censusPrimes := by
  obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hp
  revert i
  decide

theorem designPrimes_subset : designPrimes ⊆ correctionPrimes := by
  intro p hp
  obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hp
  exact Finset.mem_map.2 ⟨_, Finset.mem_univ _, rfl⟩

/-- Explicit lower bound of the local drop of `φ` at each correction prime. -/
def lowerDrop (φ : ℕ → ℝ) (p : Nat.Primes) : ℝ :=
  if p.val = 2 then φ (2 ^ 2) / 8 - φ (2 ^ 4) / 32
  else if p.val = 29 then φ (29 ^ 2) / 2 - φ (29 ^ 4) / 4
  else if p.val = 7 then φ (7 ^ 4) / 4 - φ (7 ^ 8) / 8
  else φ (p.val ^ 2) / 2 - φ (p.val ^ 4) / 4

section Bridge

variable (E M : Type*) [Field E] [NumberField E] [IsGalois ℚ E]
  [Field M] [NumberField M] [IsGalois ℚ M] [Algebra E M]

/-- Local-type hypotheses on the base field `E`. -/
structure GenusLocalTypes : Prop where
  two_dvd : (rationalPrimeIdeal 2).inertiaDegIn (𝓞 E) ∣ 2
  two_le : (rationalPrimeIdeal 2).ramificationIdxIn (𝓞 E) *
    (rationalPrimeIdeal 2).inertiaDegIn (𝓞 E) ≤ 8
  twentyNine_e : (rationalPrimeIdeal 29).ramificationIdxIn (𝓞 E) = 1
  twentyNine_f : (rationalPrimeIdeal 29).inertiaDegIn (𝓞 E) ∣ 2
  seven_e : (rationalPrimeIdeal 7).ramificationIdxIn (𝓞 E) = 1
  seven_f : (rationalPrimeIdeal 7).inertiaDegIn (𝓞 E) ∣ 4
  census_e : ∀ p ∈ censusPrimes, (rationalPrimeIdeal p).ramificationIdxIn (𝓞 E) = 1
  census_f : ∀ p ∈ censusPrimes, (rationalPrimeIdeal p).inertiaDegIn (𝓞 E) ∣ 2

variable {E M}

omit [Algebra E M] in
/-- Each correction prime drops the normalized contribution by at least
`lowerDrop`. -/
theorem lowerDrop_le {φ : ℕ → ℝ} (hφ : IsNormWeight φ)
    (hsq : ∀ q : ℕ, 1 < q → φ (q ^ 2) ≤ 2 * φ q) (hE : GenusLocalTypes E)
    (h2 : (rationalPrimeIdeal 2).ramificationIdxIn (𝓞 M) = 8 ∧
      (rationalPrimeIdeal 2).inertiaDegIn (𝓞 M) = 4)
    (h29 : (rationalPrimeIdeal 29).ramificationIdxIn (𝓞 M) = 1 ∧
      (rationalPrimeIdeal 29).inertiaDegIn (𝓞 M) = 4)
    (h7 : (rationalPrimeIdeal 7).ramificationIdxIn (𝓞 M) = 1 ∧
      (rationalPrimeIdeal 7).inertiaDegIn (𝓞 M) = 8)
    (hcensus : ∀ p ∈ censusPrimes, 4 ≤ (rationalPrimeIdeal p).inertiaDegIn (𝓞 M))
    (p : Nat.Primes) (hp : p ∈ correctionPrimes) :
    lowerDrop φ p ≤ normalizedRationalPrimeContribution E φ p -
      normalizedRationalPrimeContribution M φ p := by
  rw [normalizedRationalPrimeContribution_eq E φ p, normalizedRationalPrimeContribution_eq M φ p]
  have hp1 : 1 < p.val := p.property.one_lt
  have heE := ramificationIdxIn_pos E p
  have heM := ramificationIdxIn_pos M p
  have hmem := mem_correctionPrimes hp
  unfold lowerDrop
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with (h | h | h) | hc
  · obtain rfl : p = ⟨2, Nat.prime_two⟩ := Subtype.ext h
    simp only [ite_true, h2.1, h2.2]
    have := contrib_ge_dyadic hφ heE hE.two_dvd hE.two_le
    norm_num at this ⊢
    linarith
  · obtain rfl : p = ⟨29, by norm_num⟩ := Subtype.ext h
    simp only [show (29 : ℕ) ≠ 2 by norm_num, ite_false, ite_true, h29.1, h29.2]
    have := contrib_ge_of_dvd_two hsq (p := 29) (by norm_num) hE.twentyNine_e hE.twentyNine_f
    norm_num at this ⊢
    linarith
  · obtain rfl : p = ⟨7, by norm_num⟩ := Subtype.ext h
    simp only [show (7 : ℕ) ≠ 2 by norm_num, show (7 : ℕ) ≠ 29 by norm_num, ite_false,
      ite_true, h7.1, h7.2]
    have := contrib_ge_of_dvd_four hsq (p := 7) (by norm_num) hE.seven_e hE.seven_f
    norm_num at this ⊢
    linarith
  · have hne2 : p.val ≠ 2 := by
      intro h; rw [h] at hc; revert hc; decide
    have hne29 : p.val ≠ 29 := by
      intro h; rw [h] at hc; revert hc; decide
    have hne7 : p.val ≠ 7 := by
      intro h; rw [h] at hc; revert hc; decide
    simp only [hne2, hne29, hne7, ite_false]
    have hEc := contrib_ge_of_dvd_two hsq hp1 (hE.census_e _ hc) (hE.census_f _ hc)
    have hMc := contrib_le_of_four_le hφ hp1 heM (hcensus _ hc)
    linarith

theorem sum_lowerDrop_correctionPrimes (φ : ℕ → ℝ) :
    ∑ p ∈ correctionPrimes, lowerDrop φ p =
      (φ (2 ^ 2) / 8 - φ (2 ^ 4) / 32) + (φ (29 ^ 2) / 2 - φ (29 ^ 4) / 4) +
      (φ (7 ^ 4) / 4 - φ (7 ^ 8) / 8) + (φ (41 ^ 2) / 2 - φ (41 ^ 4) / 4) +
      (φ (47 ^ 2) / 2 - φ (47 ^ 4) / 4) + (φ (53 ^ 2) / 2 - φ (53 ^ 4) / 4) +
      (φ (59 ^ 2) / 2 - φ (59 ^ 4) / 4) + (φ (61 ^ 2) / 2 - φ (61 ^ 4) / 4) +
      (φ (67 ^ 2) / 2 - φ (67 ^ 4) / 4) + (φ (79 ^ 2) / 2 - φ (79 ^ 4) / 4) +
      (φ (83 ^ 2) / 2 - φ (83 ^ 4) / 4) + (φ (97 ^ 2) / 2 - φ (97 ^ 4) / 4) := by
  rw [correctionPrimes, Finset.sum_map]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Function.Embedding.coeFn_mk]
  simp [correctionPrimeList, lowerDrop]
  ring

theorem sum_lowerDrop_designPrimes (φ : ℕ → ℝ) :
    ∑ p ∈ designPrimes, lowerDrop φ p =
      (φ (2 ^ 2) / 8 - φ (2 ^ 4) / 32) + (φ (29 ^ 2) / 2 - φ (29 ^ 4) / 4) +
      (φ (7 ^ 4) / 4 - φ (7 ^ 8) / 8) := by
  rw [designPrimes, Finset.sum_map]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Function.Embedding.coeFn_mk]
  simp [correctionPrimeList, lowerDrop]
  ring

/-- The analytic bridge for an abstract genus field `E` with the design's
local types. -/
theorem fixedBaseCeiling_lt_of_local_types
    (hdeg : Module.finrank ℚ E = 512) (hE : GenusLocalTypes E)
    (h2 : (rationalPrimeIdeal 2).ramificationIdxIn (𝓞 M) = 8 ∧
      (rationalPrimeIdeal 2).inertiaDegIn (𝓞 M) = 4)
    (h29 : (rationalPrimeIdeal 29).ramificationIdxIn (𝓞 M) = 1 ∧
      (rationalPrimeIdeal 29).inertiaDegIn (𝓞 M) = 4)
    (h7 : (rationalPrimeIdeal 7).ramificationIdxIn (𝓞 M) = 1 ∧
      (rationalPrimeIdeal 7).inertiaDegIn (𝓞 M) = 8)
    (hcensus : ∀ p ∈ censusPrimes, 4 ≤ (rationalPrimeIdeal p).inertiaDegIn (𝓞 M))
    (H : Real.log (dedekindZeta E ((1 + (1 / 300 : ℝ) : ℝ) : ℂ)).re / 512 +
        (1 / 300 : ℝ) * ((Witness.logRD - Real.eulerMascheroniConstant -
          Real.log (4 * Real.pi)) / 4 - (logDeriv (dedekindZeta E) 2).re / 512) <
        852 / 10000) :
    fixedBaseResidueCeiling M Witness.logRD (1 / 300) < 495 / 10000 := by
  have hs : (1 : ℝ) < sigma := by norm_num [sigma]
  -- Euler logarithms
  have hz := normalized_weight_le_sub_contributions E M eulerWeight_isNormWeight
    (dedekindZeta_log_hasSum E hs) (dedekindZeta_log_hasSum M hs) correctionPrimes
  have hzsum : ∑ p ∈ correctionPrimes, lowerDrop eulerWeight p ≤
      ∑ p ∈ correctionPrimes, (normalizedRationalPrimeContribution E eulerWeight p -
        normalizedRationalPrimeContribution M eulerWeight p) :=
    Finset.sum_le_sum fun p hp => lowerDrop_le eulerWeight_isNormWeight
      (fun q hq => eulerWeight_sq_le hq) hE h2 h29 h7 hcensus p hp
  rw [sum_lowerDrop_correctionPrimes] at hzsum
  -- prime debit
  have hd := normalized_weight_le_sub_contributions E M debitWeight_isNormWeight
    (summable_primeDebit E).hasSum (summable_primeDebit M).hasSum designPrimes
  have hdsum : ∑ p ∈ designPrimes, lowerDrop debitWeight p ≤
      ∑ p ∈ designPrimes, (normalizedRationalPrimeContribution E debitWeight p -
        normalizedRationalPrimeContribution M debitWeight p) :=
    Finset.sum_le_sum fun p hp => lowerDrop_le debitWeight_isNormWeight
      (fun q hq => debitWeight_sq_le hq) hE h2 h29 h7 hcensus p (designPrimes_subset hp)
  rw [sum_lowerDrop_designPrimes] at hdsum
  have hnum := Numerics.corrections_ge
  have hdE := normalizedPrimeDebit_eq_neg_logDeriv E
  have hdegR : (Module.finrank ℚ E : ℝ) = 512 := by exact_mod_cast hdeg
  unfold normalizedPrimeDebit at hdE
  rw [hdegR] at hz hd hdE
  rw [← sigma_eq] at H
  unfold fixedBaseResidueCeiling
  rw [← sigma_eq]
  unfold normalizedPrimeDebit
  simp only [eulerWeight, debitWeight] at hz hzsum hd hdsum
  linarith [hz, hzsum, hd, hdsum, hnum, hdE, H]

end Bridge

end UnitDistance.Sqrt241.Analytic
