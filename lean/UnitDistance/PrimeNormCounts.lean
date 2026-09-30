module

public import Mathlib.NumberTheory.RamificationInertia.Basic
public import UnitDistance.RelativeEuler
public import Mathlib.Data.Nat.Prime.Pow
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.Topology.Sequences

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual normalized prime-norm counts

The count is over nonzero prime ideals of the ordinary ring of integers.
Each norm fiber injects into the primes above the smallest rational prime
dividing that norm. This proves the uniform bound by the absolute degree,
needed for diagonal extraction and dominated convergence of Euler sums.
-/

noncomputable section
open NumberField IsDedekindDomain Filter Topology
open scoped BigOperators

namespace UnitDistance.NumberFieldAnalysis

variable (K : Type*) [Field K] [NumberField K]

/-- Actual prime ideals with specified absolute norm. -/
abbrev PrimeNormFiber (q : ℕ) :=
  {P : HeightOneSpectrum (𝓞 K) // Ideal.absNorm P.asIdeal = q}

instance finite_primeNormFiber (q : ℕ) : Finite (PrimeNormFiber K q) := by
  letI : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = q} :=
    (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) q).to_subtype
  exact Finite.of_injective
    (fun P : PrimeNormFiber K q => (⟨P.1.asIdeal, P.2⟩ :
      {I : Ideal (𝓞 K) // Ideal.absNorm I = q}))
    (fun P Q h => Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h)))

/-- The ordinary number of prime ideals of a specified norm. -/
def primeNormCount (q : ℕ) : ℕ := Nat.card (PrimeNormFiber K q)

theorem primeNormCount_eq_zero {q : ℕ} (hq : q ≤ 1) : primeNormCount K q = 0 := by
  haveI : IsEmpty (PrimeNormFiber K q) := ⟨fun P => by
    have h := primeIdeal_absNorm_gt_one K P.1
    rw [P.2] at h
    omega⟩
  simp [primeNormCount]

theorem primeNormFiber_minFac_mem {q : ℕ} (P : PrimeNormFiber K q) :
    (q.minFac : 𝓞 K) ∈ P.1.asIdeal := by
  letI := P.1.isPrime
  letI : P.1.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal P.1.isPrime P.1.ne_bot
  obtain ⟨p, n, hn, hpP, hp, hnorm⟩ := Ideal.exists_prime_and_absNorm_eq_pow P.1.asIdeal
  have he : q.minFac = p := by
    rw [← P.2, hnorm]
    exact hp.pow_minFac hn.ne'
  rwa [he]

theorem primeNormFiber_liesOver {q : ℕ} (hq : 1 < q) (P : PrimeNormFiber K q) :
    P.1.asIdeal.LiesOver (Ideal.span {(q.minFac : ℤ)}) := by
  letI : Fact q.minFac.Prime := ⟨Nat.minFac_prime hq.ne'⟩
  letI := P.1.isPrime
  constructor
  apply Ideal.IsMaximal.eq_of_le (inferInstance : (Ideal.span {(q.minFac : ℤ)}).IsMaximal)
    (Ideal.IsPrime.ne_top (inferInstance : (P.1.asIdeal.under ℤ).IsPrime))
  rw [Ideal.span_singleton_le_iff_mem]
  change algebraMap ℤ (𝓞 K) (q.minFac : ℤ) ∈ P.1.asIdeal
  simpa using primeNormFiber_minFac_mem K P

/-- There are at most `[K:Q]` prime ideals of any given norm, without Galois
or ramification assumptions. -/
theorem primeNormCount_le_degree {q : ℕ} (hq : 1 < q) :
    primeNormCount K q ≤ Module.finrank ℚ K := by
  let p : Ideal ℤ := Ideal.span {(q.minFac : ℤ)}
  letI : Fact q.minFac.Prime := ⟨Nat.minFac_prime hq.ne'⟩
  have hp : p ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Nat.minFac_prime hq.ne').ne_zero
  let f : PrimeNormFiber K q → ↥(IsDedekindDomain.primesOverFinset p (𝓞 K)) := fun P =>
    ⟨P.1.asIdeal, (IsDedekindDomain.mem_primesOverFinset_iff hp (𝓞 K)).mpr
      ⟨P.1.isPrime, primeNormFiber_liesOver K hq P⟩⟩
  have hf : Function.Injective f := fun P Q h =>
    Subtype.ext (HeightOneSpectrum.ext (congrArg Subtype.val h))
  calc
    primeNormCount K q ≤ Nat.card ↥(IsDedekindDomain.primesOverFinset p (𝓞 K)) :=
      Nat.card_le_card_of_injective f hf
    _ = (IsDedekindDomain.primesOverFinset p (𝓞 K)).card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ _ := Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K hp

/-- Prime count normalized by the actual absolute degree. -/
def normalizedPrimeNormCount (q : ℕ) : ℝ :=
  (primeNormCount K q : ℝ)/(Module.finrank ℚ K : ℝ)

theorem normalizedPrimeNormCount_mem {q : ℕ} (hq : 1 < q) :
    normalizedPrimeNormCount K q ∈ Set.Icc (0:ℝ) 1 := by
  have hd : (0:ℝ) < Module.finrank ℚ K := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hd.le
  · apply (div_le_iff₀ hd).mpr
    simpa only [one_mul] using (show (primeNormCount K q : ℝ) ≤ Module.finrank ℚ K by
      exact_mod_cast primeNormCount_le_degree K hq)

/-- Regrouping the genuine Euler logarithm by absolute prime-ideal norm. -/
theorem primeNormCount_euler_hasSum {s : ℝ} (hs : 1 < s) :
    HasSum (fun q : ℕ => (primeNormCount K q : ℝ)*primeEulerLog q s)
      (Real.log (dedekindZeta K s).re) := by
  have h := (dedekindZeta_log_hasSum K hs).tsum_fiberwise
    (fun P : HeightOneSpectrum (𝓞 K) => Ideal.absNorm P.asIdeal)
  change HasSum (fun q : ℕ => ∑' P : PrimeNormFiber K q,
    primeEulerLog (Ideal.absNorm P.1.asIdeal) s) (Real.log (dedekindZeta K s).re) at h
  have hfun : (fun q : ℕ => ∑' P : PrimeNormFiber K q,
      primeEulerLog (Ideal.absNorm P.1.asIdeal) s) =
      fun q : ℕ => (primeNormCount K q : ℝ)*primeEulerLog q s := by
    funext q
    have he : (fun P : PrimeNormFiber K q => primeEulerLog (Ideal.absNorm P.1.asIdeal) s) =
        fun _ : PrimeNormFiber K q => primeEulerLog q s := by
      funext P
      rw [P.2]
    rw [he, tsum_const]
    simp only [primeNormCount, nsmul_eq_mul]
  rwa [hfun] at h

/-- The normalized Euler series on the countable list of all possible norms. -/
theorem normalizedPrimeNormCount_euler_hasSum {s : ℝ} (hs : 1 < s) :
    HasSum (fun q : ℕ => normalizedPrimeNormCount K (q+2)*primeEulerLog (q+2) s)
      (Real.log (dedekindZeta K s).re/(Module.finrank ℚ K : ℝ)) := by
  have h := (primeNormCount_euler_hasSum K hs).div_const (Module.finrank ℚ K : ℝ)
  have hfun : (fun q : ℕ => (primeNormCount K q : ℝ)*primeEulerLog q s /
      (Module.finrank ℚ K : ℝ)) =
      fun q : ℕ => normalizedPrimeNormCount K q*primeEulerLog q s := by
    funext q
    unfold normalizedPrimeNormCount
    ring
  rw [hfun] at h
  have hshift := (hasSum_nat_add_iff' 2).mpr h
  simpa [Finset.sum_range_succ, normalizedPrimeNormCount,
    primeNormCount_eq_zero K (by norm_num : 0 ≤ 1),
    primeNormCount_eq_zero K (by norm_num : 1 ≤ 1)] using hshift

/-- A countable diagonal subsequence exists for every actual number-field
sequence. The coordinates index all integer norms `q+2`; the non-prime-power
coordinates simply vanish. -/
theorem exists_subsequence_normalizedPrimeNormCount
    (Ks : ℕ → Type*) [∀ n, Field (Ks n)] [∀ n, NumberField (Ks n)] :
    ∃ (beta : ℕ → ℝ) (phi : ℕ → ℕ), StrictMono phi ∧
      (∀ q, beta q ∈ Set.Icc (0:ℝ) 1) ∧
      ∀ q, Tendsto (fun n => normalizedPrimeNormCount (Ks (phi n)) (q+2))
        atTop (𝓝 (beta q)) := by
  let x : ℕ → (ℕ → Set.Icc (0:ℝ) 1) := fun n q =>
    ⟨normalizedPrimeNormCount (Ks n) (q+2), normalizedPrimeNormCount_mem (Ks n) (by omega)⟩
  obtain ⟨b, phi, hphi, hlim⟩ := SeqCompactSpace.tendsto_subseq x
  refine ⟨fun q => (b q : ℝ), phi, hphi, fun q => (b q).2, fun q => ?_⟩
  exact (continuous_subtype_val.tendsto (b q)).comp
    ((continuous_apply q).tendsto b |>.comp hlim)

end UnitDistance.NumberFieldAnalysis
