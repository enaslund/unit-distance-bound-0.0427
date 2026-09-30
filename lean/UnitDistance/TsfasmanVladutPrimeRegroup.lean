module

public import UnitDistance.TsfasmanVladutPrimeWeight
public import UnitDistance.PrimeNormCounts

@[expose] public section
set_option backward.privateInPublic true


/-!
# Exact regrouping of the literal prime-side series by absolute norm

The scalar kernel identity removes the contour parameter. Fubini sums the
prime powers, and the actual finite fibers of the absolute norm produce
`primeNormCount`. Summability is an explicit premise of these independent
regrouping lemmas; `TsfasmanVladutPrimeSideRegroup` discharges it for the
actual explicit-formula prime side.
-/

noncomputable section
open NumberField IsDedekindDomain Filter Topology
open scoped BigOperators
namespace UnitDistance.NumberFieldAnalysis

variable (K : Type*) [Field K] [NumberField K]

/-- Match the explicit formula's nonzero-prime-ideal subtype with the actual
height-one spectrum used by the normalized prime counts. -/
def tvPrimeIdealEquiv :
    {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} ≃ HeightOneSpectrum (𝓞 K) where
  toFun P := ⟨P.1, P.2.1, P.2.2⟩
  invFun P := ⟨P.asIdeal, P.isPrime, P.ne_bot⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Grouping a convergent actual prime-ideal series by its absolute norms. -/
theorem tv_primeNormCount_hasSum {weight : ℕ → ℝ} {S : ℝ}
    (h : HasSum (fun P : HeightOneSpectrum (𝓞 K) => weight (Ideal.absNorm P.asIdeal)) S) :
    HasSum (fun q : ℕ => (primeNormCount K q : ℝ)*weight q) S := by
  have hs := h.tsum_fiberwise (fun P : HeightOneSpectrum (𝓞 K) => Ideal.absNorm P.asIdeal)
  change HasSum (fun q : ℕ => ∑' P : PrimeNormFiber K q,
    weight (Ideal.absNorm P.1.asIdeal)) S at hs
  have he : (fun q : ℕ => ∑' P : PrimeNormFiber K q,
      weight (Ideal.absNorm P.1.asIdeal)) =
      fun q : ℕ => (primeNormCount K q : ℝ)*weight q := by
    funext q
    have hf : (fun P : PrimeNormFiber K q => weight (Ideal.absNorm P.1.asIdeal)) =
        fun _ : PrimeNormFiber K q => weight q := by
      funext P
      rw [P.2]
    rw [hf, tsum_const]
    simp only [primeNormCount, nsmul_eq_mul]
  rwa [he] at hs

/-- The list of all possible norms starts at two; impossible norm fibers
vanish by the actual prime-ideal norm theorem. -/
theorem tv_primeNormCount_hasSum_shift {weight : ℕ → ℝ} {S : ℝ}
    (h : HasSum (fun P : HeightOneSpectrum (𝓞 K) => weight (Ideal.absNorm P.asIdeal)) S) :
    HasSum (fun q : ℕ => (primeNormCount K (q+2) : ℝ)*weight (q+2)) S := by
  have hs := (hasSum_nat_add_iff' 2).mpr (tv_primeNormCount_hasSum K h)
  simpa [Finset.sum_range_succ, primeNormCount_eq_zero K (by norm_num : 0 ≤ 1),
    primeNormCount_eq_zero K (by norm_num : 1 ≤ 1)] using hs

end UnitDistance.NumberFieldAnalysis

namespace UnitDistance.NumberFieldAnalysis

theorem tvKernel_prime_side_term (e a : ℝ) {q : ℝ} (hq : 1 < q) (m : ℕ) :
    ((Real.log q*q^(-(((m+1:ℕ):ℝ)*(1+a))) : ℝ) : ℂ) *
      (tvKernel e (((m+1:ℕ):ℝ)*Real.log q) *
        (Real.exp ((1/2+a)*(((m+1:ℕ):ℝ)*Real.log q)) : ℂ)) =
    ((2*Real.log q*Real.exp (-e*((m+1:ℕ):ℝ)*Real.log q)/(q^(m+1)+1) : ℝ) : ℂ) := by
  have hq0 : 0 < q := by linarith
  have hp : q^(-(((m+1:ℕ):ℝ)*(1+a))) *
      Real.exp ((1/2+a)*(((m+1:ℕ):ℝ)*Real.log q)) = q^(-(((m+1:ℕ):ℝ)/2)) := by
    rw [Real.rpow_def_of_pos hq0, Real.rpow_def_of_pos hq0, ← Real.exp_add]
    congr 1
    ring
  calc
    _ = ((Real.log q*(q^(-(((m+1:ℕ):ℝ)*(1+a))) *
        Real.exp ((1/2+a)*(((m+1:ℕ):ℝ)*Real.log q))) : ℝ) : ℂ) *
        tvKernel e (((m+1:ℕ):ℝ)*Real.log q) := by
      simp only [Complex.ofReal_mul]
      ring
    _ = _ := by rw [hp]; exact tvKernel_prime_power_term e hq m

end UnitDistance.NumberFieldAnalysis

namespace UnitDistance.NumberFieldAnalysis

variable (K : Type*) [Field K] [NumberField K]

/-- Literal prime-power contribution before cancellation of the contour
parameter; this is exactly the explicit formula's summand at zero. -/
def tvPrimePairTerm (e a : ℝ)
    (pk : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} × ℕ) : ℂ :=
  ((Real.log (Ideal.absNorm pk.1.1)*
    (Ideal.absNorm pk.1.1 : ℝ)^(-(((pk.2+1:ℕ):ℝ)*(1+a))) : ℝ) : ℂ)*
    (tvKernel e (((pk.2+1:ℕ):ℝ)*Real.log (Ideal.absNorm pk.1.1))*
      (Real.exp ((1/2+a)*(((pk.2+1:ℕ):ℝ)*Real.log (Ideal.absNorm pk.1.1))) : ℂ))

/-- The actual prime-side series at zero, written without the explicit-formula
library so that the counting and regrouping proof can be checked independently. -/
def tvPrimeOrigin (e a : ℝ) : ℂ := ∑' pk, tvPrimePairTerm K e a pk

/-- Fubini and actual absolute-norm fibers give the prime-count series.
Summability of the literal prime-side double series is the explicit input. -/
theorem tvPrimeOrigin_primeNormCount_hasSum {e a : ℝ}
    (he : 0 ≤ e) (hsum : Summable (tvPrimePairTerm K e a)) :
    HasSum (fun q : ℕ => (primeNormCount K (q+2) : ℝ)*tvPrimeWeight e (q+2))
      (tvPrimeOrigin K e a).re := by
  have hnorm : ∀ P : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥},
      1 < (Ideal.absNorm P.1 : ℝ) := fun P => by
    exact_mod_cast primeIdeal_absNorm_gt_one K ((tvPrimeIdealEquiv K) P)
  let f : ({P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} × ℕ) → ℂ := fun pk =>
    ((Real.log (Ideal.absNorm pk.1.1)*
      (Ideal.absNorm pk.1.1 : ℝ)^(-(((pk.2+1:ℕ):ℝ)/2)) : ℝ) : ℂ)*
      tvKernel e (((pk.2+1:ℕ):ℝ)*Real.log (Ideal.absNorm pk.1.1))
  have hterm : ∀ pk : ({P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} × ℕ),
      tvPrimePairTerm K e a pk = f pk := by
    intro pk
    dsimp only [tvPrimePairTerm, f]
    rw [tvKernel_prime_side_term e a (hnorm pk.1), tvKernel_prime_power_term e (hnorm pk.1)]
  have hs : Summable f := hsum.congr hterm
  have hzero : tvPrimeOrigin K e a = ∑' pk, f pk := tsum_congr hterm
  have hpower : ∀ P : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥},
      (∑' m : ℕ, f (P,m)) = (tvPrimeWeight e (Ideal.absNorm P.1) : ℂ) := by
    intro P
    exact (hasSum_tvKernel_prime_power_terms he (hnorm P)).tsum_eq
  have hp : HasSum (fun P : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} =>
      (tvPrimeWeight e (Ideal.absNorm P.1) : ℂ))
      (tvPrimeOrigin K e a) := by
    have h := hs.prod.hasSum
    rw [← hs.tsum_prod, ← hzero] at h
    have hfun := funext hpower
    rw [hfun] at h
    exact h
  have hreal : HasSum (fun P : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} =>
      tvPrimeWeight e (Ideal.absNorm P.1))
      (tvPrimeOrigin K e a).re := by
    simpa only [Complex.ofReal_re] using Complex.hasSum_re hp
  have hheight : HasSum (fun P : HeightOneSpectrum (𝓞 K) =>
      tvPrimeWeight e (Ideal.absNorm P.asIdeal))
      (tvPrimeOrigin K e a).re :=
    (tvPrimeIdealEquiv K).hasSum_iff.mp hreal
  simpa only [Nat.cast_add, Nat.cast_ofNat] using
    tv_primeNormCount_hasSum_shift K (weight := fun q : ℕ => tvPrimeWeight e q) hheight

/-- Any finite collection of actual prime norms contributes no more than
the genuine explicit-formula prime side at zero. -/
theorem finite_primeNormCount_tvPrimeWeight_le_origin {e a : ℝ}
    (he : 0 ≤ e) (hsum : Summable (tvPrimePairTerm K e a)) (J : Finset ℕ) :
    (∑ q ∈ J, (primeNormCount K (q+2) : ℝ)*tvPrimeWeight e (q+2)) ≤
      (tvPrimeOrigin K e a).re := by
  have h := tvPrimeOrigin_primeNormCount_hasSum K he hsum
  rw [← h.tsum_eq]
  apply Summable.sum_le_tsum J (fun q _ => ?_) h.summable
  exact mul_nonneg (Nat.cast_nonneg _) (tvPrimeWeight_nonneg e (by
    have := Nat.cast_nonneg (α := ℝ) q
    linarith))

end UnitDistance.NumberFieldAnalysis
