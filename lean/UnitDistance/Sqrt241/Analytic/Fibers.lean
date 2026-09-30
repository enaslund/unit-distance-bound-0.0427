module

public import UnitDistance.FiniteEulerCorrection
public import UnitDistance.PrimeDebit
public import UnitDistance.GaloisPrimeNormCounts
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum

@[expose] public section
set_option backward.privateInPublic true


/-!
# Weighted Euler defects above finitely many rational primes

Port of the finite Euler-correction interface (`FiniteEulerCorrection`,
and the research files `RationalPrimeEulerCensus`,
`FixedZetaRetainedCertificateAstra`, `FixedZetaRetainedRationalFactorsAstra`)
to an arbitrary nonnegative weight `φ` on prime norms that is antitone.  The
two weights used are the Euler logarithm `primeEulerLog · s` (for
`log ζ(s)`) and the prime-debit weight `log q/(q²-1)` (for the logarithmic
derivative at two).

For an extension `K/F` of number fields and a finite set `T` of rational
primes, the normalized `φ`-sum of `K` is at most that of `F` minus the drop
of the normalized local contributions at the primes of `T`.  For Galois
fields the local contribution at `p` is `φ(p^f)/(e f)` with the actual
indices `e`, `f` of `p`.
-/

noncomputable section
open NumberField IsDedekindDomain
open scoped BigOperators

namespace UnitDistance.Sqrt241.Analytic

open UnitDistance.NumberFieldAnalysis

section Generic

variable (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K]
  [Algebra F K]

/-- The slack of the local comparison above one prime of `F` for the weight `φ`. -/
def weightFiberDefect (φ : ℕ → ℝ) (p : HeightOneSpectrum (𝓞 F)) : ℝ :=
  (Module.finrank F K : ℝ) * φ (Ideal.absNorm p.asIdeal) -
    ∑ P : PrimeFiber F K p, φ (Ideal.absNorm P.1.asIdeal)

/-- Hypotheses on a weight: nonnegative and antitone on the norms `> 1`. -/
structure IsNormWeight (φ : ℕ → ℝ) : Prop where
  nonneg : ∀ q : ℕ, 1 < q → 0 ≤ φ q
  anti : ∀ q Q : ℕ, 1 < q → q ≤ Q → φ Q ≤ φ q

theorem weightFiberDefect_nonneg {φ : ℕ → ℝ} (hφ : IsNormWeight φ)
    (p : HeightOneSpectrum (𝓞 F)) : 0 ≤ weightFiberDefect F K φ p := by
  unfold weightFiberDefect
  have hp := primeIdeal_absNorm_gt_one F p
  have hsum : (∑ P : PrimeFiber F K p, φ (Ideal.absNorm P.1.asIdeal)) ≤
      (Module.finrank F K : ℝ) * φ (Ideal.absNorm p.asIdeal) := by
    calc
      (∑ P : PrimeFiber F K p, φ (Ideal.absNorm P.1.asIdeal)) ≤
          ∑ _P : PrimeFiber F K p, φ (Ideal.absNorm p.asIdeal) := by
        apply Finset.sum_le_sum
        intro P _
        exact hφ.anti _ _ hp (primeFiber_norm_le F K p P)
      _ = (Fintype.card (PrimeFiber F K p) : ℝ) * φ (Ideal.absNorm p.asIdeal) := by
        simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast primeFiber_card_le F K p)
        (hφ.nonneg _ hp)
  linarith

/-- The local defects sum to the global gap. -/
theorem weightFiberDefect_hasSum {φ : ℕ → ℝ} {ΦF ΦK : ℝ}
    (hF : HasSum (fun P : HeightOneSpectrum (𝓞 F) => φ (Ideal.absNorm P.asIdeal)) ΦF)
    (hK : HasSum (fun P : HeightOneSpectrum (𝓞 K) => φ (Ideal.absNorm P.asIdeal)) ΦK) :
    HasSum (fun p : HeightOneSpectrum (𝓞 F) => weightFiberDefect F K φ p)
      ((Module.finrank F K : ℝ) * ΦF - ΦK) := by
  have hK' := hK.tsum_fiberwise (HeightOneSpectrum.under (𝓞 F))
  change HasSum
    (fun p : HeightOneSpectrum (𝓞 F) =>
      ∑' P : PrimeFiber F K p, φ (Ideal.absNorm P.1.asIdeal)) ΦK at hK'
  have hK'' : HasSum
      (fun p : HeightOneSpectrum (𝓞 F) =>
        ∑ P : PrimeFiber F K p, φ (Ideal.absNorm P.1.asIdeal)) ΦK := by
    simpa only [tsum_fintype] using hK'
  simpa only [weightFiberDefect] using (hF.mul_left (Module.finrank F K : ℝ)).sub hK''

/-- Normalized comparison after subtracting finitely many local defects. -/
theorem normalized_weight_le_sub_defects {φ : ℕ → ℝ} (hφ : IsNormWeight φ) {ΦF ΦK : ℝ}
    (hF : HasSum (fun P : HeightOneSpectrum (𝓞 F) => φ (Ideal.absNorm P.asIdeal)) ΦF)
    (hK : HasSum (fun P : HeightOneSpectrum (𝓞 K) => φ (Ideal.absNorm P.asIdeal)) ΦK)
    (J : Finset (HeightOneSpectrum (𝓞 F))) :
    ΦK / (Module.finrank ℚ K : ℝ) ≤
      ΦF / (Module.finrank ℚ F : ℝ) -
        (∑ p ∈ J, weightFiberDefect F K φ p) / (Module.finrank ℚ K : ℝ) := by
  have h := weightFiberDefect_hasSum F K hF hK
  have hJ : (∑ p ∈ J, weightFiberDefect F K φ p) ≤ (Module.finrank F K : ℝ) * ΦF - ΦK := by
    rw [← h.tsum_eq]
    exact h.summable.sum_le_tsum J fun p _ => weightFiberDefect_nonneg F K hφ p
  have hdF : (0 : ℝ) < Module.finrank ℚ F := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := F)
  have hdK : (0 : ℝ) < Module.finrank ℚ K := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := K)
  have hdeg : (Module.finrank ℚ K : ℝ) =
      (Module.finrank ℚ F : ℝ) * (Module.finrank F K : ℝ) := by
    exact_mod_cast (Module.finrank_mul_finrank ℚ F K).symm
  have hraw : ΦK ≤ (Module.finrank F K : ℝ) * ΦF - ∑ p ∈ J, weightFiberDefect F K φ p := by
    linarith
  calc
    ΦK / (Module.finrank ℚ K : ℝ) ≤
        ((Module.finrank F K : ℝ) * ΦF - ∑ p ∈ J, weightFiberDefect F K φ p) /
          (Module.finrank ℚ K : ℝ) := div_le_div_of_nonneg_right hraw hdK.le
    _ = _ := by
      rw [hdeg]
      have hr : (0 : ℝ) < Module.finrank F K := by
        exact_mod_cast Module.finrank_pos (R := F) (M := K)
      field_simp

end Generic

section RationalPrimes

/-- The height-one prime of `𝓞 ℚ` corresponding to a natural prime. -/
def rationalPrimePlace (p : Nat.Primes) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm p

theorem rationalPrimePlace_natGenerator (p : Nat.Primes) :
    Rat.HeightOneSpectrum.natGenerator (rationalPrimePlace p) = p.val :=
  congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply p)

theorem prime_mem_rationalPrimePlace (p : Nat.Primes) :
    (p.val : 𝓞 ℚ) ∈ (rationalPrimePlace p).asIdeal := by
  have hmem : (p.val : ℤ) ∈
      (rationalPrimePlace p).asIdeal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) := by
    rw [← Rat.HeightOneSpectrum.span_natGenerator, rationalPrimePlace_natGenerator]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hh : (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) (p.val : 𝓞 ℚ) ∈
      (rationalPrimePlace p).asIdeal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) := by
    simpa using hmem
  exact Ideal.apply_mem_of_equiv_iff.mp hh

theorem rationalPrimePlace_asIdeal (p : Nat.Primes) :
    (rationalPrimePlace p).asIdeal = Ideal.span {(p.val : 𝓞 ℚ)} := by
  change (Ideal.span {(p.val : ℤ)}).map
    (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm.toRingHom = _
  rw [Ideal.map_span, Set.image_singleton]
  simp only [map_natCast]

variable (F : Type*) [Field F] [NumberField F]

/-- All primes of `F` above all rational primes inject into the primes of `F`. -/
def rationalPrimeFiberEmbedding :
    (Σ p : Nat.Primes, PrimeFiber ℚ F (rationalPrimePlace p)) ↪
      HeightOneSpectrum (𝓞 F) where
  toFun x := x.2.1
  inj' := by
    rintro ⟨p, P⟩ ⟨q, Q⟩ h
    have hpq : p = q := by
      apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm.injective
      calc
        rationalPrimePlace p = HeightOneSpectrum.under (𝓞 ℚ) P.1 := P.2.symm
        _ = HeightOneSpectrum.under (𝓞 ℚ) Q.1 := congrArg _ h
        _ = rationalPrimePlace q := Q.2
    subst q
    congr
    exact Subtype.ext h

/-- The finite set of primes of `F` above a finite set of rational primes. -/
def rationalPrimeBaseSet (S : Finset Nat.Primes) : Finset (HeightOneSpectrum (𝓞 F)) :=
  (S.sigma fun _ => Finset.univ).map (rationalPrimeFiberEmbedding F)

/-- The `φ`-defect of `K/F` above one rational prime. -/
def rationalPrimeWeightDefect (K : Type*) [Field K] [NumberField K] [Algebra F K]
    (φ : ℕ → ℝ) (p : Nat.Primes) : ℝ :=
  ∑ P : PrimeFiber ℚ F (rationalPrimePlace p), weightFiberDefect F K φ P.1

theorem sum_rationalPrimeBaseSet (K : Type*) [Field K] [NumberField K] [Algebra F K]
    (φ : ℕ → ℝ) (S : Finset Nat.Primes) :
    (∑ P ∈ rationalPrimeBaseSet F S, weightFiberDefect F K φ P) =
      ∑ p ∈ S, rationalPrimeWeightDefect F K φ p := by
  rw [rationalPrimeBaseSet, Finset.sum_map]
  simp only [Finset.sum_sigma', rationalPrimeFiberEmbedding, rationalPrimeWeightDefect]
  rfl

/-- The normalized `φ`-contribution of all primes of `F` above `p`. -/
def normalizedRationalPrimeContribution (φ : ℕ → ℝ) (p : Nat.Primes) : ℝ :=
  (∑ P : PrimeFiber ℚ F (rationalPrimePlace p), φ (Ideal.absNorm P.1.asIdeal)) /
    (Module.finrank ℚ F : ℝ)

/-- Primes above `p` in a tower, indexed directly or through the middle field. -/
def rationalPrimeTowerFiberEquiv
    (K : Type*) [Field K] [NumberField K] [Algebra F K] [IsScalarTower ℚ F K]
    (p : Nat.Primes) :
    (Σ P : PrimeFiber ℚ F (rationalPrimePlace p), PrimeFiber F K P.1) ≃
      PrimeFiber ℚ K (rationalPrimePlace p) :=
  Equiv.ofBijective (fun x => ⟨x.2.1, by
      apply HeightOneSpectrum.ext
      change x.2.1.asIdeal.under (𝓞 ℚ) = (rationalPrimePlace p).asIdeal
      rw [← Ideal.under_under (A := 𝓞 ℚ) (B := 𝓞 F)]
      rw [show x.2.1.asIdeal.under (𝓞 F) = x.1.1.asIdeal from
        congrArg HeightOneSpectrum.asIdeal x.2.2]
      exact congrArg HeightOneSpectrum.asIdeal x.1.2⟩) (by
    constructor
    · rintro ⟨P, Q⟩ ⟨P', Q'⟩ h
      have hQ : Q.1 = Q'.1 := congrArg Subtype.val h
      have hP : P.1 = P'.1 := by
        rw [← Q.2, ← Q'.2, hQ]
      have hP' : P = P' := Subtype.ext hP
      subst P'
      have hQ' : Q = Q' := Subtype.ext hQ
      subst Q'
      rfl
    · intro Q
      let P : PrimeFiber ℚ F (rationalPrimePlace p) :=
        ⟨Q.1.under (𝓞 F), by
          apply HeightOneSpectrum.ext
          change (Q.1.asIdeal.under (𝓞 F)).under (𝓞 ℚ) =
            (rationalPrimePlace p).asIdeal
          rw [Ideal.under_under (A := 𝓞 ℚ) (B := 𝓞 F)]
          exact congrArg HeightOneSpectrum.asIdeal Q.2⟩
      refine ⟨⟨P, ⟨Q.1, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      rfl)

theorem sum_primeFiber_tower_eq_rationalPrimeFiber
    (K : Type*) [Field K] [NumberField K] [Algebra F K] [IsScalarTower ℚ F K]
    (φ : ℕ → ℝ) (p : Nat.Primes) :
    (∑ P : PrimeFiber ℚ F (rationalPrimePlace p),
        ∑ Q : PrimeFiber F K P.1, φ (Ideal.absNorm Q.1.asIdeal)) =
      ∑ Q : PrimeFiber ℚ K (rationalPrimePlace p), φ (Ideal.absNorm Q.1.asIdeal) := by
  calc
    _ = ∑ x : (Σ P : PrimeFiber ℚ F (rationalPrimePlace p), PrimeFiber F K P.1),
          φ (Ideal.absNorm x.2.1.asIdeal) := by
      symm
      exact Fintype.sum_sigma _
    _ = _ := Fintype.sum_equiv (rationalPrimeTowerFiberEquiv F K p) _ _ (fun _ => rfl)

/-- The defect above `p`, divided by the top degree, is the drop of the
normalized local contributions. -/
theorem rationalPrimeWeightDefect_div_degree
    (K : Type*) [Field K] [NumberField K] [Algebra F K] [IsScalarTower ℚ F K]
    (φ : ℕ → ℝ) (p : Nat.Primes) :
    rationalPrimeWeightDefect F K φ p / (Module.finrank ℚ K : ℝ) =
      normalizedRationalPrimeContribution F φ p -
        normalizedRationalPrimeContribution K φ p := by
  have hsum := sum_primeFiber_tower_eq_rationalPrimeFiber F K φ p
  have hdF : (0 : ℝ) < Module.finrank ℚ F := by
    exact_mod_cast Module.finrank_pos (R := ℚ) (M := F)
  have hr : (0 : ℝ) < Module.finrank F K := by
    exact_mod_cast Module.finrank_pos (R := F) (M := K)
  have hdeg : (Module.finrank ℚ K : ℝ) =
      (Module.finrank ℚ F : ℝ) * (Module.finrank F K : ℝ) := by
    exact_mod_cast (Module.finrank_mul_finrank ℚ F K).symm
  unfold rationalPrimeWeightDefect weightFiberDefect normalizedRationalPrimeContribution
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, hdeg]
  field_simp

/-- Normalized comparison after subtracting the local drops above a finite
set of rational primes. -/
theorem normalized_weight_le_sub_contributions
    (K : Type*) [Field K] [NumberField K] [Algebra F K] [IsScalarTower ℚ F K]
    {φ : ℕ → ℝ} (hφ : IsNormWeight φ) {ΦF ΦK : ℝ}
    (hF : HasSum (fun P : HeightOneSpectrum (𝓞 F) => φ (Ideal.absNorm P.asIdeal)) ΦF)
    (hK : HasSum (fun P : HeightOneSpectrum (𝓞 K) => φ (Ideal.absNorm P.asIdeal)) ΦK)
    (S : Finset Nat.Primes) :
    ΦK / (Module.finrank ℚ K : ℝ) ≤
      ΦF / (Module.finrank ℚ F : ℝ) -
        ∑ p ∈ S, (normalizedRationalPrimeContribution F φ p -
          normalizedRationalPrimeContribution K φ p) := by
  have h := normalized_weight_le_sub_defects F K hφ hF hK (rationalPrimeBaseSet F S)
  rw [sum_rationalPrimeBaseSet, Finset.sum_div] at h
  simp_rw [rationalPrimeWeightDefect_div_degree F K φ] at h
  exact h

end RationalPrimes

section Galois

variable (L : Type*) [Field L] [NumberField L]

/-- A prime above `p` lies over the integer ideal `(p)`. -/
theorem rationalPrimeFiber_liesOver_integer (p : Nat.Primes)
    (P : PrimeFiber ℚ L (rationalPrimePlace p)) :
    P.1.asIdeal.LiesOver (rationalPrimeIdeal p.val) := by
  have : Fact p.val.Prime := ⟨p.property⟩
  have := P.1.isPrime
  have : P.1.asIdeal.LiesOver (rationalPrimePlace p).asIdeal :=
    primeFiber_liesOver ℚ L (rationalPrimePlace p) P
  have hmem : (p.val : 𝓞 L) ∈ P.1.asIdeal := by
    have h : (p.val : 𝓞 ℚ) ∈ P.1.asIdeal.under (𝓞 ℚ) := by
      rw [← Ideal.over_def P.1.asIdeal (rationalPrimePlace p).asIdeal]
      exact prime_mem_rationalPrimePlace p
    change algebraMap (𝓞 ℚ) (𝓞 L) (p.val : 𝓞 ℚ) ∈ P.1.asIdeal at h
    simpa using h
  constructor
  apply Ideal.IsMaximal.eq_of_le (inferInstance : (rationalPrimeIdeal p.val).IsMaximal)
    (Ideal.IsPrime.ne_top (inferInstance : (P.1.asIdeal.under ℤ).IsPrime))
  rw [Ideal.span_singleton_le_iff_mem]
  change algebraMap ℤ (𝓞 L) (p.val : ℤ) ∈ P.1.asIdeal
  simpa using hmem

variable [IsGalois ℚ L]

/-- In a Galois field, every prime above `p` has norm `p^f`. -/
theorem rationalPrimeFiber_norm_eq (p : Nat.Primes) (f : ℕ)
    (hres : (rationalPrimeIdeal p.val).inertiaDegIn (𝓞 L) = f)
    (P : PrimeFiber ℚ L (rationalPrimePlace p)) :
    Ideal.absNorm P.1.asIdeal = p.val ^ f := by
  have : Fact p.val.Prime := ⟨p.property⟩
  have := P.1.isPrime
  have : P.1.asIdeal.IsMaximal := P.1.isPrime.isMaximal P.1.ne_bot
  have : P.1.asIdeal.LiesOver (rationalPrimeIdeal p.val) :=
    rationalPrimeFiber_liesOver_integer L p P
  rw [← Ideal.pow_inertiaDeg p.val P.1.asIdeal]
  rw [← Ideal.inertiaDegIn_eq_inertiaDeg (rationalPrimeIdeal p.val)
    P.1.asIdeal Gal(L/ℚ), hres]

/-- The rational-prime fiber is the prime-norm fiber at `p^f`. -/
def rationalPrimeFiberEquivPrimeNormFiber (p : Nat.Primes) (f : ℕ) (hf : 0 < f)
    (hres : (rationalPrimeIdeal p.val).inertiaDegIn (𝓞 L) = f) :
    PrimeFiber ℚ L (rationalPrimePlace p) ≃ PrimeNormFiber L (p.val ^ f) :=
  Equiv.ofBijective (fun P => ⟨P.1, rationalPrimeFiber_norm_eq L p f hres P⟩) (by
    constructor
    · intro P Q h
      apply Subtype.ext
      exact congrArg (fun R : PrimeNormFiber L (p.val ^ f) => R.1) h
    · intro Q
      have hq : 1 < p.val ^ f := Nat.one_lt_pow hf.ne' p.property.one_lt
      have hlies : Q.1.asIdeal.LiesOver (rationalPrimeIdeal p.val) := by
        have h := primeNormFiber_liesOver L hq Q
        simpa only [p.property.pow_minFac hf.ne'] using h
      have : Fact p.val.Prime := ⟨p.property⟩
      have := Q.1.isPrime
      have : Q.1.asIdeal.LiesOver (rationalPrimeIdeal p.val) := hlies
      have hmem : (p.val : 𝓞 L) ∈ Q.1.asIdeal := by
        have h : (p.val : ℤ) ∈ Q.1.asIdeal.under ℤ := by
          rw [← Ideal.over_def Q.1.asIdeal (rationalPrimeIdeal p.val)]
          exact Ideal.subset_span (Set.mem_singleton _)
        change algebraMap ℤ (𝓞 L) (p.val : ℤ) ∈ Q.1.asIdeal at h
        simpa using h
      let P : PrimeFiber ℚ L (rationalPrimePlace p) := ⟨Q.1, by
        apply HeightOneSpectrum.ext
        apply Eq.symm
        apply Ideal.IsMaximal.eq_of_le
          ((rationalPrimePlace p).isPrime.isMaximal (rationalPrimePlace p).ne_bot)
          (Ideal.IsPrime.ne_top (inferInstance : (Q.1.asIdeal.under (𝓞 ℚ)).IsPrime))
        rw [rationalPrimePlace_asIdeal, Ideal.span_singleton_le_iff_mem]
        change algebraMap (𝓞 ℚ) (𝓞 L) (p.val : 𝓞 ℚ) ∈ Q.1.asIdeal
        simpa using hmem⟩
      refine ⟨P, ?_⟩
      apply Subtype.ext
      rfl)

/-- Exact normalized count of the primes above `p` from the actual indices. -/
theorem normalizedPrimeNormCount_eq_inv_indices (p : ℕ) (hp : p.Prime) (e f : ℕ)
    (hepos : 0 < e) (hfpos : 0 < f)
    (he : (rationalPrimeIdeal p).ramificationIdxIn (𝓞 L) = e)
    (hf : (rationalPrimeIdeal p).inertiaDegIn (𝓞 L) = f) :
    normalizedPrimeNormCount L (p ^ f) = 1 / ((e : ℝ) * f) := by
  have h := primeNormCount_mul_ramification_residue L p hp e f hfpos he hf
  have hd : (Module.finrank ℚ L : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := L)).ne'
  have hef : (e : ℝ) * f ≠ 0 := by positivity
  unfold normalizedPrimeNormCount
  apply (div_eq_div_iff hd hef).2
  simpa only [one_mul, Nat.cast_mul] using congrArg (fun n : ℕ => (n : ℝ)) h

/-- The normalized local contribution of a Galois field at `p` is
`φ(p^f)/(e f)` with the actual indices. -/
theorem normalizedRationalPrimeContribution_eq_of_indices (φ : ℕ → ℝ)
    (p : Nat.Primes) (e f : ℕ) (hepos : 0 < e) (hfpos : 0 < f)
    (he : (rationalPrimeIdeal p.val).ramificationIdxIn (𝓞 L) = e)
    (hf : (rationalPrimeIdeal p.val).inertiaDegIn (𝓞 L) = f) :
    normalizedRationalPrimeContribution L φ p = φ (p.val ^ f) / ((e : ℝ) * f) := by
  have hnorm : ∀ P : PrimeFiber ℚ L (rationalPrimePlace p),
      Ideal.absNorm P.1.asIdeal = p.val ^ f := rationalPrimeFiber_norm_eq L p f hf
  have hfun : (fun P : PrimeFiber ℚ L (rationalPrimePlace p) =>
      φ (Ideal.absNorm P.1.asIdeal)) = fun _ => φ (p.val ^ f) := by
    funext P
    rw [hnorm P]
  have hcard : Fintype.card (PrimeFiber ℚ L (rationalPrimePlace p)) =
      Nat.card (PrimeNormFiber L (p.val ^ f)) := by
    have := Fintype.ofFinite (PrimeNormFiber L (p.val ^ f))
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr (rationalPrimeFiberEquivPrimeNormFiber L p f hfpos hf)
  have hcount := normalizedPrimeNormCount_eq_inv_indices L p.val p.property e f hepos hfpos he hf
  unfold normalizedPrimeNormCount primeNormCount at hcount
  unfold normalizedRationalPrimeContribution
  rw [hfun, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
  rw [mul_div_right_comm, hcount]
  ring

/-- The actual indices are positive. -/
theorem ramificationIdxIn_pos (p : Nat.Primes) :
    0 < (rationalPrimeIdeal p.val).ramificationIdxIn (𝓞 L) := by
  have : Fact p.val.Prime := ⟨p.property⟩
  exact Nat.pos_of_ne_zero (Ideal.ramificationIdxIn_ne_zero Gal(L/ℚ))

theorem inertiaDegIn_pos (p : Nat.Primes) :
    0 < (rationalPrimeIdeal p.val).inertiaDegIn (𝓞 L) := by
  have : Fact p.val.Prime := ⟨p.property⟩
  exact Nat.pos_of_ne_zero (Ideal.inertiaDegIn_ne_zero Gal(L/ℚ))

/-- Evaluation with the field's own indices. -/
theorem normalizedRationalPrimeContribution_eq (φ : ℕ → ℝ) (p : Nat.Primes) :
    normalizedRationalPrimeContribution L φ p =
      φ (p.val ^ (rationalPrimeIdeal p.val).inertiaDegIn (𝓞 L)) /
        (((rationalPrimeIdeal p.val).ramificationIdxIn (𝓞 L) : ℝ) *
          (rationalPrimeIdeal p.val).inertiaDegIn (𝓞 L)) :=
  normalizedRationalPrimeContribution_eq_of_indices L φ p _ _
    (ramificationIdxIn_pos L p) (inertiaDegIn_pos L p) rfl rfl

end Galois

end UnitDistance.Sqrt241.Analytic
