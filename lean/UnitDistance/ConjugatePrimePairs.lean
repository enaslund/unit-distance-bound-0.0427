module

public import UnitDistance.FreeInvolutionPairs
public import UnitDistance.PrimeNormCounts
public import UnitDistance.RelativeIdealCosetsFamily

@[expose] public section
set_option backward.privateInPublic true


/-! Finite prime pairs constructed from the free action of actual conjugation. -/
noncomputable section
open NumberField IsDedekindDomain
open scoped Classical
namespace UnitDistance.RelativeIdealCosets
open NumberFieldAnalysis
variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K]
variable (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)

/-- Actual quadratic conjugation on nonzero prime ideals. -/
def conjugatePrime (P : HeightOneSpectrum (𝓞 K)) : HeightOneSpectrum (𝓞 K) where
  asIdeal := conjugateIdeal ι P.asIdeal
  isPrime := by
    letI := P.isPrime
    exact Ideal.map_isPrime_of_equiv (RingOfIntegers.mapRingEquiv ι.toRingEquiv)
  ne_bot := conjugateIdeal_ne_zero ι hι P.ne_bot

theorem conjugatePrime_involutive : Function.Involutive (conjugatePrime ι hι) :=
  fun P => HeightOneSpectrum.ext (conjugateIdeal_involutive ι hι P.asIdeal)

instance primeNormFiberFintype (q : ℕ) : Fintype (PrimeNormFiber K q) := Fintype.ofFinite _

/-- Conjugation restricts to each finite actual norm fiber. -/
def conjugateNormFiber (q : ℕ) (P : PrimeNormFiber K q) : PrimeNormFiber K q :=
  ⟨conjugatePrime ι hι P.1,(conjugateIdeal_absNorm ι P.1.asIdeal).trans P.2⟩

theorem conjugateNormFiber_involutive (q : ℕ) :
    Function.Involutive (conjugateNormFiber ι hι q) :=
  fun P => Subtype.ext (conjugatePrime_involutive ι hι P.1)

abbrev NormPairIndex (q : ℕ) := FreeInvolution.Representatives (conjugateNormFiber ι hι q)

/-- Each representative indexes its two actual conjugate primes. -/
def normPairPrime (q : ℕ) (s : NormPairIndex ι hι q × Bool) : HeightOneSpectrum (𝓞 K) :=
  (FreeInvolution.pair (conjugateNormFiber ι hι q) s).1

@[simp] theorem normPairPrime_norm (q : ℕ) (s : NormPairIndex ι hι q × Bool) :
    Ideal.absNorm (normPairPrime ι hι q s).asIdeal = q :=
  (FreeInvolution.pair (conjugateNormFiber ι hι q) s).2

/-- Exact half-count from a free involution, proved on the literal prime fiber. -/
theorem normPairIndex_card_mul_two (q : ℕ)
    (hfree : ∀ P : PrimeNormFiber K q, conjugateIdeal ι P.1.asIdeal ≠ P.1.asIdeal) :
    Fintype.card (NormPairIndex ι hι q) * 2 = primeNormCount K q := by
  rw [primeNormCount,Nat.card_eq_fintype_card]
  apply FreeInvolution.card_representatives_mul_two _ (conjugateNormFiber_involutive ι hι q)
  intro P he
  exact hfree P (congrArg (fun x : PrimeNormFiber K q => x.1.asIdeal) he)

variable {A : Type*} [Fintype A] (q : A → ℕ)

/-- All chosen two-element prime orbits, retaining their rational-prime label. -/
abbrev PrimePairIndex := Σ a : A, NormPairIndex ι hι (q a)

/-- Distinct norm fibers give an actual finite `PrimePairFamily`. -/
def normPrimePairFamily (hq : Function.Injective q) :
    PrimePairFamily ι (PrimePairIndex ι hι q) where
  prime x := normPairPrime ι hι (q x.1.1) (x.1.2,x.2)
  partner s := rfl
  distinct := by
    rintro ⟨⟨a,x⟩,b⟩ ⟨⟨a',y⟩,c⟩ he
    have hn := congrArg Ideal.absNorm he
    simp only [normPairPrime_norm] at hn
    have ha := hq hn
    subst a'
    have hp : FreeInvolution.pair (conjugateNormFiber ι hι (q a)) (x,b) =
        FreeInvolution.pair (conjugateNormFiber ι hι (q a)) (y,c) :=
      Subtype.ext (HeightOneSpectrum.ext he)
    have hxy := FreeInvolution.pair_injective _ (conjugateNormFiber_involutive ι hι (q a)) hp
    cases hxy
    rfl

@[simp] theorem normPrimePairFamily_norm (hq : Function.Injective q)
    (s : PrimePairIndex ι hι q) (b : Bool) :
    Ideal.absNorm ((normPrimePairFamily ι hι q hq).prime (s,b)).asIdeal = q s.1 :=
  normPairPrime_norm ι hι (q s.1) (s.2,b)

/-- The label fiber consists exactly of the chosen orbits at that norm. -/
def primePairIndexFiberEquiv (a : A) :
    {s : PrimePairIndex ι hι q // s.1 = a} ≃ NormPairIndex ι hι (q a) where
  toFun s := s.2 ▸ s.1.2
  invFun x := ⟨⟨a,x⟩,rfl⟩
  left_inv s := by rcases s with ⟨⟨a',x⟩,h⟩; cases h; rfl
  right_inv x := rfl

theorem primePairIndexFiber_card_mul_two (a : A)
    (hfree : ∀ P : PrimeNormFiber K (q a), conjugateIdeal ι P.1.asIdeal ≠ P.1.asIdeal) :
    Fintype.card {s : PrimePairIndex ι hι q // s.1 = a} * 2 = primeNormCount K (q a) := by
  rw [Fintype.card_congr (primePairIndexFiberEquiv ι hι q a)]
  exact normPairIndex_card_mul_two ι hι (q a) hfree

end UnitDistance.RelativeIdealCosets
