module

public import UnitDistance.RelativeIdealCosets
public import Mathlib.RingTheory.DedekindDomain.SInteger

@[expose] public section
set_option backward.privateInPublic true


/-! # Actual signed prime-ideal labels and their norm-one principal generators -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField nonZeroDivisors Classical
open NumberField IsDedekindDomain

namespace UnitDistance.RelativeIdealCosets

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K]
  {S : Type*} [Fintype S]

/-- A selected actual prime as an element of the fractional-ideal group. -/
def primeIdealGroup {ι : K ≃ₐ[F] K} (D : PrimePairFamily ι S) (a : S × Bool) :
    IdealGroup K :=
  FractionalIdeal.mk0 K ⟨(D.prime a).asIdeal,
    mem_nonZeroDivisors_iff_ne_zero.mpr (D.prime a).ne_bot⟩

@[simp] theorem primeIdealGroup_coe {ι : K ≃ₐ[F] K} (D : PrimePairFamily ι S)
    (a : S × Bool) :
    (primeIdealGroup D a : FractionalIdeal (𝓞 K)⁰ K) = (D.prime a).asIdeal := rfl

@[simp] theorem conjugate_primeIdealGroup {ι : K ≃ₐ[F] K} (hι : ι ≠ 1)
    (D : PrimePairFamily ι S) (s : S) :
    conjugateIdealGroup ι (primeIdealGroup D (s, false)) = primeIdealGroup D (s, true) := by
  apply Units.ext
  change conjugateFractionalIdeal ι ((D.prime (s, false)).asIdeal :
    FractionalIdeal (𝓞 K)⁰ K) = _
  rw [conjugateFractionalIdeal_coeIdeal, ← D.partner]
  rfl

/-- The literal fractional ideal `A(n)=∏ P_s^n_s` for arbitrary integer labels. -/
def signedOneSidedIdeal {ι : K ≃ₐ[F] K} (D : PrimePairFamily ι S) (n : S → ℤ) :
    IdealGroup K := ∏ s, primeIdealGroup D (s, false) ^ n s

/-- The actual anti-invariant ideal with exponents `(n_s,-n_s)`. -/
def signedStepIdeal {ι : K ≃ₐ[F] K} (D : PrimePairFamily ι S) (n : S → ℤ) :
    IdealGroup K :=
  ∏ s, primeIdealGroup D (s, false) ^ n s * primeIdealGroup D (s, true) ^ (-n s)

theorem signedOneSidedIdeal_div {ι : K ≃ₐ[F] K} (D : PrimePairFamily ι S)
    (n m : S → ℤ) :
    signedOneSidedIdeal D n / signedOneSidedIdeal D m = signedOneSidedIdeal D (n - m) := by
  unfold signedOneSidedIdeal
  rw [← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro s _
  exact (zpow_sub _ _ _).symm

theorem fractionalAntiRatio_signedOneSidedIdeal {ι : K ≃ₐ[F] K} (hι : ι ≠ 1)
    (D : PrimePairFamily ι S) (n : S → ℤ) :
    fractionalAntiRatio ι (signedOneSidedIdeal D n) = signedStepIdeal D n := by
  rw [fractionalAntiRatio_apply]
  simp only [signedOneSidedIdeal, signedStepIdeal, map_prod, map_zpow,
    conjugate_primeIdealGroup hι D]
  rw [← Finset.prod_div_distrib]
  simp only [div_eq_mul_inv, ← zpow_neg]

/-- The signed label's class in the actual relative ideal-class quotient. -/
def signedChoiceClass {ι : K ≃ₐ[F] K} (D : PrimePairFamily ι S) (n : S → ℤ) :
    RelativeUnits.RelativeClassQuotient (F := F) (K := K) :=
  relativeFractionalClass (F := F) (signedOneSidedIdeal D n)

/-- A signed-label class fiber supplies the actual principal ideal with
exponents `(n_s-n₀_s,-n_s+n₀_s)` and the literal norm-one generator `x/ι(x)`. -/
theorem same_signedChoiceClass_exists_normOne_generator {ι : K ≃ₐ[F] K} (hι : ι ≠ 1)
    (D : PrimePairFamily ι S) (n n₀ : S → ℤ)
    (h : signedChoiceClass D n = signedChoiceClass D n₀) :
    ∃ x : Kˣ, signedStepIdeal D (n - n₀) =
        toPrincipalIdeal (𝓞 K) K (fieldCoboundary ι x) ∧
      Algebra.norm F (fieldCoboundary ι x : K) = 1 := by
  obtain ⟨x, hx, hn⟩ := same_relativeFractionalClass_exists_normOne_generator ι hι
    (signedOneSidedIdeal D n) (signedOneSidedIdeal D n₀) h
  rw [← map_div, signedOneSidedIdeal_div, fractionalAntiRatio_signedOneSidedIdeal hι] at hx
  exact ⟨x, hx, hn⟩

/-- Prime multiplicity, restricted to the group of actual nonzero fractional
ideals, is an ordinary group homomorphism into the integers. -/
def idealCountHom (P : HeightOneSpectrum (𝓞 K)) : IdealGroup K →* Multiplicative ℤ where
  toFun I := Multiplicative.ofAdd (FractionalIdeal.count K P I.val)
  map_one' := congrArg Multiplicative.ofAdd (FractionalIdeal.count_one K P)
  map_mul' I J := congrArg Multiplicative.ofAdd
    (FractionalIdeal.count_mul K P I.ne_zero J.ne_zero)

theorem idealCountHom_prime {ι : K ≃ₐ[F] K} (D : PrimePairFamily ι S)
    (a : S × Bool) (P : HeightOneSpectrum (𝓞 K)) :
    idealCountHom P (primeIdealGroup D a) =
      Multiplicative.ofAdd (if D.prime a = P then 1 else 0) := by
  exact congrArg Multiplicative.ofAdd (FractionalIdeal.count_maximal K P (D.prime a))

/-- The actual first-prime multiplicity of a signed step ideal recovers its
integer label, including negative labels. -/
theorem signedStepIdeal_first_count {ι : K ≃ₐ[F] K} (D : PrimePairFamily ι S)
    (n : S → ℤ) (s : S) :
    FractionalIdeal.count K (D.prime (s, false)) (signedStepIdeal D n).val = n s := by
  have he (t : S) : D.prime (t, false) = D.prime (s, false) ↔ t = s := by
    constructor
    · intro h
      exact congrArg Prod.fst (D.distinct (congrArg HeightOneSpectrum.asIdeal h))
    · rintro rfl
      rfl
  have hn (t : S) : D.prime (t, true) ≠ D.prime (s, false) := by
    intro h
    have hh := congrArg Prod.snd (D.distinct (congrArg HeightOneSpectrum.asIdeal h))
    cases hh
  change Multiplicative.toAdd (idealCountHom (D.prime (s, false)) (signedStepIdeal D n)) = _
  simp [signedStepIdeal, map_prod, map_mul, map_zpow, idealCountHom_prime, he, hn]

/-- At the conjugate prime the actual multiplicity is the negative label. -/
theorem signedStepIdeal_second_count {ι : K ≃ₐ[F] K} (D : PrimePairFamily ι S)
    (n : S → ℤ) (s : S) :
    FractionalIdeal.count K (D.prime (s, true)) (signedStepIdeal D n).val = -n s := by
  have he (t : S) : D.prime (t, true) = D.prime (s, true) ↔ t = s := by
    constructor
    · intro h
      exact congrArg Prod.fst (D.distinct (congrArg HeightOneSpectrum.asIdeal h))
    · rintro rfl
      rfl
  have hn (t : S) : D.prime (t, false) ≠ D.prime (s, true) := by
    intro h
    have hh := congrArg Prod.snd (D.distinct (congrArg HeightOneSpectrum.asIdeal h))
    cases hh
  change Multiplicative.toAdd (idealCountHom (D.prime (s, true)) (signedStepIdeal D n)) = _
  simp [signedStepIdeal, map_prod, map_mul, map_zpow, idealCountHom_prime, he, hn]

/-- Distinct integer labels determine distinct actual anti-invariant ideals. -/
theorem signedStepIdeal_injective {ι : K ≃ₐ[F] K} (D : PrimePairFamily ι S) :
    Function.Injective (signedStepIdeal D) := by
  intro n m h
  funext s
  have hh := congrArg (fun I : IdealGroup K ↦ FractionalIdeal.count K (D.prime (s, false)) I.val) h
  simpa only [signedStepIdeal_first_count] using hh

/-- Outside the selected prime pairs, every signed step ideal has multiplicity zero. -/
theorem signedStepIdeal_count_outside {ι : K ≃ₐ[F] K} (D : PrimePairFamily ι S)
    (n : S → ℤ) (P : HeightOneSpectrum (𝓞 K)) (hP : P ∉ Set.range D.prime) :
    FractionalIdeal.count K P (signedStepIdeal D n).val = 0 := by
  have hn (a : S × Bool) : D.prime a ≠ P := fun h ↦ hP ⟨a, h⟩
  change Multiplicative.toAdd (idealCountHom P (signedStepIdeal D n)) = _
  simp [signedStepIdeal, map_prod, map_mul, map_zpow, idealCountHom_prime, hn]

end UnitDistance.RelativeIdealCosets
