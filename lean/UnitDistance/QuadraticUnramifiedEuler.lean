module

public import UnitDistance.RelativeEuler
public import UnitDistance.RelativeDiscriminant
public import UnitDistance.HeckeNormCharacterEuler

@[expose] public section
set_option backward.privateInPublic true


/-! The exact local Euler denominator of every actual unramified quadratic
prime fiber. The sign is defined by the cardinality of that fiber. -/
noncomputable section
open NumberField IsDedekindDomain
open scoped BigOperators Real Classical nonZeroDivisors
namespace UnitDistance.NumberFieldAnalysis

/-- A finite family of positive residue degrees adding to two has precisely
the split or inert quadratic Euler polynomial. -/
theorem prod_one_sub_pow_of_sum_two {ι : Type*} [Fintype ι]
    (f : ι → ℕ) (hf : ∀ i, 0 < f i) (hs : ∑ i, f i = 2) (z : ℂ) :
    (∏ i, (1-z^f i)) = (1-z)*(1-(if Fintype.card ι = 2 then (1:ℂ) else -1)*z) := by
  have hc_le : Fintype.card ι ≤ 2 := by
    calc Fintype.card ι = ∑ _i : ι, (1:ℕ) := by simp
         _ ≤ ∑ i, f i := Finset.sum_le_sum (fun i _ => hf i)
         _ = 2 := hs
  have hc_pos : 0 < Fintype.card ι := by
    by_contra h
    have hz : Fintype.card ι = 0 := by omega
    haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hz
    simp at hs
  have hc : Fintype.card ι = 1 ∨ Fintype.card ι = 2 := by omega
  rcases hc with hc | hc
  · obtain ⟨a,ha⟩ := Fintype.card_eq_one_iff.mp hc
    have hsum : (∑ i, f i) = f a := by
      calc _ = ∑ _i : ι, f a := Finset.sum_congr rfl (fun i _ => congrArg f (ha i))
           _ = f a := by simp [hc]
    have hval (i : ι) : f i = 2 := by rw [ha i, ← hsum, hs]
    simp_rw [hval]
    simp only [Finset.prod_const, Finset.card_univ, hc]
    norm_num
    ring
  · have hval : ∀ i : ι, f i = 1 := by
      have heq : (∑ _i : ι, (1:ℕ)) = ∑ i, f i := by simpa [hc] using hs.symm
      have h := (Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hf i)).mp heq
      exact fun i => (h i (Finset.mem_univ i)).symm
    simp only [hc, ↓reduceIte, one_mul]
    simp_rw [hval, pow_one]
    rw [Finset.prod_const, Finset.card_univ, hc]
    ring

variable (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K]
  [Algebra F K]

/-- The canonical quadratic local sign: +1 for the actual two-prime fiber,
−1 otherwise. Under quadratic unramifiedness the latter fiber is inert. -/
def quadraticPrimeSign (p : HeightOneSpectrum (𝓞 F)) : ℂ :=
  if Fintype.card (PrimeFiber F K p) = 2 then 1 else -1

theorem norm_quadraticPrimeSign (p : HeightOneSpectrum (𝓞 F)) :
    ‖quadraticPrimeSign F K p‖ = 1 := by
  unfold quadraticPrimeSign
  split_ifs <;> norm_num

theorem quadraticPrimeSign_eq_one_or_neg_one (p : HeightOneSpectrum (𝓞 F)) :
    quadraticPrimeSign F K p = 1 ∨ quadraticPrimeSign F K p = -1 := by
  unfold quadraticPrimeSign
  split_ifs <;> simp

/-- The actual ramification index in every prime fiber is one. -/
theorem primeFiber_ramificationIdx_eq_one (hu : FiniteUnramified F K)
    (p : HeightOneSpectrum (𝓞 F)) (P : PrimeFiber F K p) :
    Ideal.ramificationIdx' p.asIdeal P.1.asIdeal = 1 := by
  letI : P.1.asIdeal.IsPrime := P.1.isPrime
  letI := primeFiber_liesOver F K p P
  letI := hu P.1.asIdeal (P.1.isPrime.isMaximal P.1.ne_bot)
  rw [Ideal.ramificationIdx'_eq_ramificationIdx p.asIdeal P.1.asIdeal p.ne_bot]
  exact Ideal.ramificationIdx_eq_one P.1.asIdeal (𝓞 F)

/-- Actual residue degrees in an unramified prime fiber sum to the field degree. -/
theorem primeFiber_sum_inertiaDeg_of_unramified (hu : FiniteUnramified F K)
    (p : HeightOneSpectrum (𝓞 F)) :
    (∑ P : PrimeFiber F K p, Ideal.inertiaDeg' p.asIdeal P.1.asIdeal) = Module.finrank F K := by
  letI : p.asIdeal.IsMaximal := p.isPrime.isMaximal p.ne_bot
  have hsum : (∑ P : PrimeFiber F K p,
      Ideal.ramificationIdx' p.asIdeal P.1.asIdeal * Ideal.inertiaDeg' p.asIdeal P.1.asIdeal) =
      Module.finrank F K := by
    calc
      _ = ∑ Q : ↥(IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 K)),
          Ideal.ramificationIdx' p.asIdeal Q.1 * Ideal.inertiaDeg' p.asIdeal Q.1 :=
        Fintype.sum_equiv (primeFiberEquiv F K p) _ _ (fun _ => rfl)
      _ = ∑ Q ∈ IsDedekindDomain.primesOverFinset p.asIdeal (𝓞 K),
          Ideal.ramificationIdx' p.asIdeal Q * Ideal.inertiaDeg' p.asIdeal Q := by
        exact Finset.sum_coe_sort _ (fun Q : Ideal (𝓞 K) =>
          Ideal.ramificationIdx' p.asIdeal Q * Ideal.inertiaDeg' p.asIdeal Q)
      _ = Module.finrank F K := Ideal.sum_ramification_inertia (𝓞 K) F K p.ne_bot
  simpa only [primeFiber_ramificationIdx_eq_one F K hu, one_mul] using hsum

/-- The ordinary prime norm is exactly the base norm raised to the residue degree. -/
theorem primeFiber_absNorm_cpow (p : HeightOneSpectrum (𝓞 F)) (P : PrimeFiber F K p) (s : ℂ) :
    (Ideal.absNorm P.1.asIdeal : ℂ)^(-s) =
      ((Ideal.absNorm p.asIdeal : ℂ)^(-s))^(Ideal.inertiaDeg' p.asIdeal P.1.asIdeal) := by
  letI := primeFiber_liesOver F K p P
  rw [Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P.1.asIdeal p.asIdeal p.isPrime p.ne_bot]
  exact map_pow (UnitDistance.DedekindEuler.cpowHom s) _ _

/-- Exact local Euler denominator for every complex argument, with the sign
selected from actual splitting. There is no local splitting premise. -/
theorem quadratic_unramified_primeFiber_factor_product
    (hquad : Module.finrank F K = 2) (hu : FiniteUnramified F K)
    (p : HeightOneSpectrum (𝓞 F)) (s : ℂ) :
    (∏ P : PrimeFiber F K p, (1-(Ideal.absNorm P.1.asIdeal : ℂ)^(-s))) =
      (1-(Ideal.absNorm p.asIdeal : ℂ)^(-s))*
        (1-quadraticPrimeSign F K p*(Ideal.absNorm p.asIdeal : ℂ)^(-s)) := by
  simp_rw [primeFiber_absNorm_cpow F K p]
  apply prod_one_sub_pow_of_sum_two
  · intro P
    letI := primeFiber_liesOver F K p P
    exact Ideal.inertiaDeg'_pos p.asIdeal P.1.asIdeal
  · rw [primeFiber_sum_inertiaDeg_of_unramified F K hu, hquad]

end UnitDistance.NumberFieldAnalysis
