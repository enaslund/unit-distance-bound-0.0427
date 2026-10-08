module

public import UnitDistance.GaloisPrimeNormCounts
public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import UnitDistance.RelativeEuler
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Prime types in number fields that need not be Galois

For number fields `M → K → L` and a rational prime `p`:

* `ramificationIdx_eq_of_sandwich`, `inertiaDeg_eq_of_sandwich`: if every prime of `M` and
  every prime of `L` above `p` has ramification index `e` (residue degree `f`), so has every
  prime of `K` above `p` (ramification indices and residue degrees are multiplicative in
  towers, and every prime of `K` lies under a prime of `L`);
* `primeNormCount_mul_of_uniform`: if every prime of `K` above `p` has type `(e, f)`, the
  primes of norm `p^f` are exactly the primes above `p` and their number times `e f` is
  `[K : ℚ]` (the fundamental identity);
* `primeFiber_card_mul_of_uniform`: the same over a number field `F` instead of `ℚ`;
* `absNorm_le_of_forall_pow_sub_mem`: if `z^q ≡ z (mod P)` for every `z`, then `N P ≤ q`;
* `map_ne_of_mul_add`: a ring automorphism `c` of `𝓞 K` moves a prime `P` if some `w`
  has `w · c(w) ∈ P` and `w + c(w) ∉ P`.

None of these needs `K` to be Galois over `ℚ`.
-/

noncomputable section

open NumberField IsDedekindDomain

namespace UnitDistance.NumberFieldAnalysis

theorem rationalPrimeIdeal_ne_bot_of_prime {p : ℕ} (hp : p.Prime) : rationalPrimeIdeal p ≠ ⊥ := by
  rw [ne_eq, Ideal.span_singleton_eq_bot]
  exact_mod_cast hp.ne_zero

theorem rationalPrimeIdeal_isMaximal_of_prime {p : ℕ} (hp : p.Prime) :
    (rationalPrimeIdeal p).IsMaximal :=
  ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
    (Nat.prime_iff_prime_int.mp hp)).isMaximal (rationalPrimeIdeal_ne_bot_of_prime hp)

/-! ### Going up and towers -/

section Tower

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- Every maximal ideal of `𝓞 K` lies under a maximal ideal of `𝓞 L`. -/
theorem exists_maximal_liesOver (P : Ideal (𝓞 K)) [P.IsMaximal] :
    ∃ Q : Ideal (𝓞 L), Q.IsMaximal ∧ Q.LiesOver P :=
  Ideal.exists_maximal_ideal_liesOver_of_isIntegral P

theorem ramificationIdx_le_of_liesOver (P : Ideal (𝓞 K)) [P.IsPrime] (Q : Ideal (𝓞 L))
    [Q.IsPrime] [Q.LiesOver P] : P.ramificationIdx ℤ ≤ Q.ramificationIdx ℤ := by
  rw [Ideal.ramificationIdx_tower (R := ℤ) P Q]
  exact Nat.le_mul_of_pos_right _ (Ideal.ramificationIdx_pos Q (𝓞 K))

theorem inertiaDeg_le_of_liesOver (P : Ideal (𝓞 K)) [P.IsPrime] (Q : Ideal (𝓞 L))
    [Q.IsPrime] [Q.LiesOver P] : P.inertiaDeg ℤ ≤ Q.inertiaDeg ℤ := by
  rw [Ideal.inertiaDeg_tower (R := ℤ) P Q]
  exact Nat.le_mul_of_pos_right _ (Ideal.inertiaDeg_pos Q (𝓞 K))

end Tower

section Sandwich

variable {M K L : Type*} [Field M] [NumberField M] [Field K] [NumberField K] [Field L]
  [NumberField L] [Algebra M K] [Algebra K L]

/-- **Ramification indices in a sandwich.** -/
theorem ramificationIdx_eq_of_sandwich (p : Ideal ℤ) [p.IsMaximal] (hp : p ≠ ⊥) (e : ℕ)
    (hM : ∀ V : Ideal (𝓞 M), V.IsPrime → V.LiesOver p → V.ramificationIdx ℤ = e)
    (hL : ∀ W : Ideal (𝓞 L), W.IsPrime → W.LiesOver p → W.ramificationIdx ℤ = e)
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver p] : P.ramificationIdx ℤ = e := by
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp P
  have : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
  let V := P.under (𝓞 M)
  have : P.LiesOver V := ⟨rfl⟩
  have : V.LiesOver p := Ideal.LiesOver.tower_bot P V p
  have h1 : e ≤ P.ramificationIdx ℤ := by
    rw [← hM V (Ideal.IsPrime.under (𝓞 M) P) this]
    exact ramificationIdx_le_of_liesOver V P
  obtain ⟨Q, hQ, hQP⟩ := exists_maximal_liesOver (L := L) P
  have : Q.LiesOver p := Ideal.LiesOver.trans Q P p
  have h2 : P.ramificationIdx ℤ ≤ e := by
    rw [← hL Q hQ.isPrime this]
    exact ramificationIdx_le_of_liesOver P Q
  omega

/-- **Residue degrees in a sandwich.** -/
theorem inertiaDeg_eq_of_sandwich (p : Ideal ℤ) [p.IsMaximal] (hp : p ≠ ⊥) (f : ℕ)
    (hM : ∀ V : Ideal (𝓞 M), V.IsPrime → V.LiesOver p → V.inertiaDeg ℤ = f)
    (hL : ∀ W : Ideal (𝓞 L), W.IsPrime → W.LiesOver p → W.inertiaDeg ℤ = f)
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver p] : P.inertiaDeg ℤ = f := by
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp P
  have : P.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
  let V := P.under (𝓞 M)
  have : P.LiesOver V := ⟨rfl⟩
  have : V.LiesOver p := Ideal.LiesOver.tower_bot P V p
  have h1 : f ≤ P.inertiaDeg ℤ := by
    rw [← hM V (Ideal.IsPrime.under (𝓞 M) P) this]
    exact inertiaDeg_le_of_liesOver V P
  obtain ⟨Q, hQ, hQP⟩ := exists_maximal_liesOver (L := L) P
  have : Q.LiesOver p := Ideal.LiesOver.trans Q P p
  have h2 : P.inertiaDeg ℤ ≤ f := by
    rw [← hL Q hQ.isPrime this]
    exact inertiaDeg_le_of_liesOver P Q
  omega

end Sandwich

/-! ### Prime-norm counts from uniform types -/

section Counts

variable (K : Type*) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime)

include hp in
/-- With a common residue degree `f` above `p`, the primes of norm `p^f` are the primes
above `p`. -/
def primeNormFiberEquivPrimesOver' (f : ℕ) (hf : 0 < f)
    (hres : ∀ P : Ideal (𝓞 K), P.IsPrime → P.LiesOver (rationalPrimeIdeal p) →
      P.inertiaDeg ℤ = f) :
    PrimeNormFiber K (p ^ f) ≃ (rationalPrimeIdeal p).primesOver (𝓞 K) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hp0 : rationalPrimeIdeal p ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hpf : 1 < p ^ f := Nat.one_lt_pow hf.ne' hp.one_lt
  have hto : ∀ P : PrimeNormFiber K (p ^ f), P.1.asIdeal.LiesOver (rationalPrimeIdeal p) := by
    intro P
    have h := primeNormFiber_liesOver K hpf P
    simpa only [hp.pow_minFac hf.ne'] using h
  have hinv : ∀ Q : (rationalPrimeIdeal p).primesOver (𝓞 K), Ideal.absNorm Q.1 = p ^ f := by
    intro Q
    letI := Q.2.1
    letI := Q.2.2
    letI : Q.1.IsMaximal := Q.2.1.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot hp0 Q.1)
    rw [Ideal.absNorm_eq_pow_inertiaDeg' Q.1 hp, Ideal.inertiaDeg'_eq_inertiaDeg,
      hres Q.1 Q.2.1 Q.2.2]
  exact {
    toFun := fun P => ⟨P.1.asIdeal, P.1.isPrime, hto P⟩
    invFun := fun Q => ⟨⟨Q.1, Q.2.1, Ideal.ne_bot_of_liesOver_of_ne_bot hp0 Q.1⟩, hinv Q⟩
    left_inv := fun P => by apply Subtype.ext; rfl
    right_inv := fun Q => rfl }

include hp in
/-- **The fundamental identity with uniform types**, as a count of primes of norm `p^f`. -/
theorem primeNormCount_mul_of_uniform (e f : ℕ) (hf : 0 < f)
    (hram : ∀ P : Ideal (𝓞 K), P.IsPrime → P.LiesOver (rationalPrimeIdeal p) →
      P.ramificationIdx ℤ = e)
    (hres : ∀ P : Ideal (𝓞 K), P.IsPrime → P.LiesOver (rationalPrimeIdeal p) →
      P.inertiaDeg ℤ = f) :
    Nat.card (PrimeNormFiber K (p ^ f)) * (e * f) = Module.finrank ℚ K := by
  have : Fact p.Prime := ⟨hp⟩
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (rationalPrimeIdeal p) (𝓞 K)
  rw [RingOfIntegers.rank] at hsum
  have hterm : ∀ q : (rationalPrimeIdeal p).primesOver (𝓞 K),
      q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ = e * f := by
    intro q
    rw [hram q.1 q.2.1 q.2.2, hres q.1 q.2.1 q.2.2]
  rw [Finset.sum_congr rfl (fun q _ => hterm q), Finset.sum_const, smul_eq_mul,
    Finset.card_univ] at hsum
  rw [Nat.card_congr (primeNormFiberEquivPrimesOver' K p hp f hf hres),
    Nat.card_eq_fintype_card]
  exact hsum

end Counts

/-! ### Prime fibers over a number field -/

section Fibers

variable (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]

/-- **The fundamental identity over `F` with uniform types.** -/
theorem primeFiber_card_mul_of_uniform (p : HeightOneSpectrum (𝓞 F)) (e f : ℕ)
    (h : ∀ P : PrimeFiber F K p, P.1.asIdeal.ramificationIdx (𝓞 F) = e ∧
      P.1.asIdeal.inertiaDeg (𝓞 F) = f) :
    Fintype.card (PrimeFiber F K p) * (e * f) = Module.finrank F K := by
  letI : p.asIdeal.IsMaximal := p.isPrime.isMaximal p.ne_bot
  have hterm : ∀ P : PrimeFiber F K p,
      Ideal.ramificationIdx' p.asIdeal P.1.asIdeal * Ideal.inertiaDeg' p.asIdeal P.1.asIdeal =
        e * f := by
    intro P
    letI : P.1.asIdeal.IsPrime := P.1.isPrime
    letI := primeFiber_liesOver F K p P
    letI : P.1.asIdeal.IsMaximal := P.1.isPrime.isMaximal P.1.ne_bot
    rw [Ideal.ramificationIdx'_eq_ramificationIdx p.asIdeal P.1.asIdeal p.ne_bot,
      Ideal.inertiaDeg'_eq_inertiaDeg, (h P).1, (h P).2]
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
  rw [Finset.sum_congr rfl (fun P _ => hterm P), Finset.sum_const, smul_eq_mul,
    Finset.card_univ] at hsum
  exact hsum

end Fibers

/-! ### Norm bounds from a power identity -/

/-- In a finite field where `y^q = y` for every `y`, there are at most `q` elements. -/
theorem card_le_of_forall_pow_eq (E : Type*) [Field E] [Fintype E] (q : ℕ) (hq : 1 < q)
    (h : ∀ y : E, y ^ q = y) : Fintype.card E ≤ q := by
  classical
  have hne := FiniteField.X_pow_card_sub_X_ne_zero E hq
  have hsub : (Finset.univ : Finset E).val ⊆
      (Polynomial.X ^ q - Polynomial.X : Polynomial E).roots := by
    intro y _
    rw [Polynomial.mem_roots hne]
    simp [h y]
  have := Polynomial.card_le_degree_of_subset_roots hsub
  rw [FiniteField.X_pow_card_sub_X_natDegree_eq E hq] at this
  exact this

/-- If `z^q ≡ z (mod P)` for every integer `z` of `K`, then `N P ≤ q`. -/
theorem absNorm_le_of_forall_pow_sub_mem {K : Type*} [Field K] [NumberField K] {p : ℕ}
    [Fact p.Prime] (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (rationalPrimeIdeal p)] (q : ℕ)
    (hq : 1 < q) (h : ∀ z : 𝓞 K, z ^ q - z ∈ P) : Ideal.absNorm P ≤ q := by
  letI := Ideal.Quotient.field P
  let _ : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  have hcard := card_le_of_forall_pow_eq (𝓞 K ⧸ P) q hq (fun y => by
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_pow, Ideal.Quotient.eq]
    exact h z)
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  exact hcard

/-! ### Moving primes -/

/-- A ring automorphism `c` moves a prime `P` if some `w` has `w · c(w) ∈ P` and
`w + c(w) ∉ P`. -/
theorem map_ne_of_mul_add {S : Type*} [CommRing S] (c : S →+* S)
    (hc : Function.Bijective c) (P : Ideal S) [P.IsPrime] (w : S) (hmul : w * c w ∈ P)
    (hadd : w + c w ∉ P) : Ideal.map c P ≠ P := by
  intro h
  have hback : ∀ x, c x ∈ P → x ∈ P := by
    intro x hx
    rw [← h] at hx
    rwa [← Ideal.comap_map_of_bijective c hc (I := P), Ideal.mem_comap]
  rcases Ideal.IsPrime.mem_or_mem inferInstance hmul with hw | hw
  · have hcw : c w ∈ P := by
      rw [← h]
      exact Ideal.mem_map_of_mem c hw
    exact hadd (P.add_mem hw hcw)
  · exact hadd (P.add_mem (hback w hw) hw)

end UnitDistance.NumberFieldAnalysis
