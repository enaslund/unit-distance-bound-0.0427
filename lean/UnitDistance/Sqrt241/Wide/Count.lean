module

public import UnitDistance.Sqrt241.Analytic.WideTypes
public import UnitDistance.Sqrt241.Wide.Degree

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Counting primes of `E_W` above a prime of `B`

Generic tools for `WideLocalTypes`:

* `finrank_le_card_mul`: if every prime of `K` above a prime `𝔮` of `F` has `e f ≤ c`, the fibre
  has at least `[K : F] / c` elements (fundamental identity);
* `absNorm_le_of_pow_sub_mem`: a prime whose residues all satisfy `y^n = y` has norm `≤ n`;
* `contribLowerBound_of_towerClasses`: the primes of `K` above distinct primes `𝔮_i` of an
  intermediate field `F` give disjoint classes for `contribLowerBound_of_classes`.

Then the tower `ℚ ⊂ B ⊂ E_W ⊂ M`: `B ≤ E_W` as subfields of the closure, `E_W → M` by
`wideToM`, and `[E_W : B] = 4096`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Wide

open NumberField IsDedekindDomain UnitDistance.NumberFieldAnalysis UnitDistance.Sqrt241.Analytic
open Polynomial

section Count

variable (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]

set_option linter.deprecated false in
/-- **Fibre count.** If every prime of `K` above `𝔮` has `e f ≤ c`, then `[K : F] ≤ c · #fibre`. -/
theorem finrank_le_card_mul (𝔮 : HeightOneSpectrum (𝓞 F)) (c : ℕ)
    (h : ∀ P : PrimeFiber F K 𝔮,
      P.1.asIdeal.ramificationIdx (𝓞 F) * P.1.asIdeal.inertiaDeg (𝓞 F) ≤ c) :
    Module.finrank F K ≤ Fintype.card (PrimeFiber F K 𝔮) * c := by
  letI : 𝔮.asIdeal.IsMaximal := 𝔮.isPrime.isMaximal 𝔮.ne_bot
  letI : Module.IsTorsionFree (𝓞 F) (𝓞 K) := inferInstance
  have hsum : (∑ P : PrimeFiber F K 𝔮,
      Ideal.ramificationIdx' 𝔮.asIdeal P.1.asIdeal * Ideal.inertiaDeg' 𝔮.asIdeal P.1.asIdeal) =
      Module.finrank F K := by
    calc
      _ = ∑ Q : ↥(IsDedekindDomain.primesOverFinset 𝔮.asIdeal (𝓞 K)),
          Ideal.ramificationIdx' 𝔮.asIdeal Q.1 * Ideal.inertiaDeg' 𝔮.asIdeal Q.1 :=
        Fintype.sum_equiv (primeFiberEquiv F K 𝔮) _ _ (fun _ => rfl)
      _ = ∑ Q ∈ IsDedekindDomain.primesOverFinset 𝔮.asIdeal (𝓞 K),
          Ideal.ramificationIdx' 𝔮.asIdeal Q * Ideal.inertiaDeg' 𝔮.asIdeal Q :=
        Finset.sum_coe_sort _ (fun Q : Ideal (𝓞 K) =>
          Ideal.ramificationIdx' 𝔮.asIdeal Q * Ideal.inertiaDeg' 𝔮.asIdeal Q)
      _ = Module.finrank F K := Ideal.sum_ramification_inertia (𝓞 K) F K 𝔮.ne_bot
  rw [← hsum]
  calc _ ≤ ∑ _P : PrimeFiber F K 𝔮, c := Finset.sum_le_sum fun P _ => by
        letI := primeFiber_liesOver F K 𝔮 P
        letI := P.1.isPrime
        letI : P.1.asIdeal.IsMaximal := P.1.isPrime.isMaximal P.1.ne_bot
        rw [Ideal.ramificationIdx'_eq_ramificationIdx 𝔮.asIdeal P.1.asIdeal 𝔮.ne_bot,
          Ideal.inertiaDeg'_eq_inertiaDeg]
        exact h P
    _ = _ := by simp [mul_comm]

omit [NumberField F] [Algebra F K] in
/-- **Residue bound.** If `x^n - x ∈ P` for all integers `x`, then `N(P) ≤ n`. -/
theorem absNorm_le_of_pow_sub_mem (P : Ideal (𝓞 K)) [P.IsMaximal] (n : ℕ) (hn : 1 < n)
    (h : ∀ x : 𝓞 K, x ^ n - x ∈ P) : Ideal.absNorm P ≤ n := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rcases finite_or_infinite (𝓞 K ⧸ P) with hfin | hinf
  · letI := Ideal.Quotient.field P
    letI := Fintype.ofFinite (𝓞 K ⧸ P)
    rw [Nat.card_eq_fintype_card]
    have hroots : (Finset.univ : Finset (𝓞 K ⧸ P)).val ⊆
        ((X ^ n - X : (𝓞 K ⧸ P)[X])).roots := by
      intro y _
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [Polynomial.mem_roots (FiniteField.X_pow_card_sub_X_ne_zero _ hn), Polynomial.IsRoot,
        Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, ← map_pow, ← map_sub,
        Ideal.Quotient.eq_zero_iff_mem]
      exact h x
    have hc := Polynomial.card_le_degree_of_subset_roots hroots
    rwa [FiniteField.X_pow_card_sub_X_natDegree_eq _ hn] at hc
  · rw [Nat.card_eq_zero_of_infinite]
    exact Nat.zero_le _

variable [IsScalarTower ℚ F K]

/-- The primes of `K` above a prime `𝔮` of `F` above `p`, as primes of `K` above `p`. -/
def towerClass (p : Nat.Primes) (𝔮 : PrimeFiber ℚ F (rationalPrimePlace p)) :
    Finset (PrimeFiber ℚ K (rationalPrimePlace p)) :=
  Finset.univ.map ⟨fun P => rationalPrimeTowerFiberEquiv F K p ⟨𝔮, P⟩, fun P P' h =>
    eq_of_heq (Sigma.mk.inj_iff.mp ((rationalPrimeTowerFiberEquiv F K p).injective h)).2⟩

theorem card_towerClass (p : Nat.Primes) (𝔮 : PrimeFiber ℚ F (rationalPrimePlace p)) :
    (towerClass F K p 𝔮).card = Fintype.card (PrimeFiber F K 𝔮.1) := by
  simp [towerClass]

theorem mem_towerClass (p : Nat.Primes) (𝔮 : PrimeFiber ℚ F (rationalPrimePlace p))
    (Q : PrimeFiber ℚ K (rationalPrimePlace p)) (hQ : Q ∈ towerClass F K p 𝔮) :
    ∃ P : PrimeFiber F K 𝔮.1, Q.1 = P.1 := by
  simp only [towerClass, Finset.mem_map, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk] at hQ
  obtain ⟨P, rfl⟩ := hQ
  exact ⟨P, rfl⟩

theorem disjoint_towerClass (p : Nat.Primes) (𝔮 𝔮' : PrimeFiber ℚ F (rationalPrimePlace p))
    (h : 𝔮 ≠ 𝔮') : Disjoint (towerClass F K p 𝔮) (towerClass F K p 𝔮') := by
  rw [Finset.disjoint_left]
  intro Q hQ hQ'
  simp only [towerClass, Finset.mem_map, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk] at hQ hQ'
  obtain ⟨P, rfl⟩ := hQ
  obtain ⟨P', hP'⟩ := hQ'
  exact h (Sigma.mk.inj_iff.mp ((rationalPrimeTowerFiberEquiv F K p).injective hP')).1.symm

/-- **Classes from an intermediate field.** -/
theorem contribLowerBound_of_towerClasses (p : Nat.Primes) {ι : Type*} (I : List ι)
    (q : ι → PrimeFiber ℚ F (rationalPrimePlace p)) (w : ι → ℚ) (f : ι → ℕ)
    (hI : I.Nodup) (hq : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → q i ≠ q j) (hf : ∀ i ∈ I, 0 < f i)
    (hnorm : ∀ i ∈ I, ∀ P : PrimeFiber F K (q i).1, Ideal.absNorm P.1.asIdeal ≤ p.val ^ f i)
    (hcard : ∀ i ∈ I, ((w i : ℚ) : ℝ) * (Module.finrank ℚ K : ℝ) ≤
      Fintype.card (PrimeFiber F K (q i).1)) :
    ContribLowerBound K p (I.map fun i => (w i, f i)) := by
  apply contribLowerBound_of_classes K p I (fun i => towerClass F K p (q i)) w f hI
  · intro i hi j hj hij
    exact disjoint_towerClass F K p _ _ (hq i hi j hj hij)
  · exact hf
  · intro i hi Q hQ
    obtain ⟨P, hP⟩ := mem_towerClass F K p (q i) Q hQ
    rw [hP]
    exact hnorm i hi P
  · intro i hi
    rw [card_towerClass]
    exact hcard i hi

end Count

/-- Two equal-degree classes merge. -/
theorem ContribLowerBound.merge {L : Type*} [Field L] [NumberField L] {p : Nat.Primes}
    {w w' : ℚ} {f : ℕ} (h : ContribLowerBound L p [(w, f), (w', f)]) :
    ContribLowerBound L p [(w + w', f)] := by
  intro φ hφ
  have := h φ hφ
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] at this ⊢
  push_cast
  linarith

/-! ### The tower `ℚ ⊂ B ⊂ E_W ⊂ M` -/

open CanonicalGenus CanonicalWide Base

theorem B_le_field : (B : IntermediateField ℚ Closure) ≤ CanonicalWide.field := by
  rw [IntermediateField.adjoin_simple_le_iff]
  exact IntermediateField.subset_adjoin ℚ _ (Set.mem_insert _ _)

instance algebraBCarrier : Algebra B CanonicalWide.Carrier :=
  (IntermediateField.inclusion B_le_field).toRingHom.toAlgebra

instance : IsScalarTower ℚ B CanonicalWide.Carrier :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

@[simp] theorem coe_algebraMap_BCarrier (x : B) :
    ((algebraMap B CanonicalWide.Carrier x : CanonicalWide.Carrier) : Closure) = (x : Closure) :=
  IntermediateField.coe_inclusion B_le_field x

theorem finrank_B_Carrier : Module.finrank B CanonicalWide.Carrier = 4096 := by
  have h := Module.finrank_mul_finrank ℚ B CanonicalWide.Carrier
  rw [finrank_field, Base.finrank_eq_two] at h
  omega

end UnitDistance.Sqrt241.Wide
