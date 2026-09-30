module

public import UnitDistance.GaloisPrimeNormCounts
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.FieldTheory.Finite.GaloisField

@[expose] public section
set_option backward.privateInPublic true


/-!
# Local indices of a Galois number field from its decomposition groups

For a number field `K`, Galois over ℚ, a rational prime `p` and a prime `P`
of `𝓞 K` above `p`:

* if every element `σ` of the decomposition group (the stabilizer of `P`)
  satisfies `σⁿ = 1`, then the residue degree `f` divides `n`: the Frobenius
  of the residue extension has order `f` and lifts to the stabilizer
  (`Ideal.Quotient.stabilizerHom_surjective`);
* if the inertia group is trivial, then `e = 1`
  (`Ideal.card_inertia_eq_ramificationIdxIn`);
* `e f` is the order of the stabilizer (`Ideal.card_stabilizer_eq`).
-/

noncomputable section
open NumberField
open scoped Pointwise

namespace UnitDistance.Sqrt241.Genus

open UnitDistance.NumberFieldAnalysis

variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]

omit [IsGalois ℚ K] in
theorem exists_prime_liesOver (p : ℕ) [Fact p.Prime] :
    ∃ P : Ideal (𝓞 K), P.IsPrime ∧ P.LiesOver (rationalPrimeIdeal p) := by
  obtain ⟨⟨P, hP1, hP2⟩⟩ := (inferInstance : Nonempty ((rationalPrimeIdeal p).primesOver (𝓞 K)))
  exact ⟨P, hP1, hP2⟩

variable {K}

omit [NumberField K] [IsGalois ℚ K] in
theorem intCast_mem_iff {p : ℕ} (P : Ideal (𝓞 K)) [P.LiesOver (rationalPrimeIdeal p)] (n : ℤ) :
    (n : 𝓞 K) ∈ P ↔ (p : ℤ) ∣ n := by
  have h : (algebraMap ℤ (𝓞 K) n ∈ P) ↔ n ∈ P.under ℤ := Iff.rfl
  rw [eq_intCast] at h
  rw [h, ← Ideal.over_def P (rationalPrimeIdeal p), rationalPrimeIdeal, Ideal.mem_span_singleton]

omit [NumberField K] [IsGalois ℚ K] in
theorem isMaximal_of_liesOver {p : ℕ} [Fact p.Prime] (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (rationalPrimeIdeal p)] : P.IsMaximal :=
  Ideal.IsMaximal.of_liesOver_isMaximal P (rationalPrimeIdeal p)

attribute [local instance] Ideal.Quotient.field in
/-- Frobenius lifting: the residue degree divides every common exponent of
the decomposition group. -/
theorem inertiaDegIn_dvd_of_stab_pow {p : ℕ} [hp : Fact p.Prime] (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (rationalPrimeIdeal p)] (n : ℕ)
    (h : ∀ σ ∈ MulAction.stabilizer Gal(K/ℚ) P, σ ^ n = 1) :
    (rationalPrimeIdeal p).inertiaDegIn (𝓞 K) ∣ n := by
  have := isMaximal_of_liesOver P (p := p)
  rw [Ideal.inertiaDegIn_eq_inertiaDeg (rationalPrimeIdeal p) P Gal(K/ℚ),
    Ideal.inertiaDeg_eq_of_isMaximal (rationalPrimeIdeal p) P]
  let _ : Fintype (ℤ ⧸ rationalPrimeIdeal p) := Fintype.ofFinite _
  rw [← FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (ℤ ⧸ rationalPrimeIdeal p) (𝓞 K ⧸ P)]
  obtain ⟨σ, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective Gal(K/ℚ) (rationalPrimeIdeal p) P
    (FiniteField.frobeniusAlgEquivOfAlgebraic (ℤ ⧸ rationalPrimeIdeal p) (𝓞 K ⧸ P))
  apply orderOf_dvd_of_pow_eq_one
  rw [← hσ, ← map_pow]
  have hσn : σ ^ n = 1 := Subtype.ext (by simpa using h σ.1 σ.2)
  rw [hσn, map_one]

/-- Trivial inertia means `e = 1`. -/
theorem ramificationIdxIn_eq_one_of_inertia {p : ℕ} [hp : Fact p.Prime] (P : Ideal (𝓞 K))
    [P.IsPrime] [P.LiesOver (rationalPrimeIdeal p)]
    (h : ∀ σ ∈ P.inertia Gal(K/ℚ), σ = 1) :
    (rationalPrimeIdeal p).ramificationIdxIn (𝓞 K) = 1 := by
  rw [← Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(K/ℚ)) (rationalPrimeIdeal p) P]
  have hbot : P.inertia Gal(K/ℚ) = ⊥ := (Subgroup.eq_bot_iff_forall _).2 h
  rw [hbot, Subgroup.card_bot]

/-- The order of the decomposition group is `e f`. -/
theorem ramificationIdxIn_mul_inertiaDegIn_le {p : ℕ} [hp : Fact p.Prime] (P : Ideal (𝓞 K))
    [P.IsPrime] [P.LiesOver (rationalPrimeIdeal p)] (N : ℕ)
    (h : Nat.card (MulAction.stabilizer Gal(K/ℚ) P) ≤ N) :
    (rationalPrimeIdeal p).ramificationIdxIn (𝓞 K) *
      (rationalPrimeIdeal p).inertiaDegIn (𝓞 K) ≤ N := by
  rw [← Ideal.card_stabilizer_eq (G := Gal(K/ℚ)) (rationalPrimeIdeal p) P]
  exact h

attribute [local instance] Ideal.Quotient.field in
/-- Fermat in the residue field `𝔽_{p^f}`: `x^(p^(f k)) ≡ x (mod P)`. -/
theorem pow_prime_pow_sub_mem {p : ℕ} [hp : Fact p.Prime] (P : Ideal (𝓞 K)) [P.IsPrime]
    [P.LiesOver (rationalPrimeIdeal p)] (x : 𝓞 K) (k : ℕ) :
    x ^ (p ^ ((rationalPrimeIdeal p).inertiaDegIn (𝓞 K) * k)) - x ∈ P := by
  have := isMaximal_of_liesOver P (p := p)
  let _ : Fintype (𝓞 K ⧸ P) := Fintype.ofFinite _
  have hcard : Fintype.card (𝓞 K ⧸ P) = p ^ (rationalPrimeIdeal p).inertiaDegIn (𝓞 K) := by
    rw [Fintype.card_eq_nat_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
      ← Ideal.pow_inertiaDeg p P,
      ← Ideal.inertiaDegIn_eq_inertiaDeg (rationalPrimeIdeal p) P Gal(K/ℚ)]
  have key : ∀ k : ℕ, (Ideal.Quotient.mk P x) ^
      (p ^ ((rationalPrimeIdeal p).inertiaDegIn (𝓞 K) * k)) = Ideal.Quotient.mk P x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, pow_add, pow_mul, ih, ← hcard, FiniteField.pow_card]
  rw [← Ideal.Quotient.eq, map_pow, key k]

/-- `n ≤ e` as soon as `p ∈ Pⁿ`. -/
theorem le_ramificationIdxIn_of_mem_pow {p : ℕ} [hp : Fact p.Prime] (P : Ideal (𝓞 K))
    [P.IsPrime] [P.LiesOver (rationalPrimeIdeal p)] (n : ℕ) (h : (p : 𝓞 K) ∈ P ^ n) :
    n ≤ (rationalPrimeIdeal p).ramificationIdxIn (𝓞 K) := by
  have hne : rationalPrimeIdeal p ≠ ⊥ := by
    rw [rationalPrimeIdeal, ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.out.ne_zero
  have hpos := Ideal.ramificationIdxIn_ne_zero Gal(K/ℚ) (p := rationalPrimeIdeal p) (B := 𝓞 K)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (rationalPrimeIdeal p) P Gal(K/ℚ),
    ← Ideal.ramificationIdx'_eq_ramificationIdx (rationalPrimeIdeal p) P hne] at hpos ⊢
  unfold Ideal.ramificationIdx' at hpos ⊢
  have hmem : n ∈ {m : ℕ | Ideal.map (algebraMap ℤ (𝓞 K)) (rationalPrimeIdeal p) ≤ P ^ m} := by
    change Ideal.map (algebraMap ℤ (𝓞 K)) (rationalPrimeIdeal p) ≤ P ^ n
    rw [rationalPrimeIdeal, Ideal.map_span, Set.image_singleton, Ideal.span_le,
      Set.singleton_subset_iff]
    simpa using h
  have hbdd : BddAbove {m : ℕ | Ideal.map (algebraMap ℤ (𝓞 K)) (rationalPrimeIdeal p) ≤ P ^ m} := by
    by_contra hb
    exact hpos (Nat.sSup_of_not_bddAbove hb)
  exact le_csSup hbdd hmem

end UnitDistance.Sqrt241.Genus
