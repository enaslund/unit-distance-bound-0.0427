module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section
set_option backward.privateInPublic true


/-!
# One quadratic Kummer step inside a fixed field

For an intermediate field `K` of `Ω/ℚ` and `r ∈ Ω` with `r² ∈ K` not a
square in `K`:

* every element of `K ⊔ ℚ⟮r⟯` is `u + v r` with `u, v ∈ K`;
* `[K ⊔ ℚ⟮r⟯ : ℚ] = 2 [K : ℚ]`;
* an element of `K` that is a square in `K ⊔ ℚ⟮r⟯` is a square in `K` or
  becomes one after multiplication by `r²`.

These are the steps of the multiquadratic degree count of the genus field.
-/

noncomputable section
open IntermediateField Polynomial

namespace UnitDistance.Sqrt241.Genus

variable {Ω : Type*} [Field Ω] [Algebra ℚ Ω]

theorem charZero_of_ratAlgebra : CharZero Ω :=
  charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective

theorem isAlgebraic_of_sq_mem {K : IntermediateField ℚ Ω} {r : Ω} (hr : r ^ 2 ∈ K) :
    IsAlgebraic K r := by
  refine ⟨X ^ 2 - C (⟨r ^ 2, hr⟩ : K), ?_, ?_⟩
  · exact X_pow_sub_C_ne_zero (by norm_num) _
  · simp [aeval_def, eval₂_sub, eval₂_X_pow, eval₂_C]

/-- Elements of `K ⊔ ℚ⟮r⟯` are `u + v r` with `u, v ∈ K`. -/
theorem exists_eq_add_mul_of_mem_sup {K : IntermediateField ℚ Ω} {r : Ω} (hr : r ^ 2 ∈ K)
    {z : Ω} (hz : z ∈ K ⊔ ℚ⟮r⟯) : ∃ u ∈ K, ∃ v ∈ K, z = u + v * r := by
  rw [← restrictScalars_adjoin_eq_sup] at hz
  have hz' : z ∈ (K⟮r⟯).toSubalgebra := hz
  rw [adjoin_simple_toSubalgebra_of_isAlgebraic (isAlgebraic_of_sq_mem hr)] at hz'
  clear hz
  induction hz' using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨0, K.zero_mem, 1, K.one_mem, by ring⟩
  | algebraMap k =>
    exact ⟨k, k.2, 0, K.zero_mem, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, hu, v, hv, rfl⟩ := hx
    obtain ⟨u', hu', v', hv', rfl⟩ := hy
    exact ⟨u + u', K.add_mem hu hu', v + v', K.add_mem hv hv', by ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u, hu, v, hv, rfl⟩ := hx
    obtain ⟨u', hu', v', hv', rfl⟩ := hy
    refine ⟨u * u' + v * v' * r ^ 2, K.add_mem (K.mul_mem hu hu')
      (K.mul_mem (K.mul_mem hv hv') hr), u * v' + v * u',
      K.add_mem (K.mul_mem hu hv') (K.mul_mem hv hu'), by ring⟩

theorem minpoly_eq_of_not_sq {K : IntermediateField ℚ Ω} {r : Ω} (hr : r ^ 2 ∈ K)
    (hns : ∀ y ∈ K, y ^ 2 ≠ r ^ 2) :
    minpoly K r = X ^ 2 - C (⟨r ^ 2, hr⟩ : K) := by
  symm
  apply minpoly.eq_of_irreducible_of_monic
  · apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
    intro b hb
    apply hns b.1 b.2
    have := congrArg Subtype.val hb
    simpa using this
  · simp [aeval_def, eval₂_sub, eval₂_X_pow, eval₂_C]
  · exact monic_X_pow_sub_C _ (by norm_num)

/-- The quadratic step doubles the absolute degree. -/
theorem finrank_sup_sqrt {K : IntermediateField ℚ Ω} {r : Ω} (hr : r ^ 2 ∈ K)
    (hns : ∀ y ∈ K, y ^ 2 ≠ r ^ 2) :
    Module.finrank ℚ ↥(K ⊔ ℚ⟮r⟯) = 2 * Module.finrank ℚ K := by
  rw [← restrictScalars_adjoin_eq_sup]
  change Module.finrank ℚ ↥(K⟮r⟯) = _
  rw [← Module.finrank_mul_finrank ℚ K (K⟮r⟯)]
  have hint : IsIntegral K r := (isAlgebraic_of_sq_mem hr).isIntegral
  rw [adjoin.finrank hint, minpoly_eq_of_not_sq hr hns]
  rw [natDegree_X_pow_sub_C]
  ring

/-- Squares of `K` in `K ⊔ ℚ⟮r⟯`. -/
theorem sq_of_mem_sup_sqrt {K : IntermediateField ℚ Ω} {r : Ω} (hr : r ^ 2 ∈ K)
    (hns : ∀ y ∈ K, y ^ 2 ≠ r ^ 2) {x : Ω} (hx : x ∈ K) {y : Ω} (hy : y ∈ K ⊔ ℚ⟮r⟯)
    (hyx : y ^ 2 = x) :
    (∃ w ∈ K, w ^ 2 = x) ∨ (∃ w ∈ K, w ^ 2 = x * r ^ 2) := by
  obtain ⟨u, hu, v, hv, rfl⟩ := exists_eq_add_mul_of_mem_sup hr hy
  by_cases huv : u * v = 0
  · rcases mul_eq_zero.1 huv with h | h
    · subst h
      right
      refine ⟨v * r ^ 2, K.mul_mem hv hr, ?_⟩
      rw [← hyx]
      ring
    · subst h
      left
      exact ⟨u, hu, by rw [← hyx]; ring⟩
  · exfalso
    have := charZero_of_ratAlgebra (Ω := Ω)
    have hrK : r ∈ K := by
      have h2 : (2 : Ω) * (u * v) ≠ 0 := by
        have : (2 : Ω) ≠ 0 := two_ne_zero
        exact mul_ne_zero this huv
      have hrexp : r = (x - u ^ 2 - v ^ 2 * r ^ 2) / (2 * (u * v)) := by
        rw [eq_div_iff h2, ← hyx]
        ring
      rw [hrexp]
      refine K.div_mem (K.sub_mem (K.sub_mem hx (pow_mem hu 2))
        (K.mul_mem (pow_mem hv 2) hr)) (K.mul_mem ?_ (K.mul_mem hu hv))
      simp
    exact hns r hrK rfl

end UnitDistance.Sqrt241.Genus
