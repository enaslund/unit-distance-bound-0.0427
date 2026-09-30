module

public import UnitDistance.Sqrt241.Genus.Degree
public import Mathlib.FieldTheory.Normal.Closure

@[expose] public section
set_option backward.privateInPublic true


/-!
# The canonical genus field is Galois over ℚ

Every `ℚ`-embedding `σ` of the closure sends `√241` to `±√241`, and a genus
root `√α_i` to a square root of `α_i` or of its conjugate `ᾱ_i`.  The
conjugates have explicit square roots in `E`
(`ᾱ₀ = α₀`, `ᾱ₁ = -1/α₁`, `ᾱ₂ = -α₃`, `ᾱ₃ = -α₂`, `ᾱ₄ = α₅`, `ᾱ₅ = α₄`,
`ᾱ₆ = α₇`, `ᾱ₇ = α₆`), so `σ(E) ≤ E`, and `E` is normal, hence Galois.

For the automorphisms of `E`: `σ(√241) = ±√241`; if `σ` fixes `√241` it
multiplies each genus root by a sign, hence `σ² = 1`; in general `σ⁴ = 1`.
-/

noncomputable section
open IntermediateField

namespace UnitDistance.Sqrt241.Genus

open CanonicalGenus

theorem eq_or_eq_neg_of_sq_eq_sq' {K : Type*} [Field K] {y z : K} (h : y ^ 2 = z ^ 2) :
    y = z ∨ y = -z :=
  sq_eq_sq_iff_eq_or_eq_neg.1 h

/-- Explicit square roots in `E` of the conjugate radicands. -/
def conjRoot : Fin 8 → Closure :=
  ![genusRoot 0, genusRoot 0 * (genusRoot 1)⁻¹, genusRoot 0 * genusRoot 3,
    genusRoot 0 * genusRoot 2, genusRoot 5, genusRoot 4, genusRoot 7, genusRoot 6]

theorem conjRoot_mem (i : Fin 8) : conjRoot i ∈ field := by
  fin_cases i <;> simp only [conjRoot, Fin.isValue] <;>
    first
    | exact genusRoot_mem _
    | exact mul_mem (genusRoot_mem _) (genusRoot_mem _)
    | exact mul_mem (genusRoot_mem _) (inv_mem (genusRoot_mem _))

theorem conjRoot_sq (i : Fin 8) : conjRoot i ^ 2 = conjRadicand i := by
  fin_cases i
  · simp only [conjRoot, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    rw [genusRoot_sq, conjRadicand_zero]
  · simp only [conjRoot, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    have h0 : radicand 0 = -1 := by simp [radicand, radicandA, radicandB]
    rw [mul_pow, inv_pow, genusRoot_sq, genusRoot_sq, h0, eq_comm, ← div_eq_mul_inv,
      eq_div_iff (radicand_ne_zero 1)]
    exact conjRadicand_one
  · simp only [conjRoot]
    simp only [Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
    rw [mul_pow, genusRoot_sq, genusRoot_sq, conjRadicand_two]
    simp [radicand, radicandA, radicandB]
  · simp only [conjRoot]
    simp only [Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
    rw [mul_pow, genusRoot_sq, genusRoot_sq, conjRadicand_three]
    simp [radicand, radicandA, radicandB]
  · simp only [conjRoot]
    simp only [Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
    rw [genusRoot_sq, conjRadicand_four]
  · simp only [conjRoot]
    simp only [Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
    rw [genusRoot_sq, conjRadicand_five]
  · simp only [conjRoot]
    simp only [Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
    rw [genusRoot_sq, conjRadicand_six]
  · simp only [conjRoot]
    simp only [Fin.reduceFinMk, Matrix.cons_val, Fin.isValue]
    rw [genusRoot_sq, conjRadicand_seven]

theorem sigma_baseRoot (σ : Closure →ₐ[ℚ] Closure) :
    σ baseRoot = baseRoot ∨ σ baseRoot = -baseRoot := by
  apply eq_or_eq_neg_of_sq_eq_sq'
  rw [← map_pow, baseRoot_sq, map_ofNat]

theorem sigma_radicand (σ : Closure →ₐ[ℚ] Closure) (i : Fin 8) :
    σ (radicand i) = (radicandA i : Closure) + (radicandB i : Closure) * σ baseRoot := by
  simp [radicand, map_add, map_mul, map_ratCast]

theorem map_field_le (σ : Closure →ₐ[ℚ] Closure) : field.map σ ≤ field := by
  rw [field, adjoin_map, adjoin_le_iff]
  rintro _ ⟨x, hx, rfl⟩
  rcases hx with rfl | ⟨i, rfl⟩
  · rcases sigma_baseRoot σ with h | h <;> rw [h]
    · exact baseRoot_mem
    · exact neg_mem baseRoot_mem
  · have hsq : (σ (genusRoot i)) ^ 2 = σ (radicand i) := by rw [← map_pow, genusRoot_sq]
    rw [sigma_radicand] at hsq
    rcases sigma_baseRoot σ with h | h <;> rw [h] at hsq
    · rw [← radicand, ← genusRoot_sq] at hsq
      rcases eq_or_eq_neg_of_sq_eq_sq' hsq with h' | h' <;> rw [h']
      · exact genusRoot_mem i
      · exact neg_mem (genusRoot_mem i)
    · rw [show (radicandA i : Closure) + (radicandB i : Closure) * -baseRoot = conjRadicand i by
        rw [conjRadicand_eq]; ring, ← conjRoot_sq] at hsq
      rcases eq_or_eq_neg_of_sq_eq_sq' hsq with h' | h' <;> rw [h']
      · exact conjRoot_mem i
      · exact neg_mem (conjRoot_mem i)

instance normal_carrier : Normal ℚ Carrier :=
  normal_iff_forall_map_le.2 map_field_le

instance isGalois_carrier : IsGalois ℚ Carrier where

/-! ### Automorphisms of `E` -/

/-- `√241` as an element of `E`. -/
def bE : Carrier := ⟨baseRoot, baseRoot_mem⟩

/-- The genus roots as elements of `E`. -/
def gE (i : Fin 8) : Carrier := ⟨genusRoot i, genusRoot_mem i⟩

@[simp] theorem coe_bE : (bE : Closure) = baseRoot := rfl
@[simp] theorem coe_gE (i : Fin 8) : (gE i : Closure) = genusRoot i := rfl

theorem bE_sq : bE ^ 2 = 241 := by
  apply Subtype.ext
  simp only [IntermediateField.coe_pow, coe_bE, baseRoot_sq]
  rfl

/-- The radicands as elements of `E`. -/
def radE (i : Fin 8) : Carrier :=
  (radicandA i : Carrier) + (radicandB i : Carrier) * bE

theorem gE_sq (i : Fin 8) : gE i ^ 2 = radE i := by
  apply Subtype.ext
  simp [radE, genusRoot_sq, radicand]

theorem gE_ne_zero (i : Fin 8) : gE i ≠ 0 := by
  intro h
  apply genusRoot_ne_zero i
  have := congrArg Subtype.val h
  simpa using this

theorem bE_ne_zero : bE ≠ 0 := by
  intro h
  apply baseRoot_ne_zero
  have := congrArg Subtype.val h
  simpa using this

theorem aut_bE (σ : Carrier ≃ₐ[ℚ] Carrier) : σ bE = bE ∨ σ bE = -bE := by
  apply eq_or_eq_neg_of_sq_eq_sq'
  rw [← map_pow, bE_sq, map_ofNat]

theorem aut_radE (σ : Carrier ≃ₐ[ℚ] Carrier) (hσ : σ bE = bE) (i : Fin 8) :
    σ (radE i) = radE i := by
  simp [radE, map_add, map_mul, map_ratCast, hσ]

theorem aut_gE (σ : Carrier ≃ₐ[ℚ] Carrier) (hσ : σ bE = bE) (i : Fin 8) :
    σ (gE i) = gE i ∨ σ (gE i) = -gE i := by
  apply eq_or_eq_neg_of_sq_eq_sq'
  rw [← map_pow, gE_sq, aut_radE σ hσ]

/-- An automorphism of `E` is determined by its values on the generators. -/
theorem aut_ext {σ τ : Carrier ≃ₐ[ℚ] Carrier} (hb : σ bE = τ bE)
    (hg : ∀ i, σ (gE i) = τ (gE i)) : σ = τ := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply IntermediateField.algHom_ext_of_eq_adjoin ℚ (S := field)
    (s := insert baseRoot (Set.range genusRoot)) rfl
  intro x hx
  rcases hx with rfl | ⟨i, rfl⟩
  · exact hb
  · exact hg i

theorem aut_sq_eq_one (σ : Carrier ≃ₐ[ℚ] Carrier) (hσ : σ bE = bE) : σ * σ = 1 := by
  apply aut_ext
  · simp [AlgEquiv.mul_apply, hσ]
  · intro i
    rcases aut_gE σ hσ i with h | h
    · simp [AlgEquiv.mul_apply, h]
    · simp [AlgEquiv.mul_apply, h, map_neg]

theorem aut_sq_bE (σ : Carrier ≃ₐ[ℚ] Carrier) : (σ * σ) bE = bE := by
  rcases aut_bE σ with h | h
  · simp [AlgEquiv.mul_apply, h]
  · simp [AlgEquiv.mul_apply, h, map_neg]

theorem aut_pow_four (σ : Carrier ≃ₐ[ℚ] Carrier) : σ ^ 4 = 1 := by
  have h := aut_sq_eq_one (σ * σ) (aut_sq_bE σ)
  rw [show σ ^ 4 = σ ^ 2 * σ ^ 2 by rw [← pow_add], pow_two, h]

/-- Some automorphism moves `√241`. -/
theorem exists_aut_neg_bE : ∃ σ : Carrier ≃ₐ[ℚ] Carrier, σ bE = -bE := by
  by_contra h
  simp only [not_exists] at h
  have hfix : bE ∈ fixedField (⊤ : Subgroup (Carrier ≃ₐ[ℚ] Carrier)) := by
    rintro ⟨σ, -⟩
    rcases aut_bE σ with h' | h'
    · exact h'
    · exact absurd h' (h σ)
  rw [IsGalois.fixedField_top, IntermediateField.mem_bot] at hfix
  obtain ⟨q, hq⟩ := hfix
  apply not_isSquare_241
  refine ⟨q, ?_⟩
  apply (algebraMap ℚ Carrier).injective
  rw [map_mul, ← sq, hq, bE_sq]
  simp

end UnitDistance.Sqrt241.Genus
