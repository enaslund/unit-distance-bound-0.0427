module

public import UnitDistance.NormExtensionCatalog

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual squareclass arithmetic for catalog words

Bitwise word addition is justified by an explicit field product identity:
the common catalog factors contribute an actual square.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.CatalogWordSquareclasses
variable {E : Type*} [Field E]

/-- The actual product selected by a raw catalog word. -/
def wordValue (a : Fin 17 → E) (m : ℕ) : E :=
  ∏ i : Fin 17, if m.testBit i.val then a i else 1

theorem wordValue_ne_zero (a : Fin 17 → E) (ha : ∀ i, a i ≠ 0) (m : ℕ) :
    wordValue a m ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  split
  · exact ha i
  · exact one_ne_zero

/-- Symmetric difference of words differs from their field product by
the square of the actual product of common factors. -/
theorem wordValue_mul (a : Fin 17 → E) (m n : ℕ) :
    wordValue a m*wordValue a n =
      wordValue a (m ^^^ n)*(wordValue a (m &&& n))^2 := by
  unfold wordValue
  rw [← Finset.prod_pow,← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Nat.testBit_xor,Nat.testBit_and]
  cases hm : m.testBit i.val <;> cases hn : n.testBit i.val <;> simp [hm,hn,pow_two]

/-- Actual squares are closed under bitwise addition of catalog words. -/
theorem isSquare_word_xor (a : Fin 17 → E) (ha : ∀ i, a i ≠ 0) (m n : ℕ)
    (hm : IsSquare (wordValue a m)) (hn : IsSquare (wordValue a n)) :
    IsSquare (wordValue a (m ^^^ n)) := by
  have hsq := (hm.mul hn).div (IsSquare.sq (wordValue a (m &&& n)))
  rw [wordValue_mul,mul_div_cancel_right₀ _ (pow_ne_zero _ (wordValue_ne_zero a ha _))] at hsq
  exact hsq

@[simp] theorem wordValue_zero (a : Fin 17 → E) : wordValue a 0 = 1 := by
  simp [wordValue]

/-- The catalog word 26 selects precisely entries 1, 3, and 4. -/
theorem wordValue_26 (a : Fin 17 → E) : wordValue a 26 = a 1*a 3*a 4 := by
  have hs : (Finset.univ.filter fun i : Fin 17 => (26 : ℕ).testBit i.val) = {1,3,4} := by
    decide +kernel
  unfold wordValue
  rw [← Finset.prod_filter,hs]
  simp
  ring

/-- The repeated quadratic radicand in those three catalog rows supplies
an explicit squareclass relation. -/
theorem triple_norm_identity (x : E) (hx : x^2 = -55) :
    (6+x)*(1+x)*(7+x) = -728 := by
  linear_combination (x+14)*hx

/-- Finite binary combinations preserve actual squares, by the explicit
product identity rather than an assumed squareclass model. -/
theorem isSquare_word_fold (a : Fin 17 → E) (ha : ∀ i, a i ≠ 0) (ms : List ℕ)
    (hms : ∀ m ∈ ms, IsSquare (wordValue a m)) :
    IsSquare (wordValue a (ms.foldr (· ^^^ ·) 0)) := by
  induction ms with
  | nil => simp
  | cons m ms ih =>
    exact isSquare_word_xor a ha m (ms.foldr (· ^^^ ·) 0)
      (hms m (by simp)) (ih fun n hn => hms n (by simp [hn]))

end UnitDistance.CatalogWordSquareclasses
