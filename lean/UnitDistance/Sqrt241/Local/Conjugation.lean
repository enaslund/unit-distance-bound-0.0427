module

public import UnitDistance.Sqrt241.Genus.Galois
public import UnitDistance.QuadraticSignLift

@[expose] public section
set_option backward.privateInPublic true

/-!
# Genus labels of automorphisms of the closure, and conjugation by a lift of `σ`

An automorphism `g` of `Closure = AlgebraicClosure ℚ` *has label* `v : Fin 8 → ZMod 2`
when it multiplies every genus root `√α_k` by `binarySign (v k)` (`1 ↦ -1`).
Labels add under composition (`HasLabel.mul`) and are unique (`HasLabel.unique`).

If `s` moves `√241` (so `s|_B = σ`), then `s⁻¹(√α_k)` is `±` the explicit square
root `conjRoot k` of `σ(α_k)` (`Genus/Galois.lean`), and `conjRoot k` is a
product of genus roots; hence `s g s⁻¹` has label `sigmaMatrix v`, where
`sigmaMatrix v = (v₀, v₀+v₁, v₀+v₃, v₀+v₂, v₅, v₄, v₇, v₆)` (`hasLabel_conj`).
This is the rule that turns first-prime data into second-prime data;
`sigmaMatrix` is an involution.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Local

open CanonicalGenus Genus Multiquadratic

/-- `g` multiplies the genus root `√α_k` by the sign `binarySign (v k)`, for every `k`. -/
def HasLabel (g : Closure ≃ₐ[ℚ] Closure) (v : Fin 8 → ZMod 2) : Prop :=
  ∀ k, g (genusRoot k) = binarySign (v k) * genusRoot k

theorem hasLabel_one : HasLabel 1 0 := by
  intro k
  simp

theorem HasLabel.mul {g h : Closure ≃ₐ[ℚ] Closure} {v w : Fin 8 → ZMod 2}
    (hg : HasLabel g v) (hh : HasLabel h w) : HasLabel (g * h) (v + w) := by
  intro k
  rw [AlgEquiv.mul_apply, hh k, map_mul, hg k, Pi.add_apply, binarySign_add]
  simp only [binarySign, map_intCast]
  ring

theorem HasLabel.unique {g : Closure ≃ₐ[ℚ] Closure} {v w : Fin 8 → ZMod 2}
    (hv : HasLabel g v) (hw : HasLabel g w) : v = w := by
  funext k
  apply binarySign_injective (E := Closure)
  exact mul_right_cancel₀ (genusRoot_ne_zero k) ((hv k).symm.trans (hw k))

theorem HasLabel.inv {g : Closure ≃ₐ[ℚ] Closure} {v : Fin 8 → ZMod 2}
    (hg : HasLabel g v) : HasLabel g⁻¹ v := by
  intro k
  have h := hg k
  apply g.injective
  rw [show g (g⁻¹ (genusRoot k)) = genusRoot k from g.apply_symm_apply _, map_mul, h]
  have hs : g (binarySign (E := Closure) (v k)) = binarySign (v k) := by
    simp only [binarySign, map_intCast]
  rw [hs, ← mul_assoc, ← sq, binarySign_sq, one_mul]

theorem HasLabel.pow {g : Closure ≃ₐ[ℚ] Closure} {v : Fin 8 → ZMod 2}
    (hg : HasLabel g v) (n : ℕ) : HasLabel (g ^ n) (n • v) := by
  induction n with
  | zero => simpa using hasLabel_one
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact ih.mul hg

/-- The transposed action of `σ` on genus vectors. -/
def sigmaMatrix (v : Fin 8 → ZMod 2) : Fin 8 → ZMod 2 :=
  ![v 0, v 0 + v 1, v 0 + v 3, v 0 + v 2, v 5, v 4, v 7, v 6]

theorem sigmaMatrix_sigmaMatrix (v : Fin 8 → ZMod 2) : sigmaMatrix (sigmaMatrix v) = v := by
  have h : ∀ a b : ZMod 2, a + (a + b) = b := by decide
  funext k
  fin_cases k <;> simp [sigmaMatrix] <;> exact h _ _

theorem sigmaMatrix_add (v w : Fin 8 → ZMod 2) :
    sigmaMatrix (v + w) = sigmaMatrix v + sigmaMatrix w := by
  funext k
  fin_cases k <;> simp [sigmaMatrix] <;> ring

/-- A genus-labelled automorphism acts on the explicit conjugate roots by `sigmaMatrix`. -/
theorem HasLabel.conjRoot {g : Closure ≃ₐ[ℚ] Closure} {v : Fin 8 → ZMod 2}
    (hg : HasLabel g v) (k : Fin 8) :
    g (conjRoot k) = binarySign (sigmaMatrix v k) * conjRoot k := by
  have hb (a b : ZMod 2) : binarySign (E := Closure) (a + b) =
      binarySign a * binarySign b := binarySign_add a b
  have hinv (a : ZMod 2) : (binarySign (E := Closure) a)⁻¹ = binarySign a := by
    exact inv_eq_of_mul_eq_one_right (by rw [← sq, binarySign_sq])
  fin_cases k <;> simp only [Genus.conjRoot, sigmaMatrix, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk, map_mul, map_inv₀,
    hg _, hb, mul_inv, hinv] <;> ring

/-- **Conjugation rule.** If `s` moves `√241`, then `s g s⁻¹` has label `sigmaMatrix v`. -/
theorem hasLabel_conj {s g : Closure ≃ₐ[ℚ] Closure} (hs : s baseRoot = -baseRoot)
    {v : Fin 8 → ZMod 2} (hg : HasLabel g v) : HasLabel (s * g * s⁻¹) (sigmaMatrix v) := by
  intro k
  have hs' : s⁻¹ baseRoot = -baseRoot := by
    apply s.injective
    rw [show s (s⁻¹ baseRoot) = baseRoot from s.apply_symm_apply _, map_neg, hs, neg_neg]
  have hsq : (s⁻¹ (genusRoot k)) ^ 2 = (conjRoot k) ^ 2 := by
    rw [← map_pow, genusRoot_sq, conjRoot_sq, conjRadicand_eq, radicand, map_add, map_mul,
      map_ratCast, map_ratCast, hs']
    ring
  have hsgn (a : ZMod 2) : s (binarySign (E := Closure) a) = binarySign a := by
    simp only [binarySign, map_intCast]
  have hss : s (s⁻¹ (genusRoot k)) = genusRoot k := s.apply_symm_apply _
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · have hc : s (conjRoot k) = genusRoot k := by rw [← h, hss]
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h, hg.conjRoot, map_mul, hsgn, hc]
  · have hc : s (conjRoot k) = -genusRoot k := by
      rw [show conjRoot k = -(s⁻¹ (genusRoot k)) by rw [h, neg_neg], map_neg, hss]
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, h, map_neg, hg.conjRoot, map_neg, map_mul, hsgn, hc]
    ring

end UnitDistance.Sqrt241.Local
