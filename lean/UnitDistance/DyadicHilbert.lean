module

public import UnitDistance.DyadicAugmentation
public import Mathlib.Algebra.Polynomial.Basic

@[expose] public section
set_option backward.privateInPublic true


/-! Hilbert-polynomial assembly from precise dimensions of actual augmentation powers. -/

noncomputable section
open scoped BigOperators
open Polynomial

namespace UnitDistance.Dyadic.AlgebraD

def dimensions : Fin 9 → ℕ := ![32, 31, 28, 23, 16, 9, 4, 1, 0]

/-- The finite Hilbert polynomial, formed from dimensions of actual
augmentation powers. Vanishing at degree eight ensures it is the full series. -/
def hilbertPolynomial : ℕ[X] := ∑ n ∈ Finset.range 8,
  Polynomial.monomial n
    (Module.finrank F (augmentationPower n) - Module.finrank F (augmentationPower (n + 1)))

theorem finrank_augmentationPower_zero :
    Module.finrank F (augmentationPower 0) = 32 := by
  change Module.finrank F (⊤ : Submodule F AlgebraD) = 32
  rw [finrank_top, finrank_algebra]

theorem augmentationPower_antitone : Antitone augmentationPower := by
  apply antitone_nat_of_succ_le
  intro n
  rw [← stage_eq_augmentationPower, ← stage_eq_augmentationPower]
  exact stage_succ_le n

/-- The ordinary successive quotient `Jⁿ / Jⁿ⁺¹`, with the smaller subspace
viewed inside the larger one. -/
abbrev augmentationLayer (n : ℕ) :=
  augmentationPower n ⧸ (augmentationPower (n + 1)).comap (augmentationPower n).subtype

theorem finrank_augmentationLayer (n : ℕ) :
    Module.finrank F (augmentationLayer n) =
      Module.finrank F (augmentationPower n) -
      Module.finrank F (augmentationPower (n + 1)) := by
  have hle : augmentationPower (n + 1) ≤ augmentationPower n :=
    augmentationPower_antitone (Nat.le_succ n)
  have hdim := Submodule.finrank_quotient_add_finrank
    ((augmentationPower (n + 1)).comap (augmentationPower n).subtype)
  have he := (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  rw [he] at hdim
  exact Nat.eq_sub_of_add_eq hdim

/-- Thus the dimension-difference formula is exactly the Hilbert polynomial
defined with the ordinary successive quotient spaces. -/
theorem hilbertPolynomial_eq_quotient_sum :
    hilbertPolynomial = ∑ n ∈ Finset.range 8,
      Polynomial.monomial n (Module.finrank F (augmentationLayer n)) := by
  simp only [hilbertPolynomial, finrank_augmentationLayer]

theorem augmentationPower_vanishes
    (h8 : augmentationPower 8 = ⊥) {n : ℕ} (hn : 8 ≤ n) :
    augmentationPower n = ⊥ := by
  apply le_bot_iff.mp
  rw [← h8]
  exact augmentationPower_antitone hn

/-- Assembly requires exact dimensions of independently defined vector spaces,
not a success predicate or a numerical hash. -/
theorem hilbertPolynomial_of_dimensions
    (h : ∀ i : Fin 9, Module.finrank F (augmentationPower i.val) = dimensions i) :
    hilbertPolynomial = (1 + X) ^ 3 * (1 + X ^ 2) ^ 2 := by
  have h0 : Module.finrank F (augmentationPower 0) = 32 := h 0
  have h1 : Module.finrank F (augmentationPower 1) = 31 := h 1
  have h2 : Module.finrank F (augmentationPower 2) = 28 := h 2
  have h3 : Module.finrank F (augmentationPower 3) = 23 := h 3
  have h4 : Module.finrank F (augmentationPower 4) = 16 := h 4
  have h5 : Module.finrank F (augmentationPower 5) = 9 := h 5
  have h6 : Module.finrank F (augmentationPower 6) = 4 := h 6
  have h7 : Module.finrank F (augmentationPower 7) = 1 := h 7
  have h8 : Module.finrank F (augmentationPower 8) = 0 := h 8
  simp only [hilbertPolynomial, Finset.sum_range_succ, Finset.sum_range_zero]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8]
  norm_num only
  simp only [← Polynomial.C_mul_X_pow_eq_monomial]
  norm_num
  ring

theorem seventh_power_le_socle (h8 : augmentationPower 8 = ⊥) :
    augmentationPower 7 ≤ socle := by
  intro v hv
  apply (mem_socle_iff_annihilates_augmentation v).mpr
  intro b hb
  have hm := stage_mul_augmentation 7 v b
    ((stage_eq_augmentationPower 7).symm ▸ hv) hb
  rw [stage_eq_augmentationPower 8, h8] at hm
  exact hm

theorem seventh_power_eq_socle_of_dimensions
    (h7 : Module.finrank F (augmentationPower 7) = 1)
    (h8 : augmentationPower 8 = ⊥) : augmentationPower 7 = socle := by
  apply Submodule.eq_of_le_of_finrank_eq (seventh_power_le_socle h8)
  rw [h7, finrank_socle]

end UnitDistance.Dyadic.AlgebraD
