module

public import UnitDistance.FilteredBasisHilbert
public import UnitDistance.JenningsAdaptedProduct

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual augmentation Hilbert polynomials and subgroup shift factors

The coefficients are defined from actual successive augmentation quotients.
The subgroup-compatible basis proves that the ambient polynomial equals
the complementary weight polynomial times the actual local polynomial.
-/

noncomputable section
open scoped BigOperators
open Polynomial
namespace UnitDistance.GroupAugmentation
variable (G : Type*) [Group G] [Finite G]

/-- The actual successive augmentation quotient, as an ordinary vector space. -/
abbrev PowerLayer (n : ℕ) :=
  power (ZMod 2) G n ⧸ (power (ZMod 2) G (n+1)).comap (power (ZMod 2) G n).subtype

theorem finrank_powerLayer (n : ℕ) :
    Module.finrank (ZMod 2) (PowerLayer G n) =
      Module.finrank (ZMod 2) (power (ZMod 2) G n) -
        Module.finrank (ZMod 2) (power (ZMod 2) G (n+1)) := by
  have he := Submodule.finrank_quotient_add_finrank
    ((power (ZMod 2) G (n+1)).comap (power (ZMod 2) G n).subtype)
  rw [(Submodule.comapSubtypeEquivOfLe (power_succ_le (ZMod 2) G n)).finrank_eq] at he
  exact Nat.eq_sub_of_add_eq he

/-- The actual finite augmentation Hilbert polynomial. For a finite 2-group
proved nilpotence ensures this contains every nonzero quotient layer. -/
def hilbertPolynomial : ℕ[X] :=
  ∑ n ∈ Finset.range (Nat.card G), Polynomial.monomial n
    (Module.finrank (ZMod 2) (PowerLayer G n))

variable (hG : IsPGroup 2 G)

include hG in
theorem powerLayer_vanishes (n : ℕ) (hn : Nat.card G ≤ n) :
    Module.finrank (ZMod 2) (PowerLayer G n) = 0 := by
  rw [finrank_powerLayer]
  have he : power (ZMod 2) G n = ⊥ :=
    le_bot_iff.mp ((power_antitone (ZMod 2) G hn).trans (power_card_eq_bot G 2 hG).le)
  rw [he,finrank_bot,Nat.zero_sub]

variable {J : Type*} [Fintype J] (b : Module.Basis J (ZMod 2) (A (ZMod 2) G)) (w : J → ℕ)
variable (hspan : ∀ n, Submodule.span (ZMod 2) {a | ∃ j, n ≤ w j ∧ a = b j} = power (ZMod 2) G n)

include hG hspan in
/-- A nonzero actual basis vector cannot carry a weight past the proved
augmentation nilpotence bound. -/
theorem basisWeight_lt_card (j : J) : w j < Nat.card G := by
  have hj : b j ∈ power (ZMod 2) G (w j) := by
    rw [← hspan]
    exact Submodule.subset_span ⟨j,le_rfl,rfl⟩
  by_contra hn
  have hz : b j ∈ power (ZMod 2) G (Nat.card G) := power_antitone (ZMod 2) G (by omega) hj
  rw [power_card_eq_bot G 2 hG,Submodule.mem_bot] at hz
  exact b.ne_zero j hz

include hG hspan in
/-- Actual quotient dimensions derive the basis weight polynomial. -/
theorem hilbertPolynomial_eq_basisWeightSum :
    hilbertPolynomial G = ∑ j, (Polynomial.monomial (w j) 1 : ℕ[X]) := by
  have he := FilteredBasis.hilbert_eq_weight_sum (ZMod 2) (A (ZMod 2) G) J b w
    (Nat.card G) (basisWeight_lt_card G hG b w hspan)
  have hspace (n : ℕ) : FilteredBasis.weightedSubspace (ZMod 2) (A (ZMod 2) G) J b w n =
      power (ZMod 2) G n := hspan n
  rw [← he]
  unfold hilbertPolynomial
  apply Finset.sum_congr rfl
  intro n _
  rw [finrank_powerLayer]
  apply congrArg (Polynomial.monomial n)
  exact congrArg₂ Nat.sub
    (congrArg (fun S : Submodule (ZMod 2) (A (ZMod 2) G) => Module.finrank (ZMod 2) S) (hspace n)).symm
    (congrArg (fun S : Submodule (ZMod 2) (A (ZMod 2) G) => Module.finrank (ZMod 2) S) (hspace (n+1))).symm

theorem hilbertPolynomial_eq_generatorWeightSum :
    hilbertPolynomial G = ∑ j, (Polynomial.monomial (generatorWeight G hG j) 1 : ℕ[X]) :=
  hilbertPolynomial_eq_basisWeightSum G hG (generatorBasis G hG) (generatorWeight G hG)
    (generatorWeightedSpan_eq_power G hG)

variable (D P : Type*) [Group D] [Group P] [Finite D] [Finite P]
variable (f : D →* P)
variable (hinj : ∀ n, Function.Injective (layerMap (ZMod 2) D f n))
variable (hD : IsPGroup 2 D) (hP : IsPGroup 2 P)

/-- The independent complementary monomial shifts form a polynomial with
nonnegative integer coefficients. -/
def shiftPolynomial : ℕ[X] :=
  ∑ t : ComplementChoices D P f hinj, Polynomial.monomial (complementWeight D P f hinj hP t) 1

include hD in
/-- Actual filtered subgroup induction gives the exact Hilbert factorization. -/
theorem hilbertPolynomial_induction :
    hilbertPolynomial P = shiftPolynomial D P f hinj hP * hilbertPolynomial D := by
  rw [hilbertPolynomial_eq_basisWeightSum P hP (adaptedProductBasis D P f hinj hD hP)
    (fun p => complementWeight D P f hinj hP p.1+generatorWeight D hD p.2)
    (adaptedProductWeightedSpan_eq_power D P f hinj hD hP),
    hilbertPolynomial_eq_generatorWeightSum D hD]
  exact FilteredBasis.weight_sum_prod _ (generatorWeight D hD) _ (complementWeight D P f hinj hP)

end UnitDistance.GroupAugmentation
