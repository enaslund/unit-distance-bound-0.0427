module

public import UnitDistance.RelativeIdealCosetsBasic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section
set_option backward.privateInPublic true


/-! # The actual one-sided and balanced split-prime ideal families -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField nonZeroDivisors Classical
open NumberField IsDedekindDomain

namespace UnitDistance.RelativeIdealCosets

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K]

/-- A finite list of distinct actual prime pairs exchanged by the quadratic
automorphism. All primes are literal nonzero prime ideals of the integers. -/
structure PrimePairFamily (ι : K ≃ₐ[F] K) (S : Type*) where
  prime : S × Bool → HeightOneSpectrum (𝓞 K)
  partner : ∀ s, (prime (s, true)).asIdeal = conjugateIdeal ι (prime (s, false)).asIdeal
  distinct : Function.Injective (fun a ↦ (prime a).asIdeal)

variable {S : Type*} [Fintype S]

/-- The manuscript's multi-index, with every exponent between zero and `k`. -/
abbrev ChoiceIndex (k : S → ℕ) := ∀ s, Fin (k s + 1)

instance choiceIndex_nonempty (k : S → ℕ) : Nonempty (ChoiceIndex k) :=
  ⟨fun _ ↦ 0⟩

theorem choiceIndex_card (k : S → ℕ) :
    Fintype.card (ChoiceIndex k) = ∏ s, (k s + 1) := by simp [ChoiceIndex]

/-- The one-sided actual integral ideal `B_j = ∏ P_s^j_s`. -/
def oneSidedIdeal {ι : K ≃ₐ[F] K} (D : PrimePairFamily ι S) (k : S → ℕ)
    (j : ChoiceIndex k) : Ideal (𝓞 K) := ∏ s, (D.prime (s, false)).asIdeal ^ (j s).val

/-- The balanced actual integral ideal `J_j = ∏ P_s^j_s (ιP_s)^(k_s-j_s)`. -/
def balancedIdeal {ι : K ≃ₐ[F] K} (D : PrimePairFamily ι S) (k : S → ℕ)
    (j : ChoiceIndex k) : Ideal (𝓞 K) :=
  ∏ s, (D.prime (s, false)).asIdeal ^ (j s).val *
    (D.prime (s, true)).asIdeal ^ (k s - (j s).val)

theorem oneSidedIdeal_ne_zero {ι : K ≃ₐ[F] K} (D : PrimePairFamily ι S) (k : S → ℕ)
    (j : ChoiceIndex k) : oneSidedIdeal D k j ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr fun s _ ↦ pow_ne_zero _ (D.prime (s, false)).ne_bot

theorem balancedIdeal_ne_zero {ι : K ≃ₐ[F] K} (D : PrimePairFamily ι S) (k : S → ℕ)
    (j : ChoiceIndex k) : balancedIdeal D k j ≠ 0 := by
  exact Finset.prod_ne_zero_iff.mpr fun s _ ↦
    mul_ne_zero (pow_ne_zero _ (D.prime (s, false)).ne_bot)
      (pow_ne_zero _ (D.prime (s, true)).ne_bot)

def oneSidedNonzeroIdeal {ι : K ≃ₐ[F] K} (D : PrimePairFamily ι S) (k : S → ℕ)
    (j : ChoiceIndex k) : NonzeroIdeal K :=
  ⟨oneSidedIdeal D k j, mem_nonZeroDivisors_iff_ne_zero.mpr (oneSidedIdeal_ne_zero D k j)⟩

def balancedNonzeroIdeal {ι : K ≃ₐ[F] K} (D : PrimePairFamily ι S) (k : S → ℕ)
    (j : ChoiceIndex k) : NonzeroIdeal K :=
  ⟨balancedIdeal D k j, mem_nonZeroDivisors_iff_ne_zero.mpr (balancedIdeal_ne_zero D k j)⟩

theorem conjugate_oneSidedIdeal {ι : K ≃ₐ[F] K} (D : PrimePairFamily ι S)
    (k : S → ℕ) (j : ChoiceIndex k) :
    conjugateIdeal ι (oneSidedIdeal D k j) =
      ∏ s, (D.prime (s, true)).asIdeal ^ (j s).val := by
  simp only [oneSidedIdeal, map_prod, map_pow, ← D.partner]

/-- This exact integral-ideal identity relates the balanced family to the
one-sided family and a fixed ideal independent of the multi-index. -/
theorem balanced_mul_conjugate_oneSided {ι : K ≃ₐ[F] K} (D : PrimePairFamily ι S)
    (k : S → ℕ) (j : ChoiceIndex k) :
    balancedIdeal D k j * conjugateIdeal ι (oneSidedIdeal D k j) =
      oneSidedIdeal D k j * ∏ s, (D.prime (s, true)).asIdeal ^ k s := by
  rw [conjugate_oneSidedIdeal]
  unfold balancedIdeal oneSidedIdeal
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro s _
  rw [mul_assoc, ← pow_add, Nat.sub_add_cancel (Nat.le_of_lt_succ (j s).isLt)]

/-- The literal relative ideal class assigned to a multi-index. -/
def choiceClass {ι : K ≃ₐ[F] K} (D : PrimePairFamily ι S) (k : S → ℕ)
    (j : ChoiceIndex k) : RelativeUnits.RelativeClassQuotient (F := F) (K := K) :=
  relativeIdealClass (F := F) (oneSidedNonzeroIdeal D k j)

end UnitDistance.RelativeIdealCosets
