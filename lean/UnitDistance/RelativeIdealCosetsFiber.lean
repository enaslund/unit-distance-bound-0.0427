module

public import UnitDistance.RelativeIdealCosetsBalanced
public import UnitDistance.RelativeIdealCosetsDistinct

@[expose] public section
set_option backward.privateInPublic true


/-! # A large actual relative-class fiber and its principal reference generators -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField nonZeroDivisors Classical
open NumberField

namespace UnitDistance.RelativeIdealCosets

open RelativeUnits

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K]
  {S : Type*} [Fintype S]

/-- The literal fiber of the actual relative class of a reference index. -/
abbrev ReferenceFiber {ι : K ≃ₐ[F] K} (D : PrimePairFamily ι S) (k : S → ℕ)
    (j₀ : ChoiceIndex k) := {j : ChoiceIndex k // choiceClass D k j = choiceClass D k j₀}

instance referenceFiber_nonempty {ι : K ≃ₐ[F] K} (D : PrimePairFamily ι S) (k : S → ℕ)
    (j₀ : ChoiceIndex k) : Nonempty (ReferenceFiber D k j₀) := ⟨⟨j₀, rfl⟩⟩

/-- Pigeonhole in the actual finite relative ideal-class quotient supplies
at least the full number of choices divided by the actual quotient order. -/
theorem exists_large_referenceFiber {ι : K ≃ₐ[F] K} (D : PrimePairFamily ι S) (k : S → ℕ) :
    ∃ j₀ : ChoiceIndex k,
      (∏ s, (k s + 1) : ℕ) / (Nat.card (RelativeClassQuotient (F := F) (K := K)) : ℝ) ≤
        (Nat.card (ReferenceFiber D k j₀) : ℝ) := by
  letI := Fintype.ofFinite (RelativeClassQuotient (F := F) (K := K))
  let a : ℝ := Fintype.card (ChoiceIndex k)
  let q : ℝ := Fintype.card (RelativeClassQuotient (F := F) (K := K))
  have ha : 0 < a := by
    dsimp [a]
    exact_mod_cast Fintype.card_pos (α := ChoiceIndex k)
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast Fintype.card_pos (α := RelativeClassQuotient (F := F) (K := K))
  obtain ⟨c, hc⟩ := Fintype.exists_le_card_fiber_of_nsmul_le_card
    (choiceClass D k) (b := a / q) (by
      change (Fintype.card (RelativeClassQuotient (F := F) (K := K))) • (a / q) ≤ a
      rw [nsmul_eq_mul]
      change q * (a / q) ≤ a
      exact le_of_eq (mul_div_cancel₀ a (ne_of_gt hq)))
  have hp : 0 < (Finset.univ.filter fun j ↦ choiceClass D k j = c).card := by
    exact_mod_cast lt_of_lt_of_le (div_pos ha hq) hc
  obtain ⟨j₀, hj₀⟩ := Finset.card_pos.mp hp
  have hjc := (Finset.mem_filter.mp hj₀).2
  refine ⟨j₀, ?_⟩
  simpa only [a, q, choiceIndex_card, Nat.card_eq_fintype_card, ReferenceFiber,
    Fintype.card_subtype, hjc] using hc

/-- The actual field element chosen from the proved principal-generator
existence theorem for each member of the reference fiber. -/
def referenceWitness {ι : K ≃ₐ[F] K} (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (k : S → ℕ) (j₀ : ChoiceIndex k) (j : ReferenceFiber D k j₀) : Kˣ :=
  (same_choiceClass_exists_normOne_generator hι D k j.val j₀ j.prop).choose

/-- The actual norm-one reference generator `x/ι(x)`. -/
def referenceGenerator {ι : K ≃ₐ[F] K} (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (k : S → ℕ) (j₀ : ChoiceIndex k) (j : ReferenceFiber D k j₀) : Kˣ :=
  fieldCoboundary ι (referenceWitness hι D k j₀ j)

theorem referenceGenerator_principal {ι : K ≃ₐ[F] K} (hι : ι ≠ 1)
    (D : PrimePairFamily ι S) (k : S → ℕ) (j₀ : ChoiceIndex k)
    (j : ReferenceFiber D k j₀) :
    FractionalIdeal.mk0 K (balancedNonzeroIdeal D k j.val) /
        FractionalIdeal.mk0 K (balancedNonzeroIdeal D k j₀) =
      toPrincipalIdeal (𝓞 K) K (referenceGenerator hι D k j₀ j) :=
  (same_choiceClass_exists_normOne_generator hι D k j.val j₀ j.prop).choose_spec.1

theorem referenceGenerator_norm {ι : K ≃ₐ[F] K} (hι : ι ≠ 1)
    (D : PrimePairFamily ι S) (k : S → ℕ) (j₀ : ChoiceIndex k)
    (j : ReferenceFiber D k j₀) :
    Algebra.norm F (referenceGenerator hι D k j₀ j : K) = 1 :=
  norm_fieldCoboundary ι hι _

/-- The inverse of the actual reference balanced integral ideal. -/
def referenceInverseIdeal {ι : K ≃ₐ[F] K} (D : PrimePairFamily ι S) (k : S → ℕ)
    (j₀ : ChoiceIndex k) : FractionalIdeal (𝓞 K)⁰ K :=
  (balancedIdeal D k j₀ : FractionalIdeal (𝓞 K)⁰ K)⁻¹

/-- Every actual reference generator belongs to the inverse reference ideal. -/
theorem referenceGenerator_mem_inverseIdeal {ι : K ≃ₐ[F] K} (hι : ι ≠ 1)
    (D : PrimePairFamily ι S) (k : S → ℕ) (j₀ : ChoiceIndex k)
    (j : ReferenceFiber D k j₀) :
    (referenceGenerator hι D k j₀ j : K) ∈ referenceInverseIdeal D k j₀ := by
  apply FractionalIdeal.spanSingleton_le_iff_mem.mp
  have h := congrArg Units.val (referenceGenerator_principal hι D k j₀ j)
  rw [coe_toPrincipalIdeal] at h
  rw [← h]
  change (balancedIdeal D k j.val : FractionalIdeal (𝓞 K)⁰ K) *
    (balancedIdeal D k j₀ : FractionalIdeal (𝓞 K)⁰ K)⁻¹ ≤ _
  calc
    _ ≤ 1 * (balancedIdeal D k j₀ : FractionalIdeal (𝓞 K)⁰ K)⁻¹ :=
      mul_le_mul_left FractionalIdeal.coeIdeal_le_one _
    _ = _ := one_mul _

end UnitDistance.RelativeIdealCosets
