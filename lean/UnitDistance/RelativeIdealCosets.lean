module

public import UnitDistance.RelativeIdealCosetsFiber
public import UnitDistance.RelativeIdealCosetsFractional

@[expose] public section
set_option backward.privateInPublic true


/-! # Disjoint actual norm-one unit cosets inside the inverse reference ideal -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField nonZeroDivisors Classical
open NumberField

namespace UnitDistance.RelativeIdealCosets

open RelativeUnits

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K]
  {S : Type*} [Fintype S]

/-- Actual integral units embedded in the multiplicative group of the field. -/
def integralUnitField : (𝓞 K)ˣ →* Kˣ := Units.map (algebraMap (𝓞 K) K)

@[simp] theorem integralUnitField_coe (u : (𝓞 K)ˣ) :
    (integralUnitField u : K) = (u : K) := rfl

@[simp] theorem principal_integralUnitField (u : (𝓞 K)ˣ) :
    toPrincipalIdeal (𝓞 K) K (integralUnitField u) = 1 := by
  apply Units.ext
  rw [coe_toPrincipalIdeal, integralUnitField_coe]
  change FractionalIdeal.spanSingleton (𝓞 K)⁰ (algebraMap (𝓞 K) K (u : 𝓞 K)) = 1
  rw [← FractionalIdeal.coeIdeal_span_singleton,
    Ideal.span_singleton_eq_top.mpr u.isUnit]
  rfl

/-- Multiplication of each actual reference generator by each actual relative
norm-one integral unit. -/
def referencePoint {ι : K ≃ₐ[F] K} (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (k : S → ℕ) (j₀ : ChoiceIndex k)
    (p : ReferenceFiber D k j₀ × normOneUnits (F := F) (K := K)) : K :=
  (referenceGenerator hι D k j₀ p.1 : K) * (p.2.val : K)

theorem referencePoint_norm {ι : K ≃ₐ[F] K} (hι : ι ≠ 1)
    (D : PrimePairFamily ι S) (k : S → ℕ) (j₀ : ChoiceIndex k)
    (p : ReferenceFiber D k j₀ × normOneUnits (F := F) (K := K)) :
    Algebra.norm F (referencePoint hι D k j₀ p) = 1 := by
  rw [referencePoint, map_mul, referenceGenerator_norm, one_mul, ← coe_unitNorm,
    show unitNorm (F := F) p.2.val = 1 from p.2.prop]
  rfl

theorem referencePoint_mem_inverseIdeal {ι : K ≃ₐ[F] K} (hι : ι ≠ 1)
    (D : PrimePairFamily ι S) (k : S → ℕ) (j₀ : ChoiceIndex k)
    (p : ReferenceFiber D k j₀ × normOneUnits (F := F) (K := K)) :
    referencePoint hι D k j₀ p ∈ referenceInverseIdeal D k j₀ := by
  change referencePoint hι D k j₀ p ∈ (referenceInverseIdeal D k j₀).val
  have hm := (referenceInverseIdeal D k j₀).val.smul_mem (p.2.val : 𝓞 K)
    (referenceGenerator_mem_inverseIdeal hι D k j₀ p.1)
  simpa only [Algebra.smul_def, referencePoint, mul_comm] using hm

/-- Distinct balanced ideals and cancellation in the field show that the
norm-one unit cosets are disjoint; every point also determines its unit. -/
theorem referencePoint_injective {ι : K ≃ₐ[F] K} (hι : ι ≠ 1)
    (D : PrimePairFamily ι S) (k : S → ℕ) (j₀ : ChoiceIndex k) :
    Function.Injective (referencePoint hι D k j₀) := by
  rintro ⟨j, u⟩ ⟨l, v⟩ h
  have hh : referenceGenerator hι D k j₀ j * integralUnitField u.val =
      referenceGenerator hι D k j₀ l * integralUnitField v.val := by
    apply Units.ext
    exact h
  have hp := congrArg (toPrincipalIdeal (𝓞 K) K) hh
  simp only [map_mul, principal_integralUnitField, mul_one,
    ← referenceGenerator_principal] at hp
  have hi : balancedIdeal D k j.val = balancedIdeal D k l.val := by
    have he := (div_left_inj).mp hp
    have hv := congrArg Units.val he
    exact FractionalIdeal.coeIdeal_injective hv
  have hj : j = l := Subtype.ext (balancedIdeal_injective D k hi)
  subst l
  have hu : u = v := by
    apply Subtype.ext
    apply NumberField.Units.coe_injective K
    exact mul_left_cancel₀ (referenceGenerator hι D k j₀ j).ne_zero h
  exact Prod.ext rfl hu

/-- The literal field coset of the actual norm-one unit group. -/
def referenceCoset {ι : K ≃ₐ[F] K} (hι : ι ≠ 1) (D : PrimePairFamily ι S)
    (k : S → ℕ) (j₀ : ChoiceIndex k) (j : ReferenceFiber D k j₀) : Set K :=
  Set.range fun u : normOneUnits (F := F) (K := K) ↦ referencePoint hι D k j₀ (j, u)

theorem referenceCoset_subset_inverseIdeal {ι : K ≃ₐ[F] K} (hι : ι ≠ 1)
    (D : PrimePairFamily ι S) (k : S → ℕ) (j₀ : ChoiceIndex k)
    (j : ReferenceFiber D k j₀) :
    referenceCoset hι D k j₀ j ⊆ referenceInverseIdeal D k j₀ := by
  rintro _ ⟨u, rfl⟩
  exact referencePoint_mem_inverseIdeal hι D k j₀ (j, u)

theorem referenceCoset_pairwiseDisjoint {ι : K ≃ₐ[F] K} (hι : ι ≠ 1)
    (D : PrimePairFamily ι S) (k : S → ℕ) (j₀ : ChoiceIndex k) :
    Pairwise (fun j l ↦ Disjoint (referenceCoset hι D k j₀ j) (referenceCoset hι D k j₀ l)) := by
  intro j l hjl
  apply Set.disjoint_left.mpr
  rintro x ⟨u, hu⟩ ⟨v, hv⟩
  exact hjl (congrArg Prod.fst (referencePoint_injective hι D k j₀ (hu.trans hv.symm)))

end UnitDistance.RelativeIdealCosets
