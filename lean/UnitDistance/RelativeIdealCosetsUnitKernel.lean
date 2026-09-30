module

public import UnitDistance.RelativeIdealCosets

@[expose] public section
set_option backward.privateInPublic true


/-! # Actual principal-generator fibers are norm-one integral unit cosets -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField nonZeroDivisors Classical
open NumberField

namespace UnitDistance.RelativeIdealCosets

open RelativeUnits

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K]

/-- The kernel of the actual principal-ideal map consists exactly of the
embedded integral units. -/
theorem principal_eq_one_exists_integralUnit (x : Kˣ)
    (h : toPrincipalIdeal (𝓞 K) K x = 1) :
    ∃ u : (𝓞 K)ˣ, integralUnitField u = x := by
  have hx : (x : K) ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    have hh := congrArg Units.val h
    simp only [coe_toPrincipalIdeal, Units.val_one] at hh
    rw [← hh]
    exact FractionalIdeal.mem_spanSingleton_self _ _
  have hxi : ((x⁻¹ : Kˣ) : K) ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    have hh : toPrincipalIdeal (𝓞 K) K x⁻¹ = 1 := by simp [map_inv, h]
    have hv := congrArg Units.val hh
    simp only [coe_toPrincipalIdeal, Units.val_one] at hv
    rw [← hv]
    exact FractionalIdeal.mem_spanSingleton_self _ _
  obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff (𝓞 K)⁰).mp hx
  obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff (𝓞 K)⁰).mp hxi
  have hab : a * b = 1 := by
    apply RingOfIntegers.coe_injective
    change algebraMap (𝓞 K) K (a * b) = algebraMap (𝓞 K) K 1
    rw [map_mul, ha, hb, map_one]
    exact x.val_inv
  let u : (𝓞 K)ˣ := ⟨a, b, hab, (mul_comm b a).trans hab⟩
  exact ⟨u, Units.ext ha⟩

/-- Two actual norm-one field elements generate the same fractional ideal
exactly when they differ by an actual norm-one integral unit. -/
theorem same_principal_normOne_iff (β y : Kˣ)
    (hβ : Algebra.norm F (β : K) = 1) (hy : Algebra.norm F (y : K) = 1) :
    toPrincipalIdeal (𝓞 K) K y = toPrincipalIdeal (𝓞 K) K β ↔
      ∃ u : normOneUnits (F := F) (K := K), y = β * integralUnitField u.val := by
  constructor
  · intro h
    have hz : toPrincipalIdeal (𝓞 K) K (y / β) = 1 := by rw [map_div, h]; simp
    obtain ⟨u, hu⟩ := principal_eq_one_exists_integralUnit (y / β) hz
    have hnu : unitNorm (F := F) u = 1 := by
      apply NumberField.Units.coe_injective F
      change (unitNorm (F := F) u : F) = (1 : F)
      rw [coe_unitNorm]
      have hh : (u : K) = (y : K) / (β : K) := by
        simpa only [integralUnitField_coe, Units.val_div_eq_div_val] using
          congrArg (fun z : Kˣ ↦ (z : K)) hu
      rw [hh, div_eq_mul_inv, map_mul, Algebra.norm_inv, hy, hβ]
      simp
    refine ⟨⟨u, hnu⟩, ?_⟩
    rw [hu]
    simp
  · rintro ⟨u, rfl⟩
    simp only [map_mul, principal_integralUnitField, mul_one]

/-- Distinct actual principal ideals imply disjoint norm-one unit cosets. -/
theorem normOneCosetPoint_injective {T : Type*} (β : T → Kˣ)
    (hβ : Function.Injective (fun t ↦ toPrincipalIdeal (𝓞 K) K (β t))) :
    Function.Injective (fun p : T × normOneUnits (F := F) (K := K) ↦
      (β p.1 : K) * (p.2.val : K)) := by
  rintro ⟨j, u⟩ ⟨l, v⟩ h
  have hh : β j * integralUnitField u.val = β l * integralUnitField v.val := Units.ext h
  have hp := congrArg (toPrincipalIdeal (𝓞 K) K) hh
  simp only [map_mul, principal_integralUnitField, mul_one] at hp
  have hj := hβ hp
  subst l
  have hu : u = v := by
    apply Subtype.ext
    apply NumberField.Units.coe_injective K
    exact mul_left_cancel₀ (β j).ne_zero h
  exact Prod.ext rfl hu

end UnitDistance.RelativeIdealCosets
