module

public import UnitDistance.Sqrt241.Base.ClassNumber
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem

@[expose] public section
set_option backward.privateInPublic true

/-!
# Units of `B = ℚ(√241)` modulo squares

The unit rank of `B` is one and its roots of unity are `±1` (`B` is real).
Since `N(ε) = -1`, `ε` is an odd power of a fundamental unit up to sign, so
every unit is `(-1)^a ε^b w²` (`unit_eq_mul_sq`). We do not need (and do not
prove) that `ε` is itself a fundamental unit.
-/

noncomputable section

namespace UnitDistance.Sqrt241.Base

open NumberField NumberField.Units

theorem unitRank_eq_one : Units.rank B = 1 := by
  rw [Units.rank, card_infinitePlace]

set_option backward.isDefEq.respectTransparency false in
/-- The roots of unity of `B` are `±1`. -/
theorem torsion_eq_one_or_neg_one (x : torsion B) :
    (x : (𝓞 B)ˣ) = 1 ∨ (x : (𝓞 B)ˣ) = -1 := by
  by_cases! hc : 2 < orderOf (x : (𝓞 B)ˣ)
  · rw [← orderOf_units, ← orderOf_submonoid] at hc
    have := InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hc (IsPrimitiveRoot.orderOf (x.1 : B))
    rw [nrRealPlaces_eq_two] at this
    exact absurd this (by norm_num)
  · interval_cases hi : orderOf (x : (𝓞 B)ˣ)
    · linarith [orderOf_pos_iff.2 ((CommGroup.mem_torsion x.1).1 x.2)]
    · exact Or.intro_left _ (orderOf_eq_one_iff.1 hi)
    · rw [← orderOf_units, CharP.orderOf_eq_two_iff 0 (by decide)] at hi
      simp [← Units.val_inj, ← Units.val_inj, Units.val_neg, Units.val_one, hi]

theorem mem_torsion_iff (u : (𝓞 B)ˣ) : u ∈ torsion B ↔ u = 1 ∨ u = -1 := by
  constructor
  · intro h
    exact torsion_eq_one_or_neg_one ⟨u, h⟩
  · rintro (rfl | rfl)
    · exact (torsion B).one_mem
    · exact neg_one_mem_torsion

/-- The index of the unique fundamental unit. -/
def fundIndex : Fin (Units.rank B) := ⟨0, by rw [unitRank_eq_one]; norm_num⟩

theorem fundIndex_eq (i : Fin (Units.rank B)) : i = fundIndex := by
  apply Fin.ext
  have h1 := i.isLt
  have h2 := unitRank_eq_one
  simp only [fundIndex]
  omega

/-- A fundamental unit of `B` (Mathlib's choice, `fundSystem`). -/
def fundUnit : (𝓞 B)ˣ := fundSystem B fundIndex

/-- Dirichlet: every unit is `± η^m` for the fundamental unit `η`. -/
theorem eq_pm_zpow (u : (𝓞 B)ˣ) :
    ∃ ζ : (𝓞 B)ˣ, (ζ = 1 ∨ ζ = -1) ∧ ∃ m : ℤ, u = ζ * fundUnit ^ m := by
  obtain ⟨⟨ζ, e⟩, h, _⟩ := exist_unique_eq_mul_prod B u
  refine ⟨ζ, torsion_eq_one_or_neg_one ζ, e fundIndex, ?_⟩
  rw [h]
  congr 1
  rw [Fintype.prod_eq_single fundIndex (fun i hi ↦ absurd (fundIndex_eq i) hi)]
  rfl

/-- The norm on units, `(𝓞 B)ˣ → ℤˣ`. -/
def unitNorm : (𝓞 B)ˣ →* ℤˣ := Units.map (Algebra.norm ℤ : 𝓞 B →* ℤ)

@[simp] theorem coe_unitNorm (u : (𝓞 B)ˣ) :
    ((unitNorm u : ℤˣ) : ℤ) = Algebra.norm ℤ (u : 𝓞 B) := rfl

theorem unitNorm_neg_one : unitNorm (-1) = 1 := by
  apply Units.ext
  rw [coe_unitNorm, Units.val_neg, Units.val_one,
    show (-1 : 𝓞 B) = mk (-1) 0 by simp [mk], norm_mk]
  norm_num

theorem unitNorm_epsUnit : unitNorm epsUnit = -1 := by
  apply Units.ext
  rw [coe_unitNorm, coe_epsUnit, norm_eps]
  rfl

theorem unitNorm_pm {ζ : (𝓞 B)ˣ} (h : ζ = 1 ∨ ζ = -1) : unitNorm ζ = 1 := by
  rcases h with rfl | rfl
  · exact map_one _
  · exact unitNorm_neg_one

/-- `ε = ± η^k` with `k` odd. -/
theorem epsUnit_eq : ∃ ζ : (𝓞 B)ˣ, (ζ = 1 ∨ ζ = -1) ∧ ∃ k : ℤ, Odd k ∧
    epsUnit = ζ * fundUnit ^ k := by
  obtain ⟨ζ, hζ, k, hk⟩ := eq_pm_zpow epsUnit
  refine ⟨ζ, hζ, k, ?_, hk⟩
  have hn := congrArg unitNorm hk
  rw [map_mul, map_zpow, unitNorm_pm hζ, one_mul, unitNorm_epsUnit] at hn
  rcases Int.units_eq_one_or (unitNorm fundUnit) with h | h
  · rw [h, one_zpow] at hn
    exact absurd hn (by decide)
  · rw [h] at hn
    by_contra hodd
    rw [Int.not_odd_iff_even] at hodd
    rw [hodd.neg_one_zpow] at hn
    exact absurd hn (by decide)

/-- **Units modulo squares.** Every unit of `𝓞 B` is `(-1)^a ε^b w²` with `a, b ∈ {0, 1}`. -/
theorem unit_eq_mul_sq (u : (𝓞 B)ˣ) : ∃ a b : ℕ, a < 2 ∧ b < 2 ∧ ∃ w : (𝓞 B)ˣ,
    u = (-1) ^ a * epsUnit ^ b * w ^ 2 := by
  obtain ⟨ζ, hζ, m, rfl⟩ := eq_pm_zpow u
  obtain ⟨ζ₁, hζ₁, k, hk, hε⟩ := epsUnit_eq
  have hsign : ∀ ξ : (𝓞 B)ˣ, (ξ = 1 ∨ ξ = -1) → ∃ a : ℕ, a < 2 ∧ ξ = (-1) ^ a := by
    rintro ξ (rfl | rfl)
    · exact ⟨0, by norm_num, by simp⟩
    · exact ⟨1, by norm_num, by simp⟩
  rcases Int.even_or_odd' m with ⟨r, hr | hr⟩
  · obtain ⟨a, ha, rfl⟩ := hsign ζ hζ
    refine ⟨a, 0, ha, by norm_num, fundUnit ^ r, ?_⟩
    have h2 : fundUnit ^ m = (fundUnit ^ r) ^ 2 := by
      rw [hr, ← zpow_natCast (fundUnit ^ r), ← zpow_mul]
      congr 1
      push_cast
      ring
    rw [h2, pow_zero, mul_one]
  · -- `m` odd: `m - k` is even
    obtain ⟨s, hs⟩ : Even (m - k) := by
      rw [hr]
      exact (odd_two_mul_add_one r).sub_odd hk
    have hζζ : ζ * ζ₁⁻¹ = 1 ∨ ζ * ζ₁⁻¹ = -1 := by
      rcases hζ with rfl | rfl <;> rcases hζ₁ with rfl | rfl <;> simp
    obtain ⟨a, ha, hae⟩ := hsign _ hζζ
    refine ⟨a, 1, ha, by norm_num, fundUnit ^ s, ?_⟩
    have h2 : (fundUnit ^ s) ^ 2 = fundUnit ^ (m - k) := by
      rw [hs, ← zpow_natCast (fundUnit ^ s), ← zpow_mul]
      congr 1
      push_cast
      ring
    rw [← hae, pow_one, hε, h2, zpow_sub]
    group

end UnitDistance.Sqrt241.Base
