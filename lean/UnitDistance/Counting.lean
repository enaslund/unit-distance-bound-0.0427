module

public import UnitDistance.Target

@[expose] public section
set_option backward.privateInPublic true


/-! Exact ordered/unordered normalization and the cardinality-growth implication. -/

open scoped Classical BigOperators
open Filter

namespace UnitDistance

@[simp] theorem mem_orderedUnitPairs {U : Finset ℂ} {x y : ℂ} :
    (x, y) ∈ orderedUnitPairs U ↔ x ∈ U ∧ y ∈ U ∧ dist x y = 1 := by
  simp [orderedUnitPairs, and_assoc]

@[simp] theorem mem_unorderedUnitPairs {U : Finset ℂ} {x y : ℂ} :
    Sym2.mk x y ∈ unorderedUnitPairs U ↔ x ∈ U ∧ y ∈ U ∧ dist x y = 1 := by
  simp only [unorderedUnitPairs, Finset.mem_filter, Finset.mk_mem_sym2_iff,
    Sym2.mk_isDiag_iff, Sym2.lift_mk]
  constructor
  · tauto
  · rintro ⟨hx, hy, hd⟩
    refine ⟨⟨hx, hy⟩, ?_, hd⟩
    intro h
    subst y
    simp at hd

theorem ordered_card_eq_twice_unordered (U : Finset ℂ) :
    (orderedUnitPairs U).card = 2 * (unorderedUnitPairs U).card := by
  let f : ℂ × ℂ → Sym2 ℂ := fun e => Sym2.mk e.1 e.2
  have hmap : Set.MapsTo f (orderedUnitPairs U) (unorderedUnitPairs U) := by
    rintro ⟨x, y⟩ h
    exact mem_unorderedUnitPairs.mpr (mem_orderedUnitPairs.mp h)
  rw [Finset.card_eq_sum_card_fiberwise hmap]
  have hfiber : ∀ z ∈ unorderedUnitPairs U,
      ({e ∈ orderedUnitPairs U | f e = z}).card = 2 := by
    intro z
    induction z using Sym2.inductionOn with
    | hf x y =>
      intro hz
      obtain ⟨hx, hy, hd⟩ := mem_unorderedUnitPairs.mp hz
      have hne : x ≠ y := by intro h; subst y; simp at hd
      have heq : {e ∈ orderedUnitPairs U | f e = Sym2.mk x y} =
          {(x, y), (y, x)} := by
        ext ⟨a, b⟩
        simp only [Finset.mem_filter, mem_orderedUnitPairs, f,
          Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro h
          exact (Sym2.mk_eq_mk_iff (p := (a, b)) (q := (x, y))).mp h.2
        · rintro (h | h) <;> cases h
          · exact ⟨⟨hx, hy, hd⟩, rfl⟩
          · exact ⟨⟨hy, hx, by simpa [dist_comm] using hd⟩, Sym2.eq_swap⟩
      rw [heq]
      simp [hne]
  simp_rw [Finset.sum_congr rfl hfiber]
  simp [Nat.mul_comm]

theorem unitPairs_eq_unordered_card (U : Finset ℂ) :
    unitPairs U = ((unorderedUnitPairs U).card : ℝ) := by
  rw [unitPairs, ordered_card_eq_twice_unordered]
  push_cast
  ring

theorem ratio_le_card_sq (U : Finset ℂ) {a : ℝ} (ha : 0 ≤ a) :
    unitPairs U / (U.card : ℝ) ^ a ≤ (U.card : ℝ)^2 := by
  by_cases hU : U = ∅
  · simp [hU]
  have hn : 1 ≤ (U.card : ℝ) := by
    exact_mod_cast (Finset.one_le_card.mpr (Finset.nonempty_iff_ne_empty.mpr hU))
  have hp := Real.one_le_rpow hn ha
  calc
    unitPairs U / (U.card : ℝ)^a ≤ unitPairs U :=
      div_le_self (unitPairs_nonneg U) hp
    _ ≤ (U.card : ℝ)^2 := by
      have := unitPairs_le U
      nlinarith [sq_nonneg (U.card : ℝ)]

/-- Divergence of the ratio forces actual cardinalities to tend to infinity. -/
theorem card_tendsto_of_ratio_tendsto (U : ℕ → Finset ℂ) {a : ℝ} (ha : 0 ≤ a)
    (h : Tendsto (fun j => unitPairs (U j) / ((U j).card : ℝ)^a) atTop atTop) :
    Tendsto (fun j => (U j).card) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [tendsto_atTop.mp h ((b : ℝ)^2 + 1)] with j hj
  have hu := ratio_le_card_sq (U j) ha
  by_contra hn
  have hn' : ((U j).card : ℝ) ≤ b := by exact_mod_cast (le_of_lt (not_le.mp hn))
  have hnonneg : 0 ≤ ((U j).card : ℝ) := Nat.cast_nonneg _
  nlinarith [sq_nonneg ((b : ℝ) - (U j).card)]

end UnitDistance
