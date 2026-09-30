module

public import UnitDistance.Sqrt241.Genus.Base

@[expose] public section
set_option backward.privateInPublic true


/-!
# The canonical genus field has degree 512

`tower j = ℚ⟮√241⟯ ⊔ ℚ⟮√α₀⟯ ⊔ … ⊔ ℚ⟮√α_{j-1}⟯`.  By induction, an element of
`B = ℚ⟮√241⟯` that is a square in `tower j` becomes a square in `B` after
multiplication by a product of radicands with indices `< j`
(`Kummer.sq_of_mem_sup_sqrt`).  Since no nonempty product of radicands is a
square in `B` (`Base.prod_radicand_not_sq`), each step is quadratic, and
`tower 8 = CanonicalGenus.field` has degree `2 · 2⁸ = 512`.
-/

noncomputable section
open IntermediateField

namespace UnitDistance.Sqrt241.Genus

open CanonicalGenus

/-- The base field `B = ℚ(√241)` inside the closure. -/
abbrev B : IntermediateField ℚ Closure := ℚ⟮baseRoot⟯

/-- The genus roots indexed by natural numbers (zero past the end). -/
def rootNat (j : ℕ) : Closure := if h : j < 8 then genusRoot ⟨j, h⟩ else 0

/-- The multiquadratic tower over `B`. -/
def tower : ℕ → IntermediateField ℚ Closure
  | 0 => B
  | j + 1 => tower j ⊔ ℚ⟮rootNat j⟯

theorem tower_le_succ (j : ℕ) : tower j ≤ tower (j + 1) := le_sup_left

theorem tower_mono {j k : ℕ} (h : j ≤ k) : tower j ≤ tower k :=
  monotone_nat_of_le_succ tower_le_succ h

theorem B_le_tower (j : ℕ) : B ≤ tower j := tower_mono (Nat.zero_le j)

theorem rootNat_mem_tower (j : ℕ) : rootNat j ∈ tower (j + 1) :=
  (le_sup_right : ℚ⟮rootNat j⟯ ≤ tower j ⊔ ℚ⟮rootNat j⟯) (mem_adjoin_simple_self ℚ _)

theorem rootNat_sq {j : ℕ} (hj : j < 8) : rootNat j ^ 2 = radicand ⟨j, hj⟩ := by
  rw [rootNat, dite_eq_left hj, genusRoot_sq]

theorem not_sq_241_bot : ∀ y ∈ (⊥ : IntermediateField ℚ Closure), y ^ 2 ≠ baseRoot ^ 2 := by
  intro y hy h
  rw [mem_bot] at hy
  obtain ⟨q, rfl⟩ := hy
  rw [baseRoot_sq] at h
  apply not_isSquare_241
  refine ⟨q, ?_⟩
  apply (algebraMap ℚ Closure).injective
  rw [map_mul, ← sq, h]
  simp

theorem finrank_B : Module.finrank ℚ B = 2 := by
  have h := finrank_sup_sqrt (K := (⊥ : IntermediateField ℚ Closure)) (r := baseRoot)
    (by rw [baseRoot_sq]; exact IntermediateField.algebraMap_mem _ 241) not_sq_241_bot
  rw [bot_sup_eq, IntermediateField.finrank_bot] at h
  simpa using h

/-- The square-class invariant of the tower. -/
theorem tower_sq (j : ℕ) (hj : j ≤ 8) : ∀ x ∈ B, ∀ y ∈ tower j, y ^ 2 = x →
    ∃ m : Finset (Fin 8), (∀ i ∈ m, i.val < j) ∧ ∃ w ∈ B, w ^ 2 = x * ∏ i ∈ m, radicand i := by
  induction j with
  | zero =>
    intro x _ y hy hyx
    exact ⟨∅, by simp, y, hy, by simp [hyx]⟩
  | succ j ih =>
    have hj' : j < 8 := by omega
    have ih' := ih (by omega)
    have hr : rootNat j ^ 2 ∈ tower j := by
      rw [rootNat_sq hj']
      exact B_le_tower j (radicand_mem _)
    have hns : ∀ y ∈ tower j, y ^ 2 ≠ rootNat j ^ 2 := by
      intro y hy h
      rw [rootNat_sq hj'] at h
      obtain ⟨m, hm, w, hw, hw2⟩ := ih' _ (radicand_mem _) y hy h
      have hjm : (⟨j, hj'⟩ : Fin 8) ∉ m := fun h' => lt_irrefl j (hm _ h')
      apply prod_radicand_not_sq (insert ⟨j, hj'⟩ m) (Finset.insert_nonempty _ _) w hw
      rw [Finset.prod_insert hjm, hw2]
    intro x hx y hy hyx
    rcases sq_of_mem_sup_sqrt hr hns (B_le_tower j hx) hy hyx with ⟨w, hw, hw2⟩ | ⟨w, hw, hw2⟩
    · obtain ⟨m, hm, w', hw', hw'2⟩ := ih' x hx w hw hw2
      exact ⟨m, fun i hi => Nat.lt_succ_of_lt (hm i hi), w', hw', hw'2⟩
    · rw [rootNat_sq hj'] at hw2
      have hxr : x * radicand ⟨j, hj'⟩ ∈ B := mul_mem hx (radicand_mem _)
      obtain ⟨m, hm, w', hw', hw'2⟩ := ih' _ hxr w hw hw2
      have hjm : (⟨j, hj'⟩ : Fin 8) ∉ m := fun h' => lt_irrefl j (hm _ h')
      refine ⟨insert ⟨j, hj'⟩ m, ?_, w', hw', ?_⟩
      · intro i hi
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact Nat.lt_succ_self j
        · exact Nat.lt_succ_of_lt (hm i hi)
      · rw [Finset.prod_insert hjm, hw'2]
        ring

theorem finrank_tower (j : ℕ) (hj : j ≤ 8) : Module.finrank ℚ (tower j) = 2 ^ (j + 1) := by
  induction j with
  | zero =>
    show Module.finrank ℚ ↥B = 2 ^ (0 + 1)
    rw [finrank_B]
    norm_num
  | succ j ih =>
    have hj' : j < 8 := by omega
    have hr : rootNat j ^ 2 ∈ tower j := by
      rw [rootNat_sq hj']
      exact B_le_tower j (radicand_mem _)
    have hns : ∀ y ∈ tower j, y ^ 2 ≠ rootNat j ^ 2 := by
      intro y hy h
      rw [rootNat_sq hj'] at h
      obtain ⟨m, hm, w, hw, hw2⟩ := tower_sq j (by omega) _ (radicand_mem _) y hy h
      have hjm : (⟨j, hj'⟩ : Fin 8) ∉ m := fun h' => lt_irrefl j (hm _ h')
      apply prod_radicand_not_sq (insert ⟨j, hj'⟩ m) (Finset.insert_nonempty _ _) w hw
      rw [Finset.prod_insert hjm, hw2]
    change Module.finrank ℚ ↥(tower j ⊔ ℚ⟮rootNat j⟯) = _
    rw [finrank_sup_sqrt hr hns, ih (by omega)]
    ring

theorem tower_le_field (j : ℕ) : tower j ≤ field := by
  induction j with
  | zero => exact adjoin_simple_le_iff.2 baseRoot_mem
  | succ j ih =>
    refine sup_le ih (adjoin_simple_le_iff.2 ?_)
    by_cases hj : j < 8
    · rw [rootNat, dite_eq_left hj]
      exact genusRoot_mem _
    · rw [rootNat, dite_eq_right hj]
      exact zero_mem _

theorem field_eq_tower : field = tower 8 := by
  apply le_antisymm _ (tower_le_field 8)
  apply adjoin_le_iff.2
  intro x hx
  rcases hx with rfl | ⟨i, rfl⟩
  · exact B_le_tower 8 (mem_adjoin_simple_self ℚ _)
  · have h := rootNat_mem_tower i.val
    rw [rootNat, dite_eq_left i.isLt] at h
    exact tower_mono (by omega : i.val + 1 ≤ 8) h

/-- The canonical genus field has degree `512`. -/
theorem finrank_carrier : Module.finrank ℚ Carrier = 512 := by
  change Module.finrank ℚ ↥field = 512
  rw [field_eq_tower, finrank_tower 8 le_rfl]
  norm_num

end UnitDistance.Sqrt241.Genus
