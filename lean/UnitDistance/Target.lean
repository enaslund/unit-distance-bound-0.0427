module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Finset.Sym
public import Mathlib.Order.Filter.AtTopBot.Tendsto
public import Mathlib.Tactic

@[expose] public section
set_option backward.privateInPublic true


/-!
# The ordinary planar target

The plane is `ℂ` with its usual Euclidean distance. An unordered pair is
counted with weight one by dividing the number of ordered pairs by two.
No multiplicity or altered metric is used. `unorderedUnitPairs` also gives
the direct `Sym2` definition; the normalization identity is proved separately.
-/

open scoped Classical
open Filter

namespace UnitDistance

noncomputable def orderedUnitPairs (U : Finset ℂ) : Finset (ℂ × ℂ) :=
  (U ×ˢ U).filter (fun e => dist e.1 e.2 = 1)

noncomputable def unorderedUnitPairs (U : Finset ℂ) : Finset (Sym2 ℂ) :=
  U.sym2.filter (fun e => ¬e.IsDiag ∧
    Sym2.lift ⟨fun x y : ℂ => dist x y = 1,
      fun x y => by simp [dist_comm]⟩ e)

noncomputable def unitPairs (U : Finset ℂ) : ℝ :=
  (orderedUnitPairs U).card / 2

noncomputable def increment : ℝ := 83647 / 2000000

noncomputable def exponent : ℝ := 2083647 / 2000000

theorem exponent_eq : exponent = 1 + increment := by
  norm_num [exponent, increment]

theorem increment_pos : 0 < increment := by norm_num [increment]

theorem increment_lt_one : increment < 1 := by norm_num [increment]

/-- This is the ultimate manuscript claim. No theorem in this file proves it. -/
def Target : Prop :=
  ∃ U : ℕ → Finset ℂ,
    Tendsto (fun j => (U j).card) atTop atTop ∧
    Tendsto (fun j => unitPairs (U j) / ((U j).card : ℝ) ^ exponent)
      atTop atTop

theorem unitPairs_nonneg (U : Finset ℂ) : 0 ≤ unitPairs U := by
  unfold unitPairs
  positivity

theorem orderedUnitPairs_card_le (U : Finset ℂ) :
    (orderedUnitPairs U).card ≤ U.card * U.card := by
  simpa only [orderedUnitPairs, Finset.card_product] using
    (Finset.card_filter_le (s := U ×ˢ U) (p := fun e => dist e.1 e.2 = 1))

theorem unitPairs_le (U : Finset ℂ) : unitPairs U ≤ (U.card : ℝ)^2 / 2 := by
  unfold unitPairs
  gcongr
  exact_mod_cast (show (orderedUnitPairs U).card ≤ U.card ^ 2 by
    simpa only [pow_two] using orderedUnitPairs_card_le U)

@[simp] theorem unitPairs_empty : unitPairs ∅ = 0 := by
  simp [unitPairs, orderedUnitPairs]

end UnitDistance
