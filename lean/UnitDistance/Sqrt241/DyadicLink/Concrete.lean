module

public import UnitDistance.Sqrt241.DyadicLink.RetainedField
public import UnitDistance.Sqrt241.Levels.Unramified

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# `hdiscM` for the concrete retained field

For the concrete input `Retained.input` (built from `Local.localElements`), `Levels/`
supplies the ramification indices of `M = Retained.input.M`: `e = 8, 2, 2` at `2, 3, 5`
(`Retained.Input.Admissible.local_types` with `admissible_M`), `e = 2` at `241`
(`Retained.ramificationIdxIn_241`) and `e = 1` elsewhere
(`Retained.ramificationIdxIn_eq_one_away`). With `√β₁ ∈ M` this gives the root
discriminant bound `hdiscM` of `target_of_tower_data` without hypotheses.
-/

open scoped NumberField
open NumberField

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.DyadicLink

open UnitDistance.NumberFieldAnalysis

/-- **`hdiscM`** for the retained field `M = Retained.input.M`:
`log rd(M) ≤ (9/4) log 2 + (1/2) log 3615`. -/
theorem log_rootDiscriminant_input_M :
    Real.log (rootDiscriminant Retained.input.M) ≤ Witness.logRD := by
  have hM := Retained.input.admissible_M
  have ht := Retained.Input.Admissible.local_types hM
  refine log_rootDiscriminant_input_M_le (ht 0).1 (ht 1).1 (ht 2).1
    (Retained.ramificationIdxIn_241 _ (Retained.BinOmega_le_of_admissible hM)) ?_
  intro p hp hmem
  exact Retained.ramificationIdxIn_eq_one_away _ ⟨p, hp⟩ hmem

end UnitDistance.Sqrt241.DyadicLink
