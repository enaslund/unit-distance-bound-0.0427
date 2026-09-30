module

public import UnitDistance.Sqrt241.DyadicLink.Radical
public import UnitDistance.Sqrt241.DyadicLink.Kummer
public import UnitDistance.Sqrt241.DyadicLink.Comparison
public import UnitDistance.Sqrt241.DyadicLink.RetainedField
public import UnitDistance.Sqrt241.DyadicLink.Concrete

@[expose] public section
set_option backward.privateInPublic true

/-!
# The dyadic link `√β₁ ∈ M` (umbrella)

`√β₁ ∈ Ω` (`Radical`), the Kummer cocycle of `√β₁` on `G_B` (`Kummer`), its factorization
through the retained quotient `Q_B` (`Comparison`), `√β₁ ∈ M` with the root
discriminant bound `hdiscM` from the ramification indices of `M` (`RetainedField`), and
the unconditional `hdiscM` for the concrete `Retained.input.M` with the ramification
indices computed in `Levels/` (`Concrete`). See `docs/sqrt241/T11_LINK.md`.
-/
