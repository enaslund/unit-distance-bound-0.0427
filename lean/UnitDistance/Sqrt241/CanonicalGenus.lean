module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section
set_option backward.privateInPublic true


/-!
# The canonical genus field of the tower over `ℚ(√241)`

Library copy of the `CanonicalGenus` definitions of `ChallengeZeta241.lean`,
with identical bodies, so that the library theorem and the challenge statement
elaborate to definitionally equal terms. `field` is ℚ adjoined with a chosen
`√241` and chosen square roots of the eight Kummer radicands
`-1, ε, π₂, π₂', π₃, π₃', π₅, π₅'` of `ℚ(√241)`; its degree is 512.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical

namespace UnitDistance.Sqrt241.CanonicalGenus
/-- A fixed algebraic closure of the rational numbers. -/
abbrev Closure := AlgebraicClosure ℚ

/-- Choose a square root in the algebraic closure. No ordering or positivity
is intended. The field below does not depend on these choices: replacing `√241`
by `−√241` maps each radicand to a product of radicands times a square, so the
span of the radicands modulo squares is stable. -/
def squareRoot (a : Closure) : Closure :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq a (by decide : 0<2))

theorem squareRoot_sq (a : Closure) : squareRoot a^2=a :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq a (by decide : 0<2))

/-- A chosen square root of `241`. -/
def baseRoot : Closure := squareRoot 241

/-- Rational parts of the eight Kummer radicands `a + b·√241`:
`-1`, a fundamental unit `-71011068 + 4574225√241` (norm `-1`), generators
of the two primes above `2` (norm `-2`), above `3` (norm `-3`) and above `5`
(norm `-5`). -/
def radicandA : Fin 8 → ℚ := ![-1, -71011068, -6101/2, 6101/2, 31, 31, 326, 326]
/-- Coefficients of `√241` in the eight Kummer radicands. -/
def radicandB : Fin 8 → ℚ := ![0, 4574225, -393/2, -393/2, -2, 2, -21, 21]

/-- The Kummer radicand `a_i + b_i·√241` in the closure. -/
def radicand (i : Fin 8) : Closure :=
  (radicandA i : Closure) + (radicandB i : Closure) * baseRoot

/-- Chosen square roots of the eight radicands. -/
def genusRoot (i : Fin 8) : Closure := squareRoot (radicand i)

/-- The subfield generated over the rationals by `√241` and the eight
genus roots. The proof identifies its degree as `512`. -/
def field : IntermediateField ℚ Closure :=
  IntermediateField.adjoin ℚ (insert baseRoot (Set.range genusRoot))

/-- The carrier field of the explicitly generated intermediate field. -/
abbrev Carrier := field

-- Keep the implicit additive structure identical across Challenge and Solution imports.
attribute [local instance 2000] AddSubgroupClass.toAddSubmonoidClass in
/-- Finitely many algebraic generators give a finite-dimensional extension. -/
instance finite : Module.Finite ℚ Carrier := by
  apply IntermediateField.finiteDimensional_adjoin
  intro x _
  exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral

/-- The fixed generated field, with its number-field structure. -/
instance numberField : NumberField Carrier where
  to_finiteDimensional := finite

theorem baseRoot_sq : baseRoot^2=(241 : Closure) := squareRoot_sq _

theorem genusRoot_sq (i : Fin 8) : genusRoot i^2=radicand i := squareRoot_sq _

theorem baseRoot_mem : baseRoot∈field :=
  IntermediateField.subset_adjoin ℚ _ (Set.mem_insert _ _)

theorem genusRoot_mem (i : Fin 8) : genusRoot i∈field :=
  IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem _ ⟨i,rfl⟩)

end UnitDistance.Sqrt241.CanonicalGenus
