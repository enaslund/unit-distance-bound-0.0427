module

public import UnitDistance.Sqrt241.CanonicalGenus

@[expose] public section
set_option backward.privateInPublic true


/-!
# The field `E_W` of four D4 forms over `ℚ(√241)`

Library copy of the definitions that a Challenge statement uses for the field `E_W`
(papers/0.043171, Sections 8, 11b, 11c): the genus field `E` (`CanonicalGenus.field`)
adjoined square roots of four elements `β_i` of `E`. Each `β_i` lies in
`B(√a_i, √b_i)`, where `√a_i = rootA i` and `√b_i = rootB i` are products of genus roots;
`B(√a_i, √b_i, √β_i)` is the D4 field of the form `24, 20, 17, 7` (in this order) of
`d4all27.json`. The four forms span the space `W''` of dimension four, and `E_W` has degree
`512 · 16 = 8192`.

Each `β_i` is written in the basis `1, s, x, s x, y, s y, x y, s x y` with `s = √241`,
`x = rootA i`, `y = rootB i`, with integer coordinates.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical

namespace UnitDistance.Sqrt241.CanonicalWide
open CanonicalGenus

/-- `√a_i`: the product of the genus roots in the first row of the form. -/
def rootA : Fin 4 → Closure :=
  ![genusRoot 1 * genusRoot 3 * genusRoot 4 * genusRoot 5 * genusRoot 6 * genusRoot 7,
    genusRoot 1 * genusRoot 4 * genusRoot 5,
    genusRoot 1 * genusRoot 5 * genusRoot 6,
    genusRoot 4 * genusRoot 6]

/-- `√b_i`: the product of the genus roots in the second row of the form. -/
def rootB : Fin 4 → Closure :=
  ![genusRoot 0 * genusRoot 3 * genusRoot 4,
    genusRoot 0 * genusRoot 3 * genusRoot 7,
    genusRoot 0 * genusRoot 4,
    genusRoot 0 * genusRoot 1 * genusRoot 5]

/-- The four radicands `β_i ∈ E`. -/
def wideRadicand : Fin 4 → Closure :=
  ![-13151840112 + 847184400 * baseRoot - 31727062200 * (rootA 0 * rootB 0) -
      2043719736 * baseRoot * (rootA 0 * rootB 0),
    -1118796 + 72068 * baseRoot - 164 * rootA 1 - 4 * baseRoot * rootA 1 - 76752 * rootB 1 +
      4944 * baseRoot * rootB 1 + 240 * (rootA 1 * rootB 1) + 16 * baseRoot * (rootA 1 * rootB 1),
    -156 + 10 * baseRoot - 3850 * rootA 2 - 248 * baseRoot * rootA 2,
    -130434 + 8402 * baseRoot - 646 * rootA 3 + 42 * baseRoot * rootA 3]

/-- Chosen square roots `√β_i` in the closure. -/
def wideRoot (i : Fin 4) : Closure := squareRoot (wideRadicand i)

/-- `E_W`: the subfield generated over the rationals by `√241`, the eight genus roots and the
four roots `√β_i`. -/
def field : IntermediateField ℚ Closure :=
  IntermediateField.adjoin ℚ (insert baseRoot (Set.range genusRoot ∪ Set.range wideRoot))

/-- The carrier field. -/
abbrev Carrier := field

attribute [local instance 2000] AddSubgroupClass.toAddSubmonoidClass in
/-- Finitely many algebraic generators give a finite-dimensional extension. -/
instance finite : Module.Finite ℚ Carrier := by
  apply IntermediateField.finiteDimensional_adjoin
  intro x _
  exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral

/-- The field `E_W` with its number-field structure. -/
instance numberField : NumberField Carrier where
  to_finiteDimensional := finite

theorem wideRoot_sq (i : Fin 4) : wideRoot i ^ 2 = wideRadicand i := squareRoot_sq _

end UnitDistance.Sqrt241.CanonicalWide
