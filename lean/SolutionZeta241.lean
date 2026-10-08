module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Data.Finset.Prod
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.Order.Filter.AtTopBot.Tendsto
public import UnitDistance.Sqrt241.V2.Final

@[expose] public section
set_option backward.privateInPublic true


/-! Planar unit-distance sequence theorem at exponent `20863/20000 = 1.04315`,
conditional on one explicit numerical inequality for an independently specified
number field `E_W` of degree 8192. Let `B = ℚ(√241)` and let
`E = B(√α₀, …, √α₇)`, with `α₀, …, α₇` a basis of the `{2,3,5}`-units of `B`
modulo squares, be the maximal elementary abelian 2-extension of `B` unramified
outside `2, 3, 5` and the infinite places (degree 512). Then `E_W = E(√β₁, …, √β₄)`
for four explicit elements `β_i ∈ E`, written below in terms of `√241` and products
of the square roots `√α_k`; each `B(√a_i, √b_i, √β_i)` is a dihedral extension of
degree 8 of `B`. The hypothesis is one displayed inequality for the Dedekind zeta
function of `E_W` near `s = 1 + 1/4411` and its logarithmic derivative at `s = 2`.
It is not proved in Lean. No assertion for every large cardinality is made. -/
/- The imports `CStarAlgebra.Classes` and `SimplexCategory.Basic`, the local
attribute `[-instance] instCommCStarAlgebraComplex`, the `backward.*` options
and the instance priority below are inherited unchanged from the earlier
challenge of the same form, so that the two statements elaborate in the same
way; they do not change the meaning of any definition or of the theorem. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter NumberField
open scoped Classical
namespace UnitDistanceSqrt241Submission

attribute [-instance] instCommCStarAlgebraComplex in
/-- Ordered pairs of points of `U` at Euclidean distance one in the complex plane. -/
def orderedUnitPairs (U : Finset ℂ) : Finset (ℂ × ℂ) :=
  (U ×ˢ U).filter (fun e => dist e.1 e.2 = 1)
/-- Number of unordered unit-distance pairs, written as a real number.
Swapping endpoints pairs the ordered edges; distance one excludes the diagonal. -/
def unitPairs (U : Finset ℂ) : ℝ := (orderedUnitPairs U).card / 2
/-- The exact exponent `1.04315`. -/
def exponent : ℝ := 20863 / 20000
/-- The strict upper threshold `0.050969` for the displayed zeta expression. -/
def ceiling : ℝ := 50969 / 1000000
/-- `ℓ = log(√241 · 2^(9/4) · √15) = (9/4) log 2 + (1/2) log 3615`. In the proof this
bounds the logarithmic root discriminant of the fields of the tower over `ℚ(√241)`. -/
def logRD : ℝ := (9 / 4 : ℝ) * Real.log 2 + (1 / 2 : ℝ) * Real.log 3615

namespace CanonicalGenus
/-- A fixed algebraic closure of the rational numbers. -/
abbrev Closure := AlgebraicClosure ℚ

/-- Choose a square root in the algebraic closure. No ordering or positivity
is intended. Other choices of the square roots below replace the field `E_W` by its
image under an automorphism of the algebraic closure, an isomorphic field with the
same Dedekind zeta function, so the displayed inequality does not depend on them. -/
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

end CanonicalGenus

namespace CanonicalWide
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

end CanonicalWide

/-- Conditional planar unit-distance theorem at exponent `1.04315`. The
displayed inequality for this one fixed number field is the sole hypothesis
and remains unproved. The conclusion gives a sequence with cardinalities and
normalized unordered unit-pair counts both tending to infinity; it makes no
all-cardinalities claim. -/
theorem target_of_wide_zeta_bound
    (hfinite : Real.log (dedekindZeta CanonicalWide.Carrier
          ((1+(1/4411:ℝ):ℝ):ℂ)).re / (8192 : ℝ) + (1/4411:ℝ)*
        ((logRD-Real.eulerMascheroniConstant-Real.log (4*Real.pi))/4-
          (logDeriv (dedekindZeta CanonicalWide.Carrier) 2).re/(8192 : ℝ)) < ceiling) :
    ∃ U : ℕ → Finset ℂ,
      Tendsto (fun j => (U j).card) atTop atTop ∧
      Tendsto (fun j => unitPairs (U j) / ((U j).card : ℝ) ^ exponent) atTop atTop := by
  exact UnitDistance.Sqrt241.V2.target_of_wide_zeta_bound hfinite


end UnitDistanceSqrt241Submission
