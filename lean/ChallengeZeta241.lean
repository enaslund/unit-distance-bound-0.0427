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

@[expose] public section
set_option backward.privateInPublic true


/-! Planar unit-distance sequence theorem at exponent `10427/10000 = 1.0427`,
conditional on one explicit numerical inequality for an independently specified
number field `E` of degree 512: `E = B(√α₀, …, √α₇)` with `B = ℚ(√241)` and
`α₀, …, α₇` a basis of the `{2,3,5}`-units of `B` modulo squares, i.e. the
maximal elementary abelian 2-extension of `B` unramified outside `2, 3, 5` and
the infinite places. The hypothesis is one displayed inequality for the
Dedekind zeta function of `E` near `s = 1 + 1/300` and its logarithmic
derivative at `s = 2`. It is not proved in Lean. No assertion for every large
cardinality is made. -/
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
/-- The exact exponent `1.0427`. -/
def exponent : ℝ := 10427 / 10000
/-- The strict upper threshold `0.0852` for the displayed zeta expression. -/
def ceiling : ℝ := 852 / 10000
/-- `ℓ = log(√241 · 2^(9/4) · √15) = (9/4) log 2 + (1/2) log 3615`. In the proof this
bounds the logarithmic root discriminant of the fields of the tower over `ℚ(√241)`
(it exceeds `log rd(E) = 2 log 2 + (1/2) log 3615`). -/
def logRD : ℝ := (9 / 4 : ℝ) * Real.log 2 + (1 / 2 : ℝ) * Real.log 3615

namespace CanonicalGenus
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

end CanonicalGenus

/-- Conditional planar unit-distance theorem at exponent `1.0427`. The
displayed inequality for this one fixed number field is the sole hypothesis
and remains unproved. The conclusion gives a sequence with cardinalities and
normalized unordered unit-pair counts both tending to infinity; it makes no
all-cardinalities claim. -/
theorem target_of_canonical_genus_zeta_bound
    (hfinite : Real.log (dedekindZeta CanonicalGenus.Carrier
          ((1+(1/300:ℝ):ℝ):ℂ)).re / (512 : ℝ) + (1/300:ℝ)*
        ((logRD-Real.eulerMascheroniConstant-Real.log (4*Real.pi))/4-
          (logDeriv (dedekindZeta CanonicalGenus.Carrier) 2).re/(512 : ℝ)) < ceiling) :
    ∃ U : ℕ → Finset ℂ,
      Tendsto (fun j => (U j).card) atTop atTop ∧
      Tendsto (fun j => unitPairs (U j) / ((U j).card : ℝ) ^ exponent) atTop atTop := by
  sorry


end UnitDistanceSqrt241Submission
