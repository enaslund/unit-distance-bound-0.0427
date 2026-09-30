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


/-! Exact planar sequence theorem conditional on one explicit numerical
inequality for an independently specified number field. The sole hypothesis
has not been proved. No assertion for every large cardinality is made. -/
/- The imports `CStarAlgebra.Classes` and `SimplexCategory.Basic` and the local
attribute [-instance] instCommCStarAlgebraComplex in exist only so that this Challenge elaborates
the same instance terms as SolutionZeta for Comparator's structural comparison; every instance path
is definitionally the standard one. backward.isDefEq.respectTransparency is elaborator-only. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter NumberField
open scoped Classical BigOperators
namespace UnitDistanceZetaSubmission

attribute [-instance] instCommCStarAlgebraComplex in
/-- Ordered pairs of points of `U` at Euclidean distance one in the complex plane. -/
def orderedUnitPairs (U : Finset ℂ) : Finset (ℂ × ℂ) :=
  (U ×ˢ U).filter (fun e => dist e.1 e.2 = 1)
/-- Number of unordered unit-distance pairs, written as a real number.
Swapping endpoints pairs the ordered edges; distance one excludes the diagonal. -/
def unitPairs (U : Finset ℂ) : ℝ := (orderedUnitPairs U).card / 2
/-- The exact exponent `1.0418235`. -/
def exponent : ℝ := 2083647 / 2000000
/-- The strict upper threshold `0.042165819` for the displayed zeta expression. -/
def ceiling : ℝ := 42165819 / 1000000000
/-- The proved upper bound `(9/4) log 2 + (1/2) log 15015`
for the logarithmic root discriminant of the fixed field. -/
def logRD : ℝ := (9 / 4 : ℝ) * Real.log 2 + (1 / 2 : ℝ) * Real.log 15015

namespace CanonicalRetained
/-- A fixed algebraic closure of the rational numbers. -/
abbrev Closure := AlgebraicClosure ℚ

/-- Choose a square root in the algebraic closure. No ordering or positivity
is intended; the subsequent field construction uses these fixed choices. -/
def squareRoot (a : Closure) : Closure :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq a (by decide : 0<2))

theorem squareRoot_sq (a : Closure) : squareRoot a^2=a :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq a (by decide : 0<2))

/-- The seven rational radicands `-1, 2, 3, 5, 7, 11, 13`, in bit order. -/
def rationalRadicands : Fin 7 → ℚ := ![-1,2,3,5,7,11,13]
/-- Chosen square roots of the seven rational radicands. -/
def genusRoot (i : Fin 7) : Closure := squareRoot (rationalRadicands i)

/-- For each of the seventeen catalog entries, the mask of genus roots
whose product occurs in that entry. Bit zero is the `-1` root. -/
def rootMasks : Fin 17 → ℕ := ![1,41,3,41,41,17,11,34,69,25,97,5,67,7,19,33,1]
/-- Integer constant coefficients of the seventeen catalog radicands. -/
def catalogX : Fin 17 → ℤ := ![4,6,1,1,7,1,1,19,4,1,5,1,1,1,3,3,-2]
/-- Integer coefficients of the genus-root products in the catalog. -/
def catalogY : Fin 17 → ℤ := ![7,1,4,1,1,1,10,2,1,7,1,2,2,8,2,1,3]
/-- Twelve masks selecting products of the seventeen catalog radicands.
Bit zero selects catalog entry zero; all indices use this zero-based order. -/
def wordMasks : Fin 12 → ℕ := ![2,256,512,4096,9,65,132,2052,24576,37,32768,65536]

/-- Product of the genus roots selected by the low seven bits of `m`. -/
def maskRoot (m : ℕ) : Closure :=
  ∏i : Fin 7,if m.testBit i.val then genusRoot i else 1

/-- Catalog entry `x_i + y_i * product(selected genus roots)`. -/
def catalogRadicand (i : Fin 17) : Closure :=
  (catalogX i : Closure)+(catalogY i : Closure)*maskRoot (rootMasks i)

/-- The product of catalog entries selected by retained word `j`. -/
def retainedRadicand (j : Fin 12) : Closure :=
  ∏i : Fin 17,if (wordMasks j).testBit i.val then catalogRadicand i else 1

/-- A chosen square root of retained radicand `j`. -/
def retainedRoot (j : Fin 12) : Closure := squareRoot (retainedRadicand j)

/-- The subfield generated over the rationals by the seven genus roots
and twelve retained roots. The proof identifies its degree as `524288`. -/
def field : IntermediateField ℚ Closure :=
  IntermediateField.adjoin ℚ (Set.range genusRoot ∪ Set.range retainedRoot)

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

theorem genusRoot_sq (i : Fin 7) : genusRoot i^2=(rationalRadicands i : Closure) :=
  squareRoot_sq _

theorem retainedRoot_sq (j : Fin 12) : retainedRoot j^2=retainedRadicand j := squareRoot_sq _

theorem genusRoot_mem (i : Fin 7) : genusRoot i∈field :=
  IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨i,rfl⟩)

theorem retainedRoot_mem (j : Fin 12) : retainedRoot j∈field :=
  IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨j,rfl⟩)

end CanonicalRetained

/-- Conditional planar unit-distance theorem. The displayed inequality for
this one fixed number field is the sole hypothesis and remains unproved.
The conclusion gives a sequence with cardinalities and normalized unordered
unit-pair counts both tending to infinity; it makes no all-cardinalities claim. -/
theorem target_of_canonical_zeta_bound
    (hfinite : Real.log (dedekindZeta CanonicalRetained.Carrier
          ((1+(1/12000:ℝ):ℝ):ℂ)).re / (524288 : ℝ) + (1/12000:ℝ)*
        ((logRD-Real.eulerMascheroniConstant-Real.log (4*Real.pi))/4-
          (logDeriv (dedekindZeta CanonicalRetained.Carrier) 2).re/(524288 : ℝ)) < ceiling) :
    ∃ U : ℕ → Finset ℂ,
      Tendsto (fun j => (U j).card) atTop atTop ∧
      Tendsto (fun j => unitPairs (U j) / ((U j).card : ℝ) ^ exponent) atTop atTop := by
  sorry


end UnitDistanceZetaSubmission
