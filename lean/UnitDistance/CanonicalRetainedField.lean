module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Tactic

@[expose] public section
set_option backward.privateInPublic true


/-! An independently specified finite field: nineteen explicit radicals in
an algebraic closure of the rationals. Only Mathlib is imported here. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace UnitDistance.CanonicalRetained
abbrev Closure := AlgebraicClosure ℚ

def squareRoot (a : Closure) : Closure :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq a (by decide : 0<2))

theorem squareRoot_sq (a : Closure) : squareRoot a^2=a :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq a (by decide : 0<2))

def rationalRadicands : Fin 7 → ℚ := ![-1,2,3,5,7,11,13]
def genusRoot (i : Fin 7) : Closure := squareRoot (rationalRadicands i)

def rootMasks : Fin 17 → ℕ := ![1,41,3,41,41,17,11,34,69,25,97,5,67,7,19,33,1]
def catalogX : Fin 17 → ℤ := ![4,6,1,1,7,1,1,19,4,1,5,1,1,1,3,3,-2]
def catalogY : Fin 17 → ℤ := ![7,1,4,1,1,1,10,2,1,7,1,2,2,8,2,1,3]
def wordMasks : Fin 12 → ℕ := ![2,256,512,4096,9,65,132,2052,24576,37,32768,65536]

def maskRoot (m : ℕ) : Closure :=
  ∏i : Fin 7,if m.testBit i.val then genusRoot i else 1

def catalogRadicand (i : Fin 17) : Closure :=
  (catalogX i : Closure)+(catalogY i : Closure)*maskRoot (rootMasks i)

def retainedRadicand (j : Fin 12) : Closure :=
  ∏i : Fin 17,if (wordMasks j).testBit i.val then catalogRadicand i else 1

def retainedRoot (j : Fin 12) : Closure := squareRoot (retainedRadicand j)

def field : IntermediateField ℚ Closure :=
  IntermediateField.adjoin ℚ (Set.range genusRoot ∪ Set.range retainedRoot)

abbrev Carrier := field

instance finite : Module.Finite ℚ Carrier := by
  apply IntermediateField.finiteDimensional_adjoin
  intro x _
  exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral

instance numberField : NumberField Carrier where
  to_finiteDimensional := finite

theorem genusRoot_sq (i : Fin 7) : genusRoot i^2=(rationalRadicands i : Closure) :=
  squareRoot_sq _

theorem retainedRoot_sq (j : Fin 12) : retainedRoot j^2=retainedRadicand j := squareRoot_sq _

theorem genusRoot_mem (i : Fin 7) : genusRoot i∈field :=
  IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨i,rfl⟩)

theorem retainedRoot_mem (j : Fin 12) : retainedRoot j∈field :=
  IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨j,rfl⟩)

end UnitDistance.CanonicalRetained
