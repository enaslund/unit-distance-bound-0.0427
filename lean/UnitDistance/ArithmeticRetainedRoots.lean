module

public import UnitDistance.ArithmeticRetainedField
public import UnitDistance.ArithmeticCompletedField
public import UnitDistance.QuadraticSevenConjugation

@[expose] public section
set_option backward.privateInPublic true


/-! Actual displayed roots of minus one and seven in the finite arithmetic
fields, and their images in arbitrary actual overfields. -/
noncomputable section
namespace UnitDistance.ArithmeticRetained
open ArithmeticChosenGenus

def imaginaryUnit : RetainedField := algebraMap GenusField RetainedField (roots 0)
def sevenRoot : RetainedField := algebraMap GenusField RetainedField (roots 4)

theorem imaginaryUnit_sq : imaginaryUnit^2=(-1 : RetainedField) := by
  rw [imaginaryUnit,← map_pow,roots_sq]
  norm_num [radicands]

theorem sevenRoot_sq : sevenRoot^2=(7 : RetainedField) := by
  have h : radicands (4 : Fin 7)=(7 : ℚ) := by decide +kernel
  rw [sevenRoot,← map_pow,roots_sq,h,map_ratCast]
  norm_num

variable (K : Type*) [Field K] [Algebra RetainedField K]

def imaginaryUnitIn : K := algebraMap RetainedField K imaginaryUnit
def sevenRootIn : K := algebraMap RetainedField K sevenRoot

theorem imaginaryUnitIn_sq : (imaginaryUnitIn K)^2=(-1 : K) := by
  rw [imaginaryUnitIn,← map_pow,imaginaryUnit_sq,map_neg,map_one]

theorem sevenRootIn_sq : (sevenRootIn K)^2=(7 : K) := by
  rw [sevenRootIn,← map_pow,sevenRoot_sq,map_ofNat]

variable [NumberField K]

theorem conjugation_fixes_sevenRoot (φ : K →+* ℂ) (c : Gal(K/ℚ))
    (hc : NumberField.ComplexEmbedding.IsConj φ c) :
    c (sevenRootIn K)=sevenRootIn K :=
  QuadraticSeven.conjugation_fixes_root φ c hc (sevenRootIn K) (sevenRootIn_sq K)

end UnitDistance.ArithmeticRetained
