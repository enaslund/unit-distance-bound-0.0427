module

public import UnitDistance.IdealScale
public import UnitDistance.RelativeDiscriminant

@[expose] public section
set_option backward.privateInPublic true


/-! # The lattice-scale root discriminant is the actual root discriminant -/

noncomputable section
open NumberField NumberField.InfinitePlace
namespace UnitDistance.EuclideanIdeal
open NumberFieldAnalysis

theorem logarithmicRootDiscriminant_eq_log_rootDiscriminant
    (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K] :
    logarithmicRootDiscriminant K = Real.log (rootDiscriminant K) := by
  rw [rootDiscriminant, Real.log_rpow (absoluteDiscriminant_pos K),
    absoluteDiscriminant_eq_abs, IsTotallyComplex.finrank K]
  simp only [logarithmicRootDiscriminant, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem logarithmicRootDiscriminant_eq_base
    (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] [IsTotallyComplex K] (hunr : FiniteUnramified F K) :
    logarithmicRootDiscriminant K = Real.log (rootDiscriminant F) := by
  rw [logarithmicRootDiscriminant_eq_log_rootDiscriminant,
    rootDiscriminant_eq_of_finiteUnramified F K hunr]

end UnitDistance.EuclideanIdeal
