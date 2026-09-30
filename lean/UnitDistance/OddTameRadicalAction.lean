module

public import UnitDistance.OddTameFrobenius

@[expose] public section
set_option backward.privateInPublic true


/-! Recovering actual signs on integral quadratic radicals from their residues. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w x
namespace UnitDistance.OddTame
open RamificationTheory.HilbertRamification.Higher
open ValuationTheory.DiscreteValuationField.ResidueField

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
  {base : ValuationTheory.DiscreteValuationField.DVF.{u,v} K}
  {target : ValuationTheory.DiscreteValuationField.DVF.{w,x} L}
  [FiniteDimensional K L] [base.valuation.HasExtension target.valuation] [IsGalois K L]
  (huniq : RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u,v,w,x,x}
    base target)

theorem squareRoot_eq_of_residue_eq
    (h2 : (2 : target.residueField)≠0)
    (a b : target.valuationSubring) (ha : target.residueMap a≠0)
    (hsq : b^2=a^2) (hres : target.residueMap b=target.residueMap a) : b=a := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  · exfalso
    have hsum : (2 : target.residueField)*target.residueMap a=0 := by
      rw [h,map_neg] at hres
      linear_combination -hres
    exact (mul_ne_zero h2 ha) hsum

theorem inertia_fixes_unit_radical
    (h2 : (2 : target.residueField)≠0)
    (σ : lowerRamificationGroup (base:=base) (target:=target) huniq ((0 : ℕ) : ℝ))
    (a : target.valuationSubringˣ) (d : ℤ) (ha : (a : target.valuationSubring)^2=d) :
    valuationSubringAutOfUniqueExtension huniq (σ : Gal(L/K)) a = a := by
  apply squareRoot_eq_of_residue_eq h2 _ _
  · exact Units.ne_zero (residueUnit a)
  · rw [← map_pow, ha, map_intCast]
  · exact congrArg Units.val (residueUnit_aut_of_inertia huniq σ a)

/-- Euler's residue calculation determines the actual sign on a unit radical. -/
theorem frobenius_unit_radical
    (h2 : (2 : target.residueField)≠0)
    (q k : ℕ) (hq : q=2*k+1) (φ : Gal(L/K))
    (hφ : ∀ a : target.valuationSubringˣ,
      residueUnit (dvfValuationSubringUnitAut huniq φ a)=(residueUnit a)^q)
    (a : target.valuationSubringˣ) (d ε : ℤ)
    (ha : (a : target.valuationSubring)^2=d)
    (he : ε=1 ∨ ε= -1)
    (hd : (d : target.residueField)^k=ε) :
    valuationSubringAutOfUniqueExtension huniq φ a = ε*(a : target.valuationSubring) := by
  have hε : (ε : target.residueField)≠0 := by rcases he with rfl | rfl <;> norm_num
  apply squareRoot_eq_of_residue_eq h2 _ _
  · simpa using mul_ne_zero hε (Units.ne_zero (residueUnit a))
  · rw [← map_pow, ha, map_intCast, mul_pow, ha]
    rcases he with rfl | rfl <;> simp
  · have hres := congrArg Units.val (hφ a)
    change target.residueMap (valuationSubringAutOfUniqueExtension huniq φ a)=
      (target.residueMap a)^q at hres
    rw [hres, map_mul, map_intCast, hq, pow_add, pow_mul, pow_one,
      ← map_pow, ha, map_intCast, hd]

end UnitDistance.OddTame
