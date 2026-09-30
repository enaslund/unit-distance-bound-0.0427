module

public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups

@[expose] public section
set_option backward.privateInPublic true


/-! The intrinsic residue inertia equals actual degree-zero ramification
for any compatible discrete valuation on the same finite field. -/
noncomputable section
open scoped ValuativeRel
namespace UnitDistance.ArithmeticProP
open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
open RamificationTheory.HilbertRamification.Higher
open ValuationTheory.DiscreteValuationField

variable (K L : Type) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L]
  (base : DVF.{0,0} K) (target : DVF.{0,0} L)
  [base.valuation.HasExtension target.valuation] [target.valuation.Compatible]
  (huniq : RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension base target)

/-- Membership in intrinsic residue inertia is the actual maximal-ideal
displacement condition for a compatible discrete valuation. -/
theorem intrinsicInertia_iff_lowerRamification_zero (σ : Gal(L/K)) :
    σ ∈ (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker ↔
      σ ∈ lowerRamificationGroup (base := base) (target := target) huniq ((0 : ℕ) : ℝ) := by
  rw [galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_sub_mem_maximalIdeal,
    mem_lowerRamificationGroup_nat_iff]
  simp only [Nat.reduceAdd,pow_one]
  constructor
  · intro h x
    have hx : (ValuativeRel.valuation L) (x : L) ≤ 1 := by
      have he := (ValuativeRel.isEquiv target.valuation (ValuativeRel.valuation L)) (x : L) 1
      simp only [map_one] at he
      exact he.mp x.property
    let xO : 𝒪[L] := ⟨(x : L),hx⟩
    have hd := h xO
    change ¬IsUnit (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ xO-xO) at hd
    rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one] at hd
    have hd' : (ValuativeRel.valuation L) (σ (x : L)-(x : L)) < 1 := hd
    apply (target.mem_maximalIdeal_iff _).mpr
    change target.valuation (σ (x : L)-(x : L)) < 1
    have he := (ValuativeRel.isEquiv (ValuativeRel.valuation L) target.valuation).lt_iff_lt
      (x := σ (x : L)-(x : L)) (y := 1)
    simp only [map_one] at he
    exact he.mp hd'
  · intro h x
    have hx : target.valuation (x : L) ≤ 1 := by
      have he := (ValuativeRel.isEquiv (ValuativeRel.valuation L) target.valuation) (x : L) 1
      simp only [map_one] at he
      exact he.mp x.property
    let xT : target.valuationSubring := ⟨(x : L),hx⟩
    have hd := (target.mem_maximalIdeal_iff _).mp (h xT)
    have hd' : target.valuation (σ (x : L)-(x : L)) < 1 := hd
    change ¬IsUnit (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x-x)
    rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    change (ValuativeRel.valuation L) (σ (x : L)-(x : L)) < 1
    have he := (ValuativeRel.isEquiv target.valuation (ValuativeRel.valuation L)).lt_iff_lt
      (x := σ (x : L)-(x : L)) (y := 1)
    simp only [map_one] at he
    exact he.mp hd'

end UnitDistance.ArithmeticProP
