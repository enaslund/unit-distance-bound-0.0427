module

public import UnitDistance.OddTameFrobenius

@[expose] public section
set_option backward.privateInPublic true


/-! Actual inertia fixes roots of X²−5 in residue characteristic two. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v w x
namespace UnitDistance.DyadicInertia
open RamificationTheory.HilbertRamification.Higher
open ValuationTheory.DiscreteValuationField.ResidueField
open ValuationTheory.DiscreteValuationField

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L] [CharZero L]
  {base : DVF.{u,v} K} {target : DVF.{w,x} L}
  [FiniteDimensional K L] [base.valuation.HasExtension target.valuation] [IsGalois K L]
  (huniq : RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u,v,w,x,x}
    base target)

theorem golden_integral (a : L) (ha : a^2=a+1) :
    a∈target.valuation.valuationSubring := by
  change target.valuation a≤1
  by_contra h
  have hlt : 1<target.valuation a := lt_of_not_ge h
  have hbound : (target.valuation a)^2≤target.valuation a := by
    rw [← map_pow,ha]
    simpa only [map_one,max_eq_left (le_of_lt hlt)] using target.valuation.map_add a 1
  have hs : target.valuation a<(target.valuation a)^2 := by
    rw [pow_two]
    simpa only [mul_one] using mul_lt_mul_of_pos_left hlt (lt_trans zero_lt_one hlt)
  exact (not_lt_of_ge hbound) hs

/-- This argument uses the integral generator (1+√5)/2, whose two conjugate
residues differ by one in characteristic two. -/
theorem inertia_fixes_sqrt_five
    (h2 : (2 : target.residueField)=0)
    (σ : lowerRamificationGroup (base:=base) (target:=target) huniq ((0 : ℕ) : ℝ))
    (r : L) (hr : r^2=5) : (σ : Gal(L/K)) r=r := by
  let a : L := (1+r)/2
  have ha : a^2=a+1 := by dsimp [a]; field_simp; linear_combination hr
  let b : target.valuationSubring := ⟨a,golden_integral a ha⟩
  let f := valuationSubringAutOfUniqueExtension huniq (σ : Gal(L/K))
  have hb : b^2=b+1 := by apply Subtype.ext; exact ha
  have hfb : (f b)^2=f b+1 := by rw [← map_pow,hb,map_add,map_one]
  have hfact : (f b-b)*(f b+b-1)=0 := by linear_combination hfb-hb
  have hres : target.residueMap (f b)=target.residueMap b := by
    have hm := (mem_lowerRamificationGroup_nat_iff huniq 0 (σ : Gal(L/K))).mp σ.property b
    apply sub_eq_zero.mp
    rw [← map_sub,IsLocalRing.residue_eq_zero_iff]
    simpa only [Nat.reduceAdd,pow_one] using hm
  have hfix : f b=b := by
    rcases mul_eq_zero.mp hfact with h | h
    · exact sub_eq_zero.mp h
    · exfalso
      have he := congrArg target.residueMap h
      rw [map_sub,map_add,map_one,map_zero,hres] at he
      have ht : (2 : target.residueField)*target.residueMap b=1 := by linear_combination he
      rw [h2,zero_mul] at ht
      exact zero_ne_one ht
  have hfield : (σ : Gal(L/K)) a=a := congrArg Subtype.val hfix
  change (σ : Gal(L/K)) ((1+r)/2)=(1+r)/2 at hfield
  rw [map_div₀,map_add,map_one,map_ofNat] at hfield
  have := (div_left_inj' (by norm_num : (2 : L)≠0)).mp hfield
  exact add_left_cancel this

end UnitDistance.DyadicInertia
