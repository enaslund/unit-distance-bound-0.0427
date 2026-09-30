module

public import UnitDistance.PadicOddIntrinsicInertia

@[expose] public section
set_option backward.privateInPublic true


/-! The reverse comparison identifies every intrinsic inertia automorphism
with an actual tame inertia automorphism after change of completion base. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ValuativeRel
namespace UnitDistance.PadicOddGenus
open RamificationTheory.HilbertRamification.Higher
open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
attribute [local instance] oddPrime

variable (i : Fin 5) (L : Type) [Field L] [Algebra ℚ_[PadicOdd.primes i] L]
  [FiniteDimensional ℚ_[PadicOdd.primes i] L] [IsGalois ℚ_[PadicOdd.primes i] L]
  [ValuativeRel L] [(target i L).valuation.Compatible]
  (K : Type) [Field K] [ValuativeRel K] [Algebra K L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L]

theorem inertia_mem_of_intrinsic (τ : Gal(L/ℚ_[PadicOdd.primes i])) (σ : Gal(L/K))
    (hσ : ∀x : L,σ x=τ x)
    (hI : σ∈(galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker) :
    τ∈inertia i L := by
  rw [galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_sub_mem_maximalIdeal] at hI
  rw [mem_lowerRamificationGroup_nat_iff (unique i L) 0]
  intro x
  have hx : (ValuativeRel.valuation L) (x : L)≤1 := by
    have he := ValuativeRel.isEquiv (target i L).valuation (ValuativeRel.valuation L) (x : L) 1
    simp only [map_one] at he
    exact he.mp x.property
  let xO : 𝒪[L] := ⟨(x : L),hx⟩
  have hd := hI xO
  change ¬IsUnit (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ xO-xO) at hd
  rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one] at hd
  have hd' : (ValuativeRel.valuation L) (σ (x : L)-(x : L))<1 := hd
  rw [hσ] at hd'
  have he := (ValuativeRel.isEquiv (ValuativeRel.valuation L) (target i L).valuation).lt_iff_lt
    (x:=τ (x : L)-(x : L)) (y:=1)
  simp only [map_one] at he
  have hm : valuationSubringAutOfUniqueExtension (unique i L) τ x-x∈(target i L).maximalIdeal :=
    (target i L).mem_maximalIdeal_iff _ |>.mpr (he.mp hd')
  simpa only [Nat.reduceAdd,pow_one] using hm

end UnitDistance.PadicOddGenus
