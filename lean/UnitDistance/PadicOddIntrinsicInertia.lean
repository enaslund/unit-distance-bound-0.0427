module

public import UnitDistance.PadicOddTamePair
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois

@[expose] public section
set_option backward.privateInPublic true


/-! Compatibility of the actual tame inertia with the intrinsic residue
inertia used by local class field theory, including a change of base field. -/
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

/-- The same field automorphism is in intrinsic inertia whenever its actual
p-adic tame action is in inertia and the valuations are compatible. -/
theorem inertia_mem_intrinsic (τ : inertia i L) (σ : Gal(L/K))
    (hσ : ∀ x : L, σ x=(τ : Gal(L/ℚ_[PadicOdd.primes i])) x) :
    σ∈(galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker := by
  rw [galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_sub_mem_maximalIdeal]
  intro x
  have hx : (target i L).valuation (x : L)≤1 := by
    have h := (ValuativeRel.isEquiv (ValuativeRel.valuation L) (target i L).valuation) (x : L) 1
    simpa only [map_one] using h.mp x.property
  have hτ := (mem_lowerRamificationGroup_nat_iff (unique i L) 0 _).mp τ.property
  have hdiff := hτ ⟨(x : L),hx⟩
  have hlt : (target i L).valuation ((τ : Gal(L/ℚ_[PadicOdd.primes i])) (x : L)-(x : L))<1 := by
    have hm : (valuationSubringAutOfUniqueExtension (unique i L) (τ : Gal(L/ℚ_[PadicOdd.primes i]))) ⟨(x : L),hx⟩-⟨(x : L),hx⟩ ∈ (target i L).maximalIdeal := by
      simpa only [Nat.reduceAdd,pow_one] using hdiff
    exact (target i L).mem_maximalIdeal_iff _ |>.mp hm
  change ¬ IsUnit (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x-x)
  rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  change (ValuativeRel.valuation L) (σ (x : L)-(x : L))<1
  rw [hσ]
  have h := (ValuativeRel.isEquiv (target i L).valuation (ValuativeRel.valuation L)).lt_iff_lt
    (x := (τ : Gal(L/ℚ_[PadicOdd.primes i])) (x : L)-(x : L)) (y := 1)
  simp only [map_one] at h
  exact h.mp hlt

end UnitDistance.PadicOddGenus
