module

public import UnitDistance.SigmaGeneratorRank
public import UnitDistance.ClassTwoCollection

@[expose] public section
set_option backward.privateInPublic true


/-! Actual generators of the maximal six-prime pro-two group, with specified
actions on the seven genus radicals. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.ArithmeticProP
open ArithmeticGenusFrattini ClassFieldTower.ProP
open ProCGroups.Generation ProCGroups.FiniteGeneration

def sigmaGenusRestriction : Gal(maximalSigmaProTwo/ℚ) →ₜ* VectorGroup :=
  genusRestriction genusInMaximal genusInMaximalEquiv

theorem sigmaGenusRestriction_surjective : Function.Surjective sigmaGenusRestriction :=
  genusRestriction_surjective genusInMaximal genusInMaximalEquiv

theorem sigmaGenusRestriction_ker :
    sigmaGenusRestriction.toMonoidHom.ker = closedPowerCommutator 2 Gal(maximalSigmaProTwo/ℚ) :=
  (genusRestriction_ker genusInMaximal genusInMaximalEquiv).trans
    maximalSigmaProTwo_frattini.symm

def genusBasis (i : Fin 7) : VectorGroup := Multiplicative.ofAdd (Pi.single i 1)

theorem genusBasis_generates : TopologicallyGenerates (Set.range genusBasis) := by
  classical
  have htop : Subgroup.closure (Set.range genusBasis) = ⊤ := by
    apply top_unique
    intro v _
    have hv : v = ∏ i : Fin 7, Multiplicative.ofAdd (Pi.single i (v.toAdd i)) := by
      rw [← ofAdd_sum, Finset.univ_sum_single]
      rfl
    rw [hv]
    apply Subgroup.prod_mem
    intro i _
    rcases ClassTwo.Collection.binary_cases (v.toAdd i) with hi | hi
    · rw [hi, Pi.single_zero]
      exact Subgroup.one_mem _
    · rw [hi]
      exact Subgroup.subset_closure ⟨i, rfl⟩
  simp [TopologicallyGenerates, htop]

/-- Any actual lifts of the seven genus basis vectors generate the entire
maximal extension's Galois group. -/
theorem sigmaGenerators_of_genusBasis (x : Fin 7 → Gal(maximalSigmaProTwo/ℚ))
    (hx : ∀ i, sigmaGenusRestriction (x i) = genusBasis i) :
    TopologicallyGenerates (Set.range x) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : (closedPowerCommutator 2 Gal(maximalSigmaProTwo/ℚ)).Normal :=
    closedPowerCommutator_normal 2 _
  let e : powerCommutatorQuotient 2 Gal(maximalSigmaProTwo/ℚ) ≃* VectorGroup :=
    QuotientGroup.liftEquiv _ sigmaGenusRestriction_surjective sigmaGenusRestriction_ker.symm
  have heval (g : Gal(maximalSigmaProTwo/ℚ)) :
      e (powerCommutatorQuotientMk 2 Gal(maximalSigmaProTwo/ℚ) g) =
        sigmaGenusRestriction g := rfl
  have hgen := topologicallyGenerates_image_of_continuousSurjective
    e.symm.toMonoidHom continuous_of_discreteTopology e.symm.surjective genusBasis_generates
  change TopologicallyGenerates (e.symm '' Set.range genusBasis) at hgen
  apply (topologicallyGenerates_iff_powerCommutatorQuotient_image
    maximalSigmaProTwo_hasPGroupOpenNormalBasis).mpr
  have himage : e.symm '' Set.range genusBasis =
      powerCommutatorQuotientMk 2 Gal(maximalSigmaProTwo/ℚ) '' Set.range x := by
    ext a
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      refine ⟨x i, ⟨i, rfl⟩, ?_⟩
      apply e.injective
      simpa only [e.apply_symm_apply, heval] using hx i
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      refine ⟨genusBasis i, ⟨i, rfl⟩, ?_⟩
      apply e.injective
      simpa only [e.apply_symm_apply, heval] using (hx i).symm
  rwa [himage] at hgen

def sigmaGenerator (i : Fin 7) : Gal(maximalSigmaProTwo/ℚ) :=
  Function.surjInv sigmaGenusRestriction_surjective (genusBasis i)

theorem sigmaGenerator_genus (i : Fin 7) :
    sigmaGenusRestriction (sigmaGenerator i) = genusBasis i :=
  Function.surjInv_eq sigmaGenusRestriction_surjective (genusBasis i)

theorem sigmaGenerator_generates : TopologicallyGenerates (Set.range sigmaGenerator) :=
  sigmaGenerators_of_genusBasis sigmaGenerator sigmaGenerator_genus

end UnitDistance.ArithmeticProP
