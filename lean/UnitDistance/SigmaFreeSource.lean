module

public import UnitDistance.SigmaGenusGenerators
public import UnitDistance.FiniteFreeProTwo

@[expose] public section
set_option backward.privateInPublic true


/-! A constructed free pro-two source and a minimal quotient map onto the
actual maximal six-prime arithmetic group. No relation bound is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace UnitDistance.ArithmeticProP
open ClassFieldTower.ProP ProCGroups

theorem exists_sigmaFreeMap :
    ∃ π : FiniteFreeProTwo.Carrier 7 →ₜ* Gal(maximalSigmaProTwo/ℚ),
      Function.Surjective π ∧
      π.toMonoidHom.ker ≤ closedPowerCommutator 2 (FiniteFreeProTwo.Carrier 7) ∧
      ∀ i, π (FiniteFreeProTwo.generator 7 i) = sigmaGenerator i :=
  FiniteFreeProTwo.exists_minimal_surjection_for_generators
    maximalSigmaProTwo_hasPGroupOpenNormalBasis 7 sigmaGenerator
    sigmaGenerator_generates maximalSigmaProTwo_generatorRank.2

def sigmaFreeMap : FiniteFreeProTwo.Carrier 7 →ₜ* Gal(maximalSigmaProTwo/ℚ) :=
  Classical.choose exists_sigmaFreeMap

theorem sigmaFreeMap_surjective : Function.Surjective sigmaFreeMap :=
  (Classical.choose_spec exists_sigmaFreeMap).1

theorem sigmaFreeMap_minimal :
    sigmaFreeMap.toMonoidHom.ker ≤ closedPowerCommutator 2 (FiniteFreeProTwo.Carrier 7) :=
  (Classical.choose_spec exists_sigmaFreeMap).2.1

theorem sigmaFreeMap_generator (i : Fin 7) :
    sigmaFreeMap (FiniteFreeProTwo.generator 7 i) = sigmaGenerator i :=
  (Classical.choose_spec exists_sigmaFreeMap).2.2 i

theorem sigmaFreeMap_generator_genus (i : Fin 7) :
    sigmaGenusRestriction (sigmaFreeMap (FiniteFreeProTwo.generator 7 i)) = genusBasis i := by
  rw [sigmaFreeMap_generator, sigmaGenerator_genus]

def sigmaRelationKernel : ClosedSubgroup (FiniteFreeProTwo.Carrier 7) where
  toSubgroup := sigmaFreeMap.toMonoidHom.ker
  isClosed' := ProCGroups.ContinuousMonoidHom.isClosed_ker sigmaFreeMap

instance sigmaRelationKernel_normal : sigmaRelationKernel.Normal :=
  inferInstanceAs sigmaFreeMap.toMonoidHom.ker.Normal

/-- The quotient by the actual relation kernel is topologically isomorphic
to the actual arithmetic Galois group. -/
def sigmaFreeQuotientEquiv :
    (FiniteFreeProTwo.Carrier 7 ⧸ (sigmaRelationKernel : Subgroup _)) ≃ₜ*
      Gal(maximalSigmaProTwo/ℚ) := by
  let e := QuotientGroup.quotientKerEquivOfSurjective
    sigmaFreeMap.toMonoidHom sigmaFreeMap_surjective
  apply ContinuousMulEquiv.ofBijectiveCompactToT2 e.toMonoidHom _ e.bijective
  apply (QuotientGroup.isQuotientMap_mk sigmaFreeMap.toMonoidHom.ker).continuous_iff.mpr
  exact sigmaFreeMap.continuous_toFun

theorem sigmaFreeQuotientEquiv_mk (g : FiniteFreeProTwo.Carrier 7) :
    sigmaFreeQuotientEquiv (QuotientGroup.mk' (sigmaRelationKernel : Subgroup _) g) =
      sigmaFreeMap g := rfl

end UnitDistance.ArithmeticProP
