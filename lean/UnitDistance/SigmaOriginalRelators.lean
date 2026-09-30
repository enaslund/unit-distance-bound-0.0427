module

public import UnitDistance.SigmaFreeRetained
public import UnitDistance.SigmaAbsoluteOddGeneration
public import UnitDistance.UniversalQuadraticFree
public import UnitDistance.UniversalQuadraticTame

@[expose] public section
set_option backward.privateInPublic true


/-! Six actual original words in the minimal free presentation of the
maximal six-prime arithmetic group, with their independent quadratic images.
No cohomological relation bound or normal-generation claim is used here. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace UnitDistance.ArithmeticProP
open ArithmeticGenusFrattini ProCGroups ProCGroups.ProC

abbrev SigmaFree := FiniteFreeProTwo.Carrier 7

/-- Chosen generators are actual absolute local witnesses, retaining generation
in every finite quotient as well as their genus signs and literal tame relation. -/
def sigmaAbsoluteOddInertia (i : Fin 5) : SigmaOddInertia i :=
  (sigma_absolute_odd_generating_relation i).choose

def sigmaAbsoluteOddFrobenius (i : Fin 5) : SigmaOddDecomposition i :=
  (sigma_absolute_odd_generating_relation i).choose_spec.choose

def sigmaOddInertia (i : Fin 5) : SigmaGroup :=
  sigmaOddInertiaMap i (sigmaAbsoluteOddInertia i)

def sigmaOddFrobenius (i : Fin 5) : SigmaGroup :=
  sigmaOddDecompositionMap i (sigmaAbsoluteOddFrobenius i)

theorem sigmaOddInertia_genus (i : Fin 5) :
    sigmaGenusRestriction (sigmaOddInertia i)=Multiplicative.ofAdd
      (UniversalQuadratic.inertiaVectors (UniversalQuadratic.oddIndex i)) :=
  (sigma_absolute_odd_generating_relation i).choose_spec.choose_spec.1

theorem sigmaOddFrobenius_genus (i : Fin 5) :
    sigmaGenusRestriction (sigmaOddFrobenius i)=Multiplicative.ofAdd
      (UniversalQuadratic.frobeniusVectors (UniversalQuadratic.oddIndex i)) :=
  (sigma_absolute_odd_generating_relation i).choose_spec.choose_spec.2.1

theorem sigmaOdd_tame (i : Fin 5) :
    sigmaOddFrobenius i*sigmaOddInertia i*(sigmaOddFrobenius i)⁻¹=
      sigmaOddInertia i^(UniversalQuadratic.oddPrimes i) :=
  (sigma_absolute_odd_generating_relation i).choose_spec.choose_spec.2.2.1

theorem sigmaOdd_quotientGenerates (i : Fin 5) (U : OpenNormalSubgroup SigmaGroup) :
    ProfiniteTame.quotientGenerates (sigmaOddInertiaMap i) (sigmaOddDecompositionMap i) U
      (sigmaOddInertia i) (sigmaOddFrobenius i) :=
  (sigma_absolute_odd_generating_relation i).choose_spec.choose_spec.2.2.2 U

def sigmaFreeOddInertia (i : Fin 5) : SigmaFree :=
  Function.surjInv sigmaFreeMap_surjective (sigmaOddInertia i)

def sigmaFreeOddFrobenius (i : Fin 5) : SigmaFree :=
  Function.surjInv sigmaFreeMap_surjective (sigmaOddFrobenius i)

theorem sigmaFreeOddInertia_image (i : Fin 5) :
    sigmaFreeMap (sigmaFreeOddInertia i)=sigmaOddInertia i :=
  Function.surjInv_eq sigmaFreeMap_surjective _

theorem sigmaFreeOddFrobenius_image (i : Fin 5) :
    sigmaFreeMap (sigmaFreeOddFrobenius i)=sigmaOddFrobenius i :=
  Function.surjInv_eq sigmaFreeMap_surjective _

def sigmaOriginalRelator : Fin 6 → sigmaRelationKernel :=
  Fin.cases ⟨sigmaFreeConjugation^2,sigmaFreeConjugation_square_mem⟩ (fun i ↦
    ⟨sigmaFreeOddFrobenius i*sigmaFreeOddInertia i*(sigmaFreeOddFrobenius i)⁻¹*
      ((sigmaFreeOddInertia i)^(UniversalQuadratic.oddPrimes i))⁻¹,by
      change sigmaFreeMap (_*_*_⁻¹*(_^_)⁻¹)=1
      rw [map_mul,map_mul,map_mul,map_inv,map_inv,map_pow,
        sigmaFreeOddInertia_image,sigmaFreeOddFrobenius_image,sigmaOdd_tame,mul_inv_cancel]⟩)

theorem sigmaOriginalRelator_infinity :
    (sigmaOriginalRelator 0 : SigmaFree)=sigmaFreeConjugation^2 := rfl

theorem sigmaOriginalRelator_odd (i : Fin 5) :
    (sigmaOriginalRelator (UniversalQuadratic.oddIndex i) : SigmaFree)=
      sigmaFreeOddFrobenius i*sigmaFreeOddInertia i*(sigmaFreeOddFrobenius i)⁻¹*
        ((sigmaFreeOddInertia i)^(UniversalQuadratic.oddPrimes i))⁻¹ := rfl

/-- The universal quadratic detector is constructed from actual freeness. -/
def sigmaUniversalDetector : SigmaFree →ₜ* UniversalQuadratic.Q :=
  UniversalQuadratic.freeDetector (FiniteFreeProTwo.isFree 7)

theorem sigmaUniversalDetector_base (g : SigmaFree) :
    (sigmaUniversalDetector g).base=(sigmaGenusRestriction (sigmaFreeMap g)).toAdd := by
  have hE : HasPGroupOpenNormalBasis 2 VectorGroup := by
    have htwo : IsPGroup 2 VectorGroup := IsPGroup.of_card vectorGroup_card
    apply HasOpenNormalBasisInClass.of_allOpenNormalQuotients
    intro U
    exact ⟨inferInstance,htwo.of_surjective (QuotientGroup.mk' (U : Subgroup VectorGroup))
      (QuotientGroup.mk'_surjective (U : Subgroup VectorGroup))⟩
  let f : SigmaFree →* VectorGroup :=
    (ClassTwo.GroupModel.baseHom UniversalQuadratic.cocycle).comp sigmaUniversalDetector.toMonoidHom
  let q := sigmaGenusRestriction.comp sigmaFreeMap
  have hf : Continuous f :=
    (continuous_of_discreteTopology : Continuous
      (ClassTwo.GroupModel.baseHom UniversalQuadratic.cocycle)).comp
        sigmaUniversalDetector.continuous_toFun
  have he : f=q.toMonoidHom := (FiniteFreeProTwo.isFree 7).hom_ext hE hf q.continuous_toFun (by
    intro i
    apply Multiplicative.toAdd.injective
    change (sigmaUniversalDetector (FiniteFreeProTwo.generator 7 i)).base=
      (sigmaGenusRestriction (sigmaFreeMap (FiniteFreeProTwo.generator 7 i))).toAdd
    rw [sigmaFreeMap_generator_genus]
    exact UniversalQuadratic.freeDetector_generator_base (FiniteFreeProTwo.isFree 7) i)
  exact congrArg Multiplicative.toAdd (DFunLike.congr_fun he g)

theorem sigmaUniversalDetector_conjugation :
    (sigmaUniversalDetector sigmaFreeConjugation).base=UniversalQuadratic.inertiaVectors 0 := by
  rw [sigmaUniversalDetector_base,sigmaFreeConjugation_image,sigmaComplexConjugation_genus]
  decide +kernel

theorem sigmaUniversalDetector_inertia (i : Fin 5) :
    (sigmaUniversalDetector (sigmaFreeOddInertia i)).base=
      UniversalQuadratic.inertiaVectors (UniversalQuadratic.oddIndex i) := by
  rw [sigmaUniversalDetector_base,sigmaFreeOddInertia_image,sigmaOddInertia_genus]
  rfl

theorem sigmaUniversalDetector_frobenius (i : Fin 5) :
    (sigmaUniversalDetector (sigmaFreeOddFrobenius i)).base=
      UniversalQuadratic.frobeniusVectors (UniversalQuadratic.oddIndex i) := by
  rw [sigmaUniversalDetector_base,sigmaFreeOddFrobenius_image,sigmaOddFrobenius_genus]
  rfl

/-- The six literal arithmetic words have the independently computed
quadratic coordinates, without an assumed local presentation. -/
theorem sigmaOriginalRelator_quadratic (i : Fin 6) :
    (sigmaUniversalDetector (sigmaOriginalRelator i)).central=
      UniversalQuadratic.originalInitial i := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rw [sigmaOriginalRelator_infinity,map_pow]
    exact congrArg (fun x : UniversalQuadratic.Q ↦ x.central)
      (UniversalQuadratic.infinitySquare_originalInitial _ sigmaUniversalDetector_conjugation)
  · change (sigmaUniversalDetector (sigmaOriginalRelator (UniversalQuadratic.oddIndex j))).central=_
    rw [sigmaOriginalRelator_odd,map_mul,map_mul,map_mul,map_inv,map_inv,map_pow]
    simpa only [UniversalQuadratic.tameWord,UniversalQuadratic.oddIndex,Fin.succ] using
      congrArg (fun x : UniversalQuadratic.Q ↦ x.central)
        (UniversalQuadratic.tameWord_originalInitial j _ _
          (sigmaUniversalDetector_inertia j) (sigmaUniversalDetector_frobenius j))

end UnitDistance.ArithmeticProP
