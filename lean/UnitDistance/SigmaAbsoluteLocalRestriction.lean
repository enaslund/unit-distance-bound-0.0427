module

public import UnitDistance.OddAbsoluteFinitePairs
public import UnitDistance.AbsoluteLocalCompactness
public import UnitDistance.SigmaOddRelationWitness

@[expose] public section
set_option backward.privateInPublic true


/-! Actual odd absolute local maps into the constructed six-prime group,
with exact finite rational restriction compatibility. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.ArithmeticProP
open ClassFieldTower.Martinet.Shafarevich
open ArithmeticChosenGenus

abbrev SigmaOddInertia (i : Fin 5) := PrimeCompletion.AbsoluteInertia (ArithmeticOdd.prime i)
abbrev SigmaOddDecomposition (i : Fin 5) := PrimeCompletion.AbsoluteDecomposition (ArithmeticOdd.prime i)

def sigmaOddDecompositionMap (i : Fin 5) : SigmaOddDecomposition i →ₜ* SigmaGroup :=
  finitePlaceDecompositionToMaximalProPOutside 2 sigmaPrimeSupport
    (PrimeCompletion.place (ArithmeticOdd.prime i))

def sigmaOddInertiaMap (i : Fin 5) : SigmaOddInertia i →ₜ* SigmaGroup :=
  finitePlaceInertiaToMaximalProPOutside 2 sigmaPrimeSupport
    (PrimeCompletion.place (ArithmeticOdd.prime i))

@[simp] theorem sigmaOddInertiaMap_apply (i : Fin 5) (τ : SigmaOddInertia i) :
    sigmaOddInertiaMap i τ=sigmaOddDecompositionMap i τ.val := rfl

instance sigmaOddLocalPair_compact (i : Fin 5) :
    CompactSpace (SigmaOddInertia i × SigmaOddDecomposition i) :=
  finitePlaceAbsoluteInertiaDecomposition_compactSpace ℚ
    (PrimeCompletion.place (ArithmeticOdd.prime i))

/-- Finite restriction through the actual maximal field is the same as
restriction of the selected absolute decomposition element. -/
theorem sigmaOddDecompositionMap_restriction (i : Fin 5)
    (M : Type) [Field M] [NumberField M] [IsGalois ℚ M]
    (f : M →ₐ[ℚ] maximalSigmaProTwo) (σ : SigmaOddDecomposition i) :
    GaloisEmbedding.restriction f (sigmaOddDecompositionMap i σ)=
      PrimeCompletion.decompositionRestriction (ArithmeticOdd.prime i) M
        (maximalSigmaProTwo.val.comp f) σ := by
  apply GaloisEmbedding.restriction_unique
  intro x
  apply maximalSigmaProTwo.val.injective
  change (maximalSigmaProTwo.val.comp f)
      (GaloisEmbedding.restriction (maximalSigmaProTwo.val.comp f) σ.val x)=
    (sigmaOddDecompositionMap i σ (f x) : AlgebraicClosure ℚ)
  rw [GaloisEmbedding.restriction_commutes]
  exact (absoluteToMaximalProPOutside_apply 2 sigmaPrimeSupport σ.val (f x)).symm

end UnitDistance.ArithmeticProP
