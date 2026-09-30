module

public import UnitDistance.SigmaCutOddDecomposition
public import UnitDistance.SigmaCutLocalGenus
public import UnitDistance.Witness

@[expose] public section
set_option backward.privateInPublic true


/-! Pointwise genus exclusion for the full actual absolute decomposition
groups at the eleven selected primes. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.ArithmeticProP.SigmaCut
open ProCGroups.Presentations RetainedQuadratic

variable (s : Fin 5 → Source)
  (hgen : closedNormalClosure (Set.range (fun i ↦ (sigmaOriginalRelator i : Source)))=
    (sigmaRelationKernel : Subgroup Source))
include s hgen

theorem odd_absolute_genus_exclusion (i : Fin 5) (d : SigmaOddDecomposition i) :
    (sigmaRetainedModelMap (sigmaOddDecompositionMap i d)).base≠binaryVector 7 1 := by
  have hm : retained s (arithmeticProjection s hgen (sigmaOddDecompositionMap i d))∈
      ((retained s).toMonoidHom.comp (oddMap s i)).range := by
    rw [←odd_decomposition_range s hgen (retained s) i]
    exact ⟨d,rfl⟩
  obtain ⟨g,hg⟩ := hm
  change retained s (oddMap s i g)=retained s
    (arithmeticProjection s hgen (sigmaOddDecompositionMap i d)) at hg
  rw [retained_arithmeticProjection] at hg
  rw [←hg]
  exact oddMap_genus_exclusion s i g

theorem dyadic_absolute_genus_exclusion
    (d : PrimeCompletion.AbsoluteDecomposition PadicTwoGlobalMap.prime) :
    (sigmaRetainedModelMap (SigmaUnramified.decompositionMap PadicTwoGlobalMap.prime d)).base≠
      binaryVector 7 1 := by
  have hm : dyadicDecompositionMap s hgen d∈(dyadicMap s hgen).toMonoidHom.range := by
    rw [←dyadic_decomposition_range s hgen]
    exact ⟨d,rfl⟩
  obtain ⟨g,hg⟩ := hm
  rw [←retained_arithmeticProjection s hgen]
  change (retained s (dyadicDecompositionMap s hgen d)).base≠_
  rw [←hg]
  exact dyadicMap_genus_exclusion s hgen g

omit s in
theorem extra_absolute_genus_exclusion (i : Fin 5)
    (d : PrimeCompletion.AbsoluteDecomposition (ExtraPrime.prime i)) :
    (sigmaRetainedModelMap (SigmaUnramified.decompositionMap (ExtraPrime.prime i) d)).base≠
      binaryVector 7 1 := by
  have hm : retained ExtraPrime.freeFrobenius
      (arithmeticProjection ExtraPrime.freeFrobenius hgen
        (SigmaUnramified.decompositionMap (ExtraPrime.prime i) d))∈
      ((retained ExtraPrime.freeFrobenius).toMonoidHom.comp
        (extraMap ExtraPrime.freeFrobenius i)).range := by
    rw [←extra_decomposition_range hgen (retained ExtraPrime.freeFrobenius) i]
    exact ⟨d,rfl⟩
  obtain ⟨g,hg⟩ := hm
  change retained ExtraPrime.freeFrobenius (extraMap ExtraPrime.freeFrobenius i g)=
    retained ExtraPrime.freeFrobenius (arithmeticProjection ExtraPrime.freeFrobenius hgen
      (SigmaUnramified.decompositionMap (ExtraPrime.prime i) d)) at hg
  rw [retained_arithmeticProjection] at hg
  rw [←hg]
  exact extraMap_genus_exclusion i g

/-- The eleven rational primes used by the geometric witness. -/
def selectedPrime (a : Fin 11) : Nat.Primes :=
  ⟨Witness.primes a,by fin_cases a <;> decide⟩

theorem selected_absolute_genus_exclusion (a : Fin 11)
    (d : PrimeCompletion.AbsoluteDecomposition (selectedPrime a)) :
    (sigmaRetainedModelMap (SigmaUnramified.decompositionMap (selectedPrime a) d)).base≠
      binaryVector 7 1 := by
  fin_cases a
  · exact dyadic_absolute_genus_exclusion s hgen d
  · exact odd_absolute_genus_exclusion s hgen 0 d
  · exact odd_absolute_genus_exclusion s hgen 1 d
  · exact odd_absolute_genus_exclusion s hgen 2 d
  · exact odd_absolute_genus_exclusion s hgen 3 d
  · exact odd_absolute_genus_exclusion s hgen 4 d
  · exact extra_absolute_genus_exclusion hgen 0 d
  · exact extra_absolute_genus_exclusion hgen 1 d
  · exact extra_absolute_genus_exclusion hgen 2 d
  · exact extra_absolute_genus_exclusion hgen 3 d
  · exact extra_absolute_genus_exclusion hgen 4 d

omit s hgen in
theorem complexConjugation_retained_base :
    (sigmaRetainedModelMap sigmaComplexConjugation).base=binaryVector 7 1 := by
  rw [←sigmaFreeConjugation_image]
  change (sigmaFreeRetainedMap sigmaFreeConjugation).base=_
  exact infinity_base

end UnitDistance.ArithmeticProP.SigmaCut
