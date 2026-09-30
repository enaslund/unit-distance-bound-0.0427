module

public import UnitDistance.GroupAugmentationRelationBlocks
public import UnitDistance.FilteredOptimizedGolodShafarevich
public import UnitDistance.RetainedQuadraticFox

@[expose] public section
set_option backward.privateInPublic true


/-!
# Optimized obstruction from actual completed relation coverage

The full defining relations cover all local blocks; the original global
relations cover only the other blocks. Completed Fox exactness proves the
spanning equality, and finite-2 consequence proves the common-row inclusion.
An actual retained quadratic group diagram supplies dyadic layer injections
and the actual genus-character coordinate inverse. None of these structural
conclusions is supplied as a Hilbert value or spanning hypothesis here.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.GroupAugmentation
variable {J : Type*} (κs : J → Type)

/-- Adjoin the distinguished dyadic generator type to an actual local family. -/
def withDyadicIndices : Option J → Type
  | none => Fin 3
  | some j => κs j

instance withDyadicIndices_fintype [∀ j, Fintype (κs j)] (j : Option J) :
    Fintype (withDyadicIndices κs j) := by
  cases j <;> dsimp [withDyadicIndices] <;> infer_instance

variable {ι : Type}

/-- The corresponding literal global word lifts. -/
def withDyadicWords (otherWords : ∀ j, κs j → FreeGroup ι)
    (words : Fin 3 → FreeGroup ι) : ∀ j, withDyadicIndices κs j → FreeGroup ι
  | none => words
  | some j => otherWords j

variable (P : Type) [Group P] [Finite P]
local notation "F" => ZMod 2
variable [Fintype ι] [Fintype J] [∀ j, Fintype (κs j)]
variable (generators : ι → P)

/-- The complete optimized local-block obstruction from actual presentation,
actual original-relation coverage, and an actual retained group diagram.
In a finite realization, the optimized coefficient must be strictly positive.
Thus any negative specialization rules out that finite realization. -/
theorem optimized_completed_presentation_positive (hP : IsPGroup 2 P)
    (hgen : Subgroup.closure (Set.range generators) = ⊤)
    (D : J → Type) [∀ j, Group (D j)] [∀ j, Finite (D j)]
    (localGenerators : ∀ j, κs j → D j)
    (localMaps : ∀ j, D j →* P) (otherWords : ∀ j, κs j → FreeGroup ι)
    (hlocalTwo : ∀ j, IsPGroup 2 (D j))
    (hlocalGen : ∀ j, Subgroup.closure (Set.range (localGenerators j)) = ⊤)
    (hlocalWords : ∀ j i, FreeGroup.lift generators (otherWords j i) =
      localMaps j (localGenerators j i))
    (hlayers : ∀ j n, Function.Injective (layerMap F (D j) (localMaps j) n))
    (words : Fin 3 → FreeGroup ι) (f : Dyadic.D →* P)
    (hwords : ∀ j, FreeGroup.lift generators (words j) = f (Dyadic.Filtration.gen j))
    (π : P →* RetainedQuadratic.Q) (hdiagram : π.comp f = RetainedQuadratic.dyadicMap)
    (allRelations : Set (CompletedWords ι))
    (hpresentation : CompletedProTwoPresentation P generators allRelations)
    (hAllCover : CompletedFoxRowCoverage P generators (withDyadicIndices κs)
      (withDyadicWords κs otherWords words) allRelations)
    (originalRelations : Set (CompletedWords ι))
    (hOriginalVanish : ∀ s ∈ originalRelations, completedWordEvaluation P generators s = 1)
    (hOriginalCover : CompletedFoxRowCoverage P generators κs otherWords originalRelations)
    (localRelation : CompletedWords (Fin 3))
    (hLocalVanish : completedWordEvaluation Dyadic.D Dyadic.Filtration.gen localRelation = 1)
    (globalLocalRelation : CompletedWords ι)
    (hGlobalRow : completedFoxDerivative P generators globalLocalRelation =
      completedFoxDerivative P generators (completedSubstitution words localRelation))
    (hConsequence : CompletedProTwoConsequence originalRelations globalLocalRelation)
    (hInitial : ∀ i, completedFoxDerivative Dyadic.D Dyadic.Filtration.gen localRelation i -
      Dyadic.AlgebraD.linearFoxCoefficients i ∈ Dyadic.AlgebraD.augmentationPower 2)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < 1-(Fintype.card ι : ℝ)*t +
      (∑ j, ((Fintype.card (κs j) : ℝ)*t-1+
        1/Polynomial.eval₂ (Nat.castRingHom ℝ) t (hilbertPolynomial (D j)))) +
      (3*t-1+1/((1+t)^3*(1+t^2)^2)) -
      t^2*(1-t^7/((1+t)^3*(1+t^2)^2)) := by
  have hs := foxKernel_eq_blocks_of_rowCoverage P generators (withDyadicIndices κs)
    (withDyadicWords κs otherWords words) hP hgen allRelations hpresentation hAllCover
  rw [iSup_option] at hs
  have hspan : (foxMap F P generators).ker =
      (⨆ j, globalFoxBlock P generators (otherWords j)) ⊔ globalFoxBlock P generators words := by
    change (foxMap F P generators).ker = globalFoxBlock P generators words ⊔
      (⨆ j, globalFoxBlock P generators (otherWords j)) at hs
    exact hs.trans (sup_comm _ _)
  have hcommon := commonRow_le_other_blocks_of_original_row P generators κs otherWords hP
    words f hwords originalRelations hOriginalVanish hOriginalCover localRelation
    globalLocalRelation hGlobalRow hConsequence
  have hi := finite_optimized_local_family_inequality P hP generators hgen D κs
    localGenerators localMaps otherWords hlocalTwo hlocalGen hlocalWords hlayers words f hwords
    (RetainedQuadratic.retained_dyadic_layer_injections P f π hdiagram 1)
    (RetainedQuadratic.retained_dyadic_layer_injections P f π hdiagram 2)
    (characterFoxRetraction P generators (fun k => (RetainedQuadratic.dyadicCharacter k).comp π))
    (RetainedQuadratic.retained_characterFoxRetraction_left P f π hdiagram generators words hwords)
    (completedFoxDerivative Dyadic.D Dyadic.Filtration.gen localRelation) hInitial hspan
    (dyadic_completed_row_kernel P generators words f hwords localRelation hLocalVanish)
    hcommon t ht0 ht1
  have hH := hilbertPolynomial_eval_pos P t ht0
  exact (mul_pos_iff_of_pos_right hH).mp (lt_of_lt_of_le zero_lt_one hi)

end UnitDistance.GroupAugmentation
