module

public import UnitDistance.SigmaCutCompletedPresentation
public import UnitDistance.FilteredCompletedBlockPresentation

@[expose] public section
set_option backward.privateInPublic true


/-! The actual arithmetic twenty-seven-word cut is infinite, by the
proved optimized Golod--Shafarevich local-block inequality. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace UnitDistance.ArithmeticProP.SigmaCut
open GroupAugmentation ArithmeticLocalBlocks
open scoped BigOperators

/-- All actual finite local blocks, exact row coverage, the genuine dyadic
initial, and the numerical negative certificate rule out a finite cut. -/
theorem infinite_of_arithmeticPresentation (hgen : ArithmeticPresentation) :
    Infinite ActualQuotient := by
  classical
  by_contra hfin
  haveI : Finite ActualQuotient := not_infinite_iff_finite.mp hfin
  let words : ∀j : AllIndex,AllGeneratorType j → FreeGroup (Fin 7) :=
    fun j=>(exists_literal_affine_lifts ActualQuotient finiteGenerators (allLifts j)).choose
  have hmatch (j : AllIndex) : ∀i,
      foxLift (ZMod 2) ActualQuotient finiteGenerators (words j i)=
        completedFoxLift ActualQuotient finiteGenerators (allLifts j i) :=
    (exists_literal_affine_lifts ActualQuotient finiteGenerators (allLifts j)).choose_spec
  have hwords (j : AllIndex) (i : AllGeneratorType j) :
      FreeGroup.lift finiteGenerators (words j i)=allMap hgen j (allGenerators j i) :=
    (literal_affine_lifts_evaluation ActualQuotient finiteGenerators (allLifts j)
      (words j) (hmatch j) i).trans (finite_allLifts hgen j i)
  have hAllCover : CompletedFoxRowCoverage ActualQuotient finiteGenerators AllGeneratorType
      words allRelations := by
    rintro r ⟨j,s,hs,rfl⟩
    refine ⟨j,s,?_,?_⟩
    · simp_rw [hwords]
      rw [completedWordEvaluation_naturality,hs,map_one]
    · exact completedGeneratorSubstitution_derivative_eq ActualQuotient finiteGenerators
        (allLifts j) (words j) (hmatch j) s
  have hOtherCover : CompletedFoxRowCoverage ActualQuotient finiteGenerators GeneratorType
      (fun j=>words (some j)) otherRelations := by
    rintro r ⟨j,s,hs,rfl⟩
    refine ⟨j,s,?_,?_⟩
    · simp_rw [hwords]
      rw [completedWordEvaluation_naturality]
      change otherMap j (completedWordEvaluation (LocalGroup j)
        (ArithmeticLocalBlocks.generators j) s)=1
      rw [hs,map_one]
    · exact completedGeneratorSubstitution_derivative_eq ActualQuotient finiteGenerators
        (allLifts (some j)) (words (some j)) (hmatch (some j)) s
  have hOtherVanish (s : CompletedWords (Fin 7)) (hs : s∈otherRelations) :
      completedWordEvaluation ActualQuotient finiteGenerators s=1 := by
    have h := localFamily_image_le_kernel GeneratorType LocalGroup ArithmeticLocalBlocks.generators
      (FiniteFreeProTwo.generator 7) ActualQuotient finiteProjection otherMap otherLifts
      finite_otherLifts ⟨s,hs,rfl⟩
    change finiteProjection (completionMap (FiniteFreeProTwo.generator 7) s)=1 at h
    exact (completedWordEvaluation_completionMap (FiniteFreeProTwo.generator 7)
      ActualQuotient finiteProjection s).trans h
  have hGlobalRow : completedFoxDerivative ActualQuotient finiteGenerators
      SigmaDyadic.completedGlobalRelation=
        completedFoxDerivative ActualQuotient finiteGenerators
          (completedSubstitution (words none) SigmaDyadic.completedRelation) :=
    completedGeneratorSubstitution_derivative_eq ActualQuotient finiteGenerators
      (allLifts none) (words none) (hmatch none) SigmaDyadic.completedRelation
  have hewords : withDyadicWords GeneratorType (fun j=>words (some j)) (words none)=words := by
    funext j
    cases j <;> rfl
  have hcover : CompletedFoxRowCoverage ActualQuotient finiteGenerators
      (withDyadicIndices GeneratorType)
      (withDyadicWords GeneratorType (fun j=>words (some j)) (words none)) allRelations := by
    rw [hewords]
    exact hAllCover
  have hpos := optimized_completed_presentation_positive GeneratorType ActualQuotient finiteGenerators
    finite_isTwoGroup finite_generates LocalGroup ArithmeticLocalBlocks.generators otherMap
    (fun j=>words (some j)) ArithmeticLocalBlocks.isTwoGroup ArithmeticLocalBlocks.generates
    (fun j i=>hwords (some j) i) otherMap_layers (words none) (actualDyadicMap hgen).toMonoidHom
    (hwords none) canonicalRetained (canonicalRetained_diagram hgen)
    allRelations (finite_completedPresentation hgen) hcover otherRelations hOtherVanish hOtherCover
    SigmaDyadic.completedRelation SigmaDyadic.completedRelation_initial.1
    SigmaDyadic.completedGlobalRelation hGlobalRow (genuine_other_consequence hgen)
    SigmaDyadic.completedRelation_initial.2 (11/34) (by norm_num) (by norm_num)
  have hneg := ArithmeticLocalBlocks.optimized_coefficient_negative
  norm_num only [Fintype.card_fin] at hpos
  unfold cost at hneg
  norm_num only [Fintype.card_fin] at hneg
  linarith

end UnitDistance.ArithmeticProP.SigmaCut
