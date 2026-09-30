module

public import UnitDistance.Sqrt241.Cut.CompletedPresentation
public import UnitDistance.Sqrt241.Cut.BlockCosts
public import UnitDistance.Sqrt241.Cut.RetainedParameter

@[expose] public section
set_option backward.privateInPublic true


/-!
# The cut quotient of the free source is infinite

The optimized Golod–Shafarevich local-block inequality
(`GS.optimized_completed_presentation_positive_retained`, with the retained
group of the distinguished dyadic slot `𝔭₁` equal to `Q_B`) applies to every
finite cut quotient: eight generators, the ten other blocks of
`Cut.Index`, the distinguished dyadic block with its saving. Its coefficient
is `P_B(34/117) < 0` (`Cut.optimized_coefficient_negative`), so the cut
quotient is infinite.

Hypotheses: lifts `A` with the label facts `hL` (proved for the local elements in
`Local/`), a genuine local relation `r` with the proved initial `hr`, and the
presentation hypothesis `hgen : A.Presentation r` (proved in `Presentation/`).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace UnitDistance.Sqrt241.Cut
open GroupAugmentation ProCGroups ProCGroups.Presentations GroupData

namespace SourceLifts
variable (A : SourceLifts)

/-- Infinitude of the literal cut quotient of the free source. -/
theorem infinite_of_presentation (hL : A.Labels) (r : LocalSource)
    (hr : Dyadic.ArithmeticPresentation.detector r = FreeThreeQuadratic.relation)
    (hgen : A.Presentation r) : Infinite A.ActualQuotient := by
  classical
  by_contra hfin
  have : Finite A.ActualQuotient := not_infinite_iff_finite.mp hfin
  let words : ∀ j : AllIndex, AllGeneratorType j → FreeGroup (Fin 8) :=
    fun j => (exists_literal_affine_lifts A.ActualQuotient A.finiteGenerators (A.allLifts j)).choose
  have hmatch (j : AllIndex) : ∀ i,
      foxLift (ZMod 2) A.ActualQuotient A.finiteGenerators (words j i) =
        completedFoxLift A.ActualQuotient A.finiteGenerators (A.allLifts j i) :=
    (exists_literal_affine_lifts A.ActualQuotient A.finiteGenerators (A.allLifts j)).choose_spec
  have hwords (j : AllIndex) (i : AllGeneratorType j) :
      FreeGroup.lift A.finiteGenerators (words j i) = A.allMap r hr hgen j (allGenerators j i) :=
    (literal_affine_lifts_evaluation A.ActualQuotient A.finiteGenerators (A.allLifts j)
      (words j) (hmatch j) i).trans (A.finite_allLifts r hr hgen j i)
  have hAllCover : CompletedFoxRowCoverage A.ActualQuotient A.finiteGenerators AllGeneratorType
      words A.allRelations := by
    rintro _ ⟨j,s,hs,rfl⟩
    refine ⟨j,s,?_,?_⟩
    · simp_rw [hwords]
      rw [completedWordEvaluation_naturality,hs,map_one]
    · exact completedGeneratorSubstitution_derivative_eq A.ActualQuotient A.finiteGenerators
        (A.allLifts j) (words j) (hmatch j) s
  have hOtherCover : CompletedFoxRowCoverage A.ActualQuotient A.finiteGenerators GeneratorType
      (fun j => words (some j)) A.otherRelations := by
    rintro _ ⟨j,s,hs,rfl⟩
    refine ⟨j,s,?_,?_⟩
    · simp_rw [hwords]
      rw [completedWordEvaluation_naturality]
      change A.otherMap r hr hgen j (completedWordEvaluation (LocalGroup j) (localGenerators j) s) = 1
      rw [hs,map_one]
    · exact completedGeneratorSubstitution_derivative_eq A.ActualQuotient A.finiteGenerators
        (A.allLifts (some j)) (words (some j)) (hmatch (some j)) s
  have hOtherVanish (s : CompletedWords (Fin 8)) (hs : s ∈ A.otherRelations) :
      completedWordEvaluation A.ActualQuotient A.finiteGenerators s = 1 := by
    have h := localFamily_image_le_kernel GeneratorType LocalGroup localGenerators
      (FiniteFreeProTwo.generator 8) A.ActualQuotient A.finiteProjection (A.otherMap r hr hgen)
      A.otherLifts (A.finite_otherLifts r hr hgen) ⟨s,hs,rfl⟩
    change A.finiteProjection (completionMap (FiniteFreeProTwo.generator 8) s) = 1 at h
    exact (completedWordEvaluation_completionMap (FiniteFreeProTwo.generator 8)
      A.ActualQuotient A.finiteProjection s).trans h
  have hGlobalRow : completedFoxDerivative A.ActualQuotient A.finiteGenerators
      (A.completedGlobalRelation r 0) =
        completedFoxDerivative A.ActualQuotient A.finiteGenerators
          (completedSubstitution (words none) (completedRelation r)) :=
    completedGeneratorSubstitution_derivative_eq A.ActualQuotient A.finiteGenerators
      (A.allLifts none) (words none) (hmatch none) (completedRelation r)
  have hewords : withDyadicWords GeneratorType (fun j => words (some j)) (words none) = words := by
    funext j
    cases j <;> rfl
  have hcover : CompletedFoxRowCoverage A.ActualQuotient A.finiteGenerators
      (withDyadicIndices GeneratorType)
      (withDyadicWords GeneratorType (fun j => words (some j)) (words none)) A.allRelations := by
    rw [hewords]
    exact hAllCover
  have hpos := GS.optimized_completed_presentation_positive_retained GeneratorType
    A.ActualQuotient A.finiteGenerators A.finite_isTwoGroup A.finite_generates LocalGroup
    localGenerators (A.otherMap r hr hgen) (fun j => words (some j)) localIsTwoGroup
    localGenerates (fun j i => hwords (some j) i) (A.otherMap_layers r hr hgen hL)
    (words none) (A.dyadicQuotientMap r hr hgen 0).toMonoidHom (hwords none) Retained.Q
    (Retained.dyadicMapOfLifts 0 (retainedFree (A.lifts.dyadicX 0))
      (retainedFree (A.lifts.dyadicY 0)) (retainedFree (A.lifts.dyadicZ 0)))
    (Retained.dyadicMapOfLifts_layers 0 _ _ _ 1) (Retained.dyadicMapOfLifts_layers 0 _ _ _ 2)
    (Retained.dyadicCharacter 0) (Retained.dyadicCharacter_ofLifts 0 _ _ _)
    (A.retained hL).toMonoidHom (A.retained_dyadicQuotientMap r hr hgen hL 0)
    A.allRelations (A.finite_completedPresentation r hr hgen) hcover A.otherRelations
    hOtherVanish hOtherCover (completedRelation r) (completedRelation_initial r hr).1
    (A.completedGlobalRelation r 0) hGlobalRow (A.genuine_other_consequence r hr hgen)
    (completedRelation_initial r hr).2 (34/117) (by norm_num) (by norm_num)
  have hneg := optimized_coefficient_negative
  norm_num only [Fintype.card_fin] at hpos
  unfold cost at hneg
  norm_num only [Fintype.card_fin] at hneg
  linarith

end SourceLifts
end UnitDistance.Sqrt241.Cut
