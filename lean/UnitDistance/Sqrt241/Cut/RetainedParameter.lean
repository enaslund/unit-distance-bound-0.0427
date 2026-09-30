module

public import UnitDistance.FilteredCompletedBlockPresentation

@[expose] public section
set_option backward.privateInPublic true


/-!
# The optimized block obstruction with the retained group as a parameter

Copy of `GroupAugmentation.optimized_completed_presentation_positive`
(`FilteredCompletedBlockPresentation.lean`, left unchanged) in which the
retained quadratic group of the distinguished dyadic slot is a parameter.

* `optimized_completed_presentation_positive_core`: the dyadic slot needs only
  its first two layer injections and three characters of the finite group
  dual to the dyadic generators;
* `optimized_completed_presentation_positive_retained`: these are supplied by
  any group `R` with a local map `ρ : D → R` (layers 1, 2 injective), three
  characters of `R` dual to `ρ(x), ρ(y), ρ(z)` and a diagram `π ∘ f = ρ`.

The `ℚ` theorem is the instance `R = RetainedQuadratic.Q`,
`ρ = RetainedQuadratic.dyadicMap` (`optimized_completed_presentation_positive_rat`).
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.Sqrt241.GS
open GroupAugmentation

section Pullback
variable (R G : Type*) [CommRing R] [Group G] {H K : Type*} [Group H] [Group K]

/-- Layer injectivity of a composite passes to its first factor. -/
theorem layerMap_injective_of_comp (f : G →* H) (π : H →* K) (n : ℕ)
    (h : Function.Injective (layerMap R G (π.comp f) n)) :
    Function.Injective (layerMap R G f n) := by
  apply (layerMap_injective_iff R G f n).mpr
  intro g hg hfg
  exact (layerMap_injective_iff R G (π.comp f) n).mp h g hg
    (map_dimensionSubgroup_le R H π (n+1) ⟨f g,hfg,rfl⟩)

end Pullback

variable {J : Type*} (κs : J → Type)
variable {ι : Type}
variable (P : Type) [Group P] [Finite P]
local notation "F" => ZMod 2
variable [Fintype ι] [Fintype J] [∀ j, Fintype (κs j)]
variable (generators : ι → P)

/-- Core form: the distinguished dyadic slot needs its first two layer
injections and three characters dual to its generators. -/
theorem optimized_completed_presentation_positive_core (hP : IsPGroup 2 P)
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
    (hfirst : Function.Injective (layerMap F Dyadic.D f 1))
    (hsecond : Function.Injective (layerMap F Dyadic.D f 2))
    (characters : Fin 3 → P →* Multiplicative F)
    (hcharacters : ∀ j k, (characters k (f (Dyadic.Filtration.gen j))).toAdd =
      (Pi.single j (1 : F) : Fin 3 → F) k)
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
    hfirst hsecond
    (characterFoxRetraction P generators characters)
    (characterFoxRetraction_left P generators words characters
      (fun a b => by rw [hwords a]; exact hcharacters a b))
    (completedFoxDerivative Dyadic.D Dyadic.Filtration.gen localRelation) hInitial hspan
    (dyadic_completed_row_kernel P generators words f hwords localRelation hLocalVanish)
    hcommon t ht0 ht1
  have hH := hilbertPolynomial_eval_pos P t ht0
  exact (mul_pos_iff_of_pos_right hH).mp (lt_of_lt_of_le zero_lt_one hi)

/-- Retained-parameter form: the dyadic slot is controlled by a map `ρ` of the
local group into an arbitrary group `R` through which the local map factors. -/
theorem optimized_completed_presentation_positive_retained (hP : IsPGroup 2 P)
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
    (R : Type*) [Group R] (ρ : Dyadic.D →* R)
    (hρ1 : Function.Injective (layerMap F Dyadic.D ρ 1))
    (hρ2 : Function.Injective (layerMap F Dyadic.D ρ 2))
    (χ : Fin 3 → R →* Multiplicative F)
    (hχ : ∀ j k, (χ k (ρ (Dyadic.Filtration.gen j))).toAdd = (Pi.single j (1 : F) : Fin 3 → F) k)
    (π : P →* R) (hdiagram : π.comp f = ρ)
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
      t^2*(1-t^7/((1+t)^3*(1+t^2)^2)) :=
  optimized_completed_presentation_positive_core κs P generators hP hgen D localGenerators
    localMaps otherWords hlocalTwo hlocalGen hlocalWords hlayers words f hwords
    (layerMap_injective_of_comp F Dyadic.D f π 1 (by rw [hdiagram]; exact hρ1))
    (layerMap_injective_of_comp F Dyadic.D f π 2 (by rw [hdiagram]; exact hρ2))
    (fun k => (χ k).comp π)
    (fun j k => by
      change (χ k ((π.comp f) (Dyadic.Filtration.gen j))).toAdd = _
      rw [hdiagram]
      exact hχ j k)
    allRelations hpresentation hAllCover originalRelations hOriginalVanish hOriginalCover
    localRelation hLocalVanish globalLocalRelation hGlobalRow hConsequence hInitial t ht0 ht1

/-- The `ℚ` theorem is the instance `R = RetainedQuadratic.Q`. -/
theorem optimized_completed_presentation_positive_rat (hP : IsPGroup 2 P)
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
      t^2*(1-t^7/((1+t)^3*(1+t^2)^2)) :=
  optimized_completed_presentation_positive_retained κs P generators hP hgen D localGenerators
    localMaps otherWords hlocalTwo hlocalGen hlocalWords hlayers words f hwords
    RetainedQuadratic.Q RetainedQuadratic.dyadicMap RetainedQuadratic.dyadicMap_first_layer
    RetainedQuadratic.dyadicMap_second_layer RetainedQuadratic.dyadicCharacter
    RetainedQuadratic.dyadicCharacter_certificate π hdiagram allRelations hpresentation hAllCover
    originalRelations hOriginalVanish hOriginalCover localRelation hLocalVanish
    globalLocalRelation hGlobalRow hConsequence hInitial t ht0 ht1

end UnitDistance.Sqrt241.GS
