module

public import UnitDistance.GroupAugmentationCompletedWords
public import UnitDistance.GroupAugmentationFoxSubstitution

@[expose] public section
set_option backward.privateInPublic true


/-!
# The actual Fox chain rule for completed local relators

Literal lifts of local generators induce an actual continuous map of free
profinite completions. The evaluated Fox chain rule extends to every
completed local word by simultaneous finite affine approximation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace UnitDistance.GroupAugmentation
universe u
variable {ι κ : Type u} (words : κ → FreeGroup ι)

/-- The actual continuous extension of the chosen literal generator lifts. -/
def completedSubstitution : CompletedWords κ ⟶ CompletedWords ι :=
  ProfiniteGrp.ProfiniteCompletion.lift
    (GrpCat.ofHom ((wordCompletion ι).comp (FreeGroup.lift words)))

@[simp] theorem completedSubstitution_word (w : FreeGroup κ) :
    completedSubstitution words (wordCompletion κ w) =
      wordCompletion ι (FreeGroup.lift words w) := by
  have he := ProfiniteGrp.ProfiniteCompletion.lift_eta
    (P := CompletedWords ι) (GrpCat.ofHom ((wordCompletion ι).comp (FreeGroup.lift words)))
  exact ConcreteCategory.congr_hom he w

variable (Q : Type u) [Group Q] [Finite Q]

/-- Any actual finite evaluation commutes with the completed substitution. -/
theorem completedFiniteMap_substitution (f : FreeGroup ι →* Q) (r : CompletedWords κ) :
    completedFiniteMap Q f (completedSubstitution words r) =
      completedFiniteMap Q (f.comp (FreeGroup.lift words)) r := by
  have he : completedSubstitution words ≫ completedFiniteMap Q f =
      completedFiniteMap Q (f.comp (FreeGroup.lift words)) := by
    apply ProfiniteGrp.ProfiniteCompletion.lift_unique
    apply GrpCat.ext
    intro w
    change completedFiniteMap Q f (completedSubstitution words (wordCompletion κ w)) =
      completedFiniteMap Q (f.comp (FreeGroup.lift words)) (wordCompletion κ w)
    simp
  have hh := ConcreteCategory.congr_hom he r
  simpa only [ProfiniteGrp.comp_apply] using hh

variable (G : Type u) [Group G] [Finite G] [Fintype ι] [Fintype κ]
local notation "F" => ZMod 2
variable (generators : ι → G)

/-- The chain rule for an actual completed local relator. -/
theorem completedFoxDerivative_substitution (r : CompletedWords κ) :
    completedFoxDerivative G generators (completedSubstitution words r) =
      foxSubstitution F G generators words
        (completedFoxDerivative G (fun j => FreeGroup.lift generators (words j)) r) := by
  obtain ⟨w,hwLocal,hwGlobal⟩ := exists_word_matching_pair
    (FoxAffine F G (ι := κ)) (FoxAffine F G (ι := ι))
    (foxLift F G (fun j => FreeGroup.lift generators (words j)))
    ((foxLift F G generators).comp (FreeGroup.lift words)) r
  have hL := congrArg (fun a : FoxAffine F G (ι := κ) => a.left.toAdd) hwLocal
  change foxDerivative F G (fun j => FreeGroup.lift generators (words j)) w =
    completedFoxDerivative G (fun j => FreeGroup.lift generators (words j)) r at hL
  rw [← completedFiniteMap_substitution words] at hwGlobal
  have hG := congrArg (fun a : FoxAffine F G (ι := ι) => a.left.toAdd) hwGlobal
  change foxDerivative F G generators (FreeGroup.lift words w) =
    completedFoxDerivative G generators (completedSubstitution words r) at hG
  rw [← hG,← hL]
  exact foxDerivative_substitution F G generators words w

end UnitDistance.GroupAugmentation
