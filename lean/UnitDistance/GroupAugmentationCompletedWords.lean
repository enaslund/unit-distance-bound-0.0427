module

public import UnitDistance.GroupAugmentationProTwoFox
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual completed free words and finite affine Fox evaluation

Completed relators are elements of the actual profinite completion of the
ordinary free group. Every evaluation into a finite group extends by the
proved universal property. Density supplies actual words matching any finite
list of evaluations. In particular the affine derivative evaluation is
literal and does not replace completed relators by abstract defining words.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace UnitDistance.GroupAugmentation
universe u
variable (ι : Type u)

/-- The actual profinite completion, retaining all finite evaluations.
The pro-2 presentation test below only tests finite 2-groups. -/
abbrev CompletedWords : ProfiniteGrp.{u} :=
  ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (FreeGroup ι))

/-- Ordinary words are mapped into their actual completion. -/
def wordCompletion : FreeGroup ι →* CompletedWords ι :=
  (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of (FreeGroup ι))).hom

variable {ι}
variable (Q : Type u) [Group Q] [Finite Q]

instance finiteTarget_discrete :
    DiscreteTopology (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of Q)) := ⟨rfl⟩

/-- The unique continuous finite evaluation extending an actual word
homomorphism. The target carries its discrete finite topology. -/
def completedFiniteMap (f : FreeGroup ι →* Q) :
    CompletedWords ι ⟶ ProfiniteGrp.ofFiniteGrp (FiniteGrp.of Q) :=
  ProfiniteGrp.ProfiniteCompletion.lift (GrpCat.ofHom f)

@[simp] theorem completedFiniteMap_word (f : FreeGroup ι →* Q) (w : FreeGroup ι) :
    completedFiniteMap Q f (wordCompletion ι w) = f w := by
  have he := ProfiniteGrp.ProfiniteCompletion.lift_eta
    (P := ProfiniteGrp.ofFiniteGrp (FiniteGrp.of Q)) (GrpCat.ofHom f)
  exact ConcreteCategory.congr_hom he w

/-- Each completed word has an ordinary word with exactly the same chosen
finite evaluation. This is a proved finite approximation statement. -/
theorem exists_word_matching (f : FreeGroup ι →* Q) (r : CompletedWords ι) :
    ∃ w : FreeGroup ι, f w = completedFiniteMap Q f r := by
  let E := completedFiniteMap Q f
  have hopen : IsOpen (E ⁻¹' {E r}) :=
    (isOpen_discrete _).preimage E.hom.continuous_toFun
  obtain ⟨w,hw⟩ := (ProfiniteGrp.ProfiniteCompletion.denseRange (G := GrpCat.of (FreeGroup ι))).exists_mem_open hopen ⟨r,rfl⟩
  change E (wordCompletion ι w) = E r at hw
  exact ⟨w,by simpa [E] using hw⟩

variable (Q' : Type u) [Group Q'] [Finite Q']

/-- Simultaneous finite approximation, used for the affine derivative and
an actual finite quotient test at the same time. -/
theorem exists_word_matching_pair (f : FreeGroup ι →* Q) (f' : FreeGroup ι →* Q')
    (r : CompletedWords ι) : ∃ w : FreeGroup ι,
      f w = completedFiniteMap Q f r ∧ f' w = completedFiniteMap Q' f' r := by
  let E := completedFiniteMap Q f
  let E' := completedFiniteMap Q' f'
  have hopen : IsOpen ((E ⁻¹' {E r}) ∩ (E' ⁻¹' {E' r})) :=
    ((isOpen_discrete _).preimage E.hom.continuous_toFun).inter
      ((isOpen_discrete _).preimage E'.hom.continuous_toFun)
  obtain ⟨w,hw⟩ := (ProfiniteGrp.ProfiniteCompletion.denseRange (G := GrpCat.of (FreeGroup ι))).exists_mem_open hopen ⟨r,rfl,rfl⟩
  change E (wordCompletion ι w) = E r ∧ E' (wordCompletion ι w) = E' r at hw
  exact ⟨w,by simpa [E,E'] using hw⟩

variable (G : Type u) [Group G] [Finite G] [Fintype ι]
local notation "F" => ZMod 2
variable (generators : ι → G)

/-- Actual completed affine evaluation into a proved finite group. -/
def completedFoxLift := completedFiniteMap (FoxAffine F G (ι := ι)) (foxLift F G generators)

def completedFoxDerivative (r : CompletedWords ι) : ι → A F G :=
  (completedFoxLift G generators r).left.toAdd

def completedWordEvaluation (r : CompletedWords ι) : G :=
  (completedFoxLift G generators r).right

@[simp] theorem completedFoxDerivative_word (w : FreeGroup ι) :
    completedFoxDerivative G generators (wordCompletion ι w) = foxDerivative F G generators w := by
  simp [completedFoxDerivative,completedFoxLift,foxDerivative]

@[simp] theorem completedWordEvaluation_word (w : FreeGroup ι) :
    completedWordEvaluation G generators (wordCompletion ι w) = FreeGroup.lift generators w := by
  simp [completedWordEvaluation,completedFoxLift,foxLift_right]

/-- The actual fundamental identity extends to every completed relator by
matching its entire finite affine evaluation with an ordinary word. -/
theorem completedFoxDerivative_fundamental (r : CompletedWords ι) :
    foxMap F G generators (completedFoxDerivative G generators r) =
      delta F (completedWordEvaluation G generators r)-1 := by
  obtain ⟨w,hw⟩ := exists_word_matching (FoxAffine F G (ι := ι)) (foxLift F G generators) r
  have hd := congrArg (fun a : FoxAffine F G (ι := ι) => a.left.toAdd) hw
  have hg := congrArg (fun a : FoxAffine F G (ι := ι) => a.right) hw
  change foxDerivative F G generators w = completedFoxDerivative G generators r at hd
  change (foxLift F G generators w).right = completedWordEvaluation G generators r at hg
  rw [foxLift_right] at hg
  rw [← hd,← hg]
  exact foxDerivative_fundamental F G generators w

end UnitDistance.GroupAugmentation
