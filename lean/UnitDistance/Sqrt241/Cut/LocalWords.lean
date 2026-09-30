module

public import UnitDistance.Sqrt241.Cut.LocalFamily

@[expose] public section
set_option backward.privateInPublic true


/-!
# Every cut word is a local relation

Each of the thirty literal cut words is the image of a word in the generators
of one local block that is trivial in the finite local group (checked by
`decide +kernel` in the local group). This is the presentation-coverage
certificate of the local block family; the six words at `𝔭₁` come from the
distinguished block `none`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.Sqrt241.Cut
open GroupAugmentation GroupData

abbrev LocalWord := (j : SourceLifts.AllIndex) × FreeGroup (SourceLifts.AllGeneratorType j)

def commWord {κ : Type} (a b : FreeGroup κ) : FreeGroup κ := a⁻¹*b⁻¹*a*b

def tameLocalWord (N : ℕ) : FreeGroup (Fin 2) :=
  FreeGroup.of 1*FreeGroup.of 0*(FreeGroup.of 1)⁻¹*((FreeGroup.of 0)^N)⁻¹

abbrev realBlock (i : Fin 2) : SourceLifts.AllIndex := some (.inl i)
abbrev tameBlock (q : Fin 4) : SourceLifts.AllIndex := some (.inr (.inl q))
abbrev dyadicTwoBlock : SourceLifts.AllIndex := some (.inr (.inr (.inl ())))
abbrev capBlock (k : Fin 3) : SourceLifts.AllIndex := some (.inr (.inr (.inr k)))

def quadraticLocalWords : Fin 21 → LocalWord :=
  ![⟨realBlock 0,(FreeGroup.of (0 : Fin 1))^2⟩,
    ⟨realBlock 1,(FreeGroup.of (0 : Fin 1))^2⟩,
    ⟨tameBlock 0,tameLocalWord 3⟩,
    ⟨tameBlock 1,tameLocalWord 3⟩,
    ⟨tameBlock 2,tameLocalWord 5⟩,
    ⟨tameBlock 3,tameLocalWord 5⟩,
    ⟨dyadicTwoBlock,(FreeGroup.of (1 : Fin 3))^2⟩,
    ⟨none,(FreeGroup.of (0 : Fin 3))^2⟩,
    ⟨none,commWord (FreeGroup.of (0 : Fin 3)) (FreeGroup.of (1 : Fin 3))⟩,
    ⟨none,commWord (FreeGroup.of (0 : Fin 3)) (FreeGroup.of (2 : Fin 3))⟩,
    ⟨dyadicTwoBlock,(FreeGroup.of (0 : Fin 3))^2⟩,
    ⟨dyadicTwoBlock,commWord (FreeGroup.of (0 : Fin 3)) (FreeGroup.of (1 : Fin 3))⟩,
    ⟨dyadicTwoBlock,commWord (FreeGroup.of (0 : Fin 3)) (FreeGroup.of (2 : Fin 3))⟩,
    ⟨tameBlock 0,(FreeGroup.of (0 : Fin 2))^2⟩,
    ⟨tameBlock 1,(FreeGroup.of (0 : Fin 2))^2⟩,
    ⟨tameBlock 2,(FreeGroup.of (0 : Fin 2))^2⟩,
    ⟨tameBlock 3,(FreeGroup.of (0 : Fin 2))^2⟩,
    ⟨tameBlock 0,(FreeGroup.of (1 : Fin 2))^2⟩,
    ⟨tameBlock 1,(FreeGroup.of (1 : Fin 2))^2⟩,
    ⟨tameBlock 2,(FreeGroup.of (1 : Fin 2))^2⟩,
    ⟨tameBlock 3,(FreeGroup.of (1 : Fin 2))^2⟩]

def cubicLocalWords : Fin 2 → LocalWord :=
  ![⟨none,commWord (commWord (FreeGroup.of (1 : Fin 3)) (FreeGroup.of (2 : Fin 3)))
      (FreeGroup.of (2 : Fin 3))⟩,
    ⟨dyadicTwoBlock,commWord (commWord (FreeGroup.of (1 : Fin 3)) (FreeGroup.of (2 : Fin 3)))
      (FreeGroup.of (2 : Fin 3))⟩]

def deepLocalWords : Fin 7 → LocalWord :=
  ![⟨none,(FreeGroup.of (2 : Fin 3))^4⟩,
    ⟨none,(commWord (FreeGroup.of (1 : Fin 3)) (FreeGroup.of (2 : Fin 3)))^2⟩,
    ⟨dyadicTwoBlock,(FreeGroup.of (2 : Fin 3))^4⟩,
    ⟨dyadicTwoBlock,(commWord (FreeGroup.of (1 : Fin 3)) (FreeGroup.of (2 : Fin 3)))^2⟩,
    ⟨capBlock 0,(FreeGroup.of (0 : Fin 1))^4⟩,
    ⟨capBlock 1,(FreeGroup.of (0 : Fin 1))^4⟩,
    ⟨capBlock 2,(FreeGroup.of (0 : Fin 1))^4⟩]

def localWordEvaluation (w : LocalWord) : SourceLifts.allGroup w.1 :=
  FreeGroup.lift (SourceLifts.allGenerators w.1) w.2

theorem quadraticLocalWords_vanish (i : Fin 21) :
    localWordEvaluation (quadraticLocalWords i) = 1 := by
  fin_cases i <;>
    dsimp [localWordEvaluation,quadraticLocalWords,SourceLifts.allGenerators,localGenerators,
      SourceLifts.allGroup,LocalGroup,tameLocalWord,commWord]
  all_goals decide +kernel

theorem cubicLocalWords_vanish (i : Fin 2) : localWordEvaluation (cubicLocalWords i) = 1 := by
  fin_cases i <;>
    dsimp [localWordEvaluation,cubicLocalWords,SourceLifts.allGenerators,localGenerators,
      SourceLifts.allGroup,LocalGroup,commWord]
  all_goals decide +kernel

theorem deepLocalWords_vanish (i : Fin 7) : localWordEvaluation (deepLocalWords i) = 1 := by
  fin_cases i <;>
    dsimp [localWordEvaluation,deepLocalWords,SourceLifts.allGenerators,localGenerators,
      SourceLifts.allGroup,LocalGroup,commWord]
  all_goals decide +kernel

namespace SourceLifts
variable (A : SourceLifts)

def sourceWordEvaluation (w : LocalWord) : Source := FreeGroup.lift (A.allSource w.1) w.2

set_option maxHeartbeats 4000000 in
theorem quadraticLocalWords_source (i : Fin 21) :
    A.sourceWordEvaluation (quadraticLocalWords i) = A.lifts.quadraticWords i := by
  fin_cases i <;>
    dsimp [sourceWordEvaluation,quadraticLocalWords,allSource,otherSource]
  all_goals simp [dyadicXYZ,commWord,tameLocalWord,Lifts.quadraticWords,Lifts.tameWord,
    lifts,Dyadic.Presentation.comm,tameNorm]

theorem cubicLocalWords_source (P : Fin 2) :
    A.sourceWordEvaluation (cubicLocalWords P) = A.lifts.cubicWords P := by
  fin_cases P <;>
    dsimp [sourceWordEvaluation,cubicLocalWords,allSource,otherSource]
  all_goals simp [dyadicXYZ,commWord,Lifts.cubicWords,lifts,Dyadic.Presentation.comm]

theorem deepLocalWords_source (i : Fin 7) :
    A.sourceWordEvaluation (deepLocalWords i) = A.lifts.deepWords i := by
  fin_cases i <;>
    dsimp [sourceWordEvaluation,deepLocalWords,allSource,otherSource]
  all_goals simp [dyadicXYZ,commWord,Lifts.deepWords,lifts,Dyadic.Presentation.comm]

/-- Every literal cut word is the image of a relation of a local block. -/
theorem cut_local_word_cover (s : Source) (hs : s ∈ A.lifts.words) :
    ∃ w : LocalWord, localWordEvaluation w = 1 ∧ A.sourceWordEvaluation w = s := by
  rcases hs with (⟨i,rfl⟩ | ⟨P,rfl⟩) | ⟨i,rfl⟩
  · exact ⟨quadraticLocalWords i,quadraticLocalWords_vanish i,A.quadraticLocalWords_source i⟩
  · exact ⟨cubicLocalWords P,cubicLocalWords_vanish P,A.cubicLocalWords_source P⟩
  · exact ⟨deepLocalWords i,deepLocalWords_vanish i,A.deepLocalWords_source i⟩

/-- Local words for the six relators other than the genuine one at `𝔭₂`. -/
def relatorLocalWords : Fin 6 → ((j : Index) × FreeGroup (GeneratorType j)) :=
  ![⟨.inl 0,(FreeGroup.of (0 : Fin 1))^2⟩,
    ⟨.inl 1,(FreeGroup.of (0 : Fin 1))^2⟩,
    ⟨.inr (.inl 0),tameLocalWord 3⟩,
    ⟨.inr (.inl 1),tameLocalWord 3⟩,
    ⟨.inr (.inl 2),tameLocalWord 5⟩,
    ⟨.inr (.inl 3),tameLocalWord 5⟩]

theorem relatorLocalWords_vanish (i : Fin 6) :
    FreeGroup.lift (localGenerators (relatorLocalWords i).1) (relatorLocalWords i).2 = 1 := by
  fin_cases i <;>
    dsimp [relatorLocalWords,localGenerators,tameLocalWord,GeneratorType,LocalGroup]
  all_goals decide +kernel

theorem relatorLocalWords_source (r : LocalSource) (i : Fin 6) :
    FreeGroup.lift (A.otherSource (relatorLocalWords i).1) (relatorLocalWords i).2 =
      A.relators r ⟨i.val,by omega⟩ := by
  fin_cases i <;> dsimp [relatorLocalWords,otherSource]
  all_goals simp [tameLocalWord,relators,Lifts.tameWord,tameNorm]

end SourceLifts
end UnitDistance.Sqrt241.Cut
