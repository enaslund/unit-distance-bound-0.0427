module

public import UnitDistance.SigmaCutLocalFamily

@[expose] public section
set_option backward.privateInPublic true


/-! Each of the actual twenty-seven defining words is a genuine relation
in its specified finite local group. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace UnitDistance.ArithmeticProP.SigmaCut
open GroupAugmentation ArithmeticLocalBlocks
abbrev LocalWord := (j : AllIndex) × FreeGroup (AllGeneratorType j)

def commWord {κ : Type} (a b : FreeGroup κ) : FreeGroup κ := a⁻¹*b⁻¹*a*b

def oddTameWord (p : ℕ) : FreeGroup (Fin 2) :=
  FreeGroup.of 1*FreeGroup.of 0*(FreeGroup.of 1)⁻¹*((FreeGroup.of 0)^p)⁻¹

def quadraticLocalWords : Fin 16 → LocalWord :=
  ![⟨some none,(FreeGroup.of (0 : Fin 1))^2⟩,
    ⟨some (some (.inl 0)),oddTameWord 3⟩,
    ⟨some (some (.inl 1)),oddTameWord 5⟩,
    ⟨some (some (.inl 2)),oddTameWord 7⟩,
    ⟨some (some (.inl 3)),oddTameWord 11⟩,
    ⟨some (some (.inl 4)),oddTameWord 13⟩,
    ⟨some (some (.inl 0)),(FreeGroup.of (0 : Fin 2))^2⟩,
    ⟨some (some (.inl 1)),(FreeGroup.of (0 : Fin 2))^2⟩,
    ⟨some (some (.inl 2)),(FreeGroup.of (0 : Fin 2))^2⟩,
    ⟨some (some (.inl 3)),(FreeGroup.of (0 : Fin 2))^2⟩,
    ⟨some (some (.inl 4)),(FreeGroup.of (0 : Fin 2))^2⟩,
    ⟨none,(FreeGroup.of (0 : Fin 3))^2⟩,
    ⟨none,commWord (FreeGroup.of (0 : Fin 3)) (FreeGroup.of (1 : Fin 3))⟩,
    ⟨none,commWord (FreeGroup.of (0 : Fin 3)) (FreeGroup.of (2 : Fin 3))⟩,
    ⟨some (some (.inl 0)),(FreeGroup.of (1 : Fin 2))^2⟩,
    ⟨some (some (.inl 1)),(FreeGroup.of (1 : Fin 2))^2⟩]

def cubicLocalWord : LocalWord :=
  ⟨none,commWord (commWord (FreeGroup.of (1 : Fin 3)) (FreeGroup.of (2 : Fin 3))) (FreeGroup.of (2 : Fin 3))⟩

def deepLocalWords : Fin 10 → LocalWord :=
  ![⟨none,(FreeGroup.of (2 : Fin 3))^4⟩,
    ⟨none,(commWord (FreeGroup.of (1 : Fin 3)) (FreeGroup.of (2 : Fin 3)))^2⟩,
    ⟨some (some (.inl 2)),(FreeGroup.of (1 : Fin 2))^4⟩,
    ⟨some (some (.inl 3)),(FreeGroup.of (1 : Fin 2))^4⟩,
    ⟨some (some (.inl 4)),(FreeGroup.of (1 : Fin 2))^4⟩,
    ⟨some (some (.inr 0)),(FreeGroup.of (0 : Fin 1))^4⟩,
    ⟨some (some (.inr 1)),(FreeGroup.of (0 : Fin 1))^4⟩,
    ⟨some (some (.inr 2)),(FreeGroup.of (0 : Fin 1))^4⟩,
    ⟨some (some (.inr 3)),(FreeGroup.of (0 : Fin 1))^4⟩,
    ⟨some (some (.inr 4)),(FreeGroup.of (0 : Fin 1))^4⟩]

def localWordEvaluation (w : LocalWord) : allGroup w.1 := FreeGroup.lift (allGenerators w.1) w.2

def sourceWordEvaluation (w : LocalWord) : Source := FreeGroup.lift (allSource w.1) w.2

theorem quadraticLocalWords_vanish (i : Fin 16) : localWordEvaluation (quadraticLocalWords i)=1 := by
  fin_cases i <;>
    dsimp [localWordEvaluation,quadraticLocalWords,allGenerators,ArithmeticLocalBlocks.generators,
      allGroup,LocalGroup,oddTameWord,commWord]
  all_goals try simp only [map_mul,map_inv,map_pow,FreeGroup.lift_apply_of]
  all_goals decide +kernel

theorem cubicLocalWord_vanish : localWordEvaluation cubicLocalWord=1 := by
  dsimp [localWordEvaluation,cubicLocalWord,allGenerators,allGroup,commWord]
  try simp only [map_mul,map_inv,FreeGroup.lift_apply_of]
  decide +kernel

theorem deepLocalWords_vanish (i : Fin 10) : localWordEvaluation (deepLocalWords i)=1 := by
  fin_cases i <;>
    dsimp [localWordEvaluation,deepLocalWords,allGenerators,ArithmeticLocalBlocks.generators,
      allGroup,LocalGroup,commWord]
  all_goals try simp only [map_mul,map_inv,map_pow,FreeGroup.lift_apply_of]
  all_goals decide +kernel

theorem allSource_dyadic : allSource none=![dyadicX,dyadicY,dyadicZ] := by
  funext i
  fin_cases i <;>
    simp [allSource,SigmaDyadic.globalXYZ,SigmaDyadic.localXYZ,local_x,local_y,local_z]

theorem quadraticLocalWords_source (i : Fin 16) : sourceWordEvaluation (quadraticLocalWords i)=quadratics i := by
  fin_cases i <;>
    dsimp [sourceWordEvaluation,quadraticLocalWords,allSource,otherSource]
  all_goals simp [
      SigmaDyadic.globalXYZ,SigmaDyadic.localXYZ,local_x,local_y,local_z,
      commWord,oddTameWord,quadratics,TruncatedMagnus.Certificate.presentationWords]

theorem cubicLocalWord_source : sourceWordEvaluation cubicLocalWord=cubical := by
  simp [sourceWordEvaluation,cubicLocalWord,allSource_dyadic,commWord,cubical,
    TruncatedMagnus.Certificate.dyadicWord]

theorem deepLocalWords_source (i : Fin 10) : sourceWordEvaluation (deepLocalWords i)=deep actualExtra i := by
  fin_cases i <;>
    dsimp [sourceWordEvaluation,deepLocalWords,allSource,otherSource]
  all_goals simp [
      SigmaDyadic.globalXYZ,SigmaDyadic.localXYZ,local_x,local_y,local_z,
      commWord,deep,RetainedQuadratic.Cut.deepWords]

/-- Every defining cut is the image of a literal relation in a specified
finite local block; this is the actual presentation-coverage certificate. -/
theorem cut_local_word_cover (s : Source) (hs : s∈relations actualExtra) :
    ∃w : LocalWord,localWordEvaluation w=1 ∧ sourceWordEvaluation w=s := by
  rcases hs with (⟨i,rfl⟩ | rfl) | ⟨i,rfl⟩
  · exact ⟨quadraticLocalWords i,quadraticLocalWords_vanish i,quadraticLocalWords_source i⟩
  · exact ⟨cubicLocalWord,cubicLocalWord_vanish,cubicLocalWord_source⟩
  · exact ⟨deepLocalWords i,deepLocalWords_vanish i,deepLocalWords_source i⟩

end UnitDistance.ArithmeticProP.SigmaCut

namespace UnitDistance.ArithmeticProP.SigmaCut
open GroupAugmentation ArithmeticLocalBlocks

def originalLocalWords : Fin 6 → ((j : Index) × FreeGroup (GeneratorType j)) :=
  ![⟨none,(FreeGroup.of (0 : Fin 1))^2⟩,
    ⟨some (.inl 0),oddTameWord 3⟩,
    ⟨some (.inl 1),oddTameWord 5⟩,
    ⟨some (.inl 2),oddTameWord 7⟩,
    ⟨some (.inl 3),oddTameWord 11⟩,
    ⟨some (.inl 4),oddTameWord 13⟩]

theorem originalLocalWords_vanish (i : Fin 6) :
    FreeGroup.lift (ArithmeticLocalBlocks.generators (originalLocalWords i).1)
      (originalLocalWords i).2=1 := by
  fin_cases i <;>
    dsimp [originalLocalWords,ArithmeticLocalBlocks.generators,oddTameWord,GeneratorType,LocalGroup]
  all_goals try simp only [map_mul,map_inv,map_pow,FreeGroup.lift_apply_of]
  all_goals decide +kernel

theorem originalLocalWords_source (i : Fin 6) :
    FreeGroup.lift (otherSource (originalLocalWords i).1) (originalLocalWords i).2=
      (sigmaOriginalRelator i : Source) := by
  fin_cases i <;>
    dsimp [originalLocalWords,otherSource]
  all_goals simp [oddTameWord,sigmaOriginalRelator,
      UniversalQuadratic.oddPrimes] <;> rfl

end UnitDistance.ArithmeticProP.SigmaCut
