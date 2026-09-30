module

public import UnitDistance.RetainedMagnusGenus
public import UnitDistance.GroupAugmentationWordDegrees

@[expose] public section
set_option backward.privateInPublic true


/-! The full literal cut-presentation frontend. All ten degree-four words
have their actual augmentation depth proved, so the only remaining inputs
are the genuine free source and actual arithmetic genus coordinates. -/
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
namespace UnitDistance.RetainedQuadratic.Cut
open ProCGroups ProCGroups.ProC ProCGroups.FreeProC ProCGroups.Presentations
open TruncatedMagnus.Certificate (freeCut relatorTails presentationWords dyadicWord)

/-- The literal ten deep words: two dyadic, three tame Frobenius, and five extra-prime Frobenius cuts. -/
def deepWords {G : Type*} [Group G] (b d : G) (f s : Fin 5 → G) : Fin 10 → G :=
  ![d^4,(b⁻¹*d⁻¹*b*d)^2,(f 2)^4,(f 3)^4,(f 4)^4,
    (s 0)^4,(s 1)^4,(s 2)^4,(s 3)^4,(s 4)^4]

/-- These are literal augmentation-degree-four words in every actual group. -/
theorem deepWords_mem_dimension_four {G : Type*} [Group G] (b d : G) (f s : Fin 5 → G)
    (i : Fin 10) : deepWords b d f s i∈GroupAugmentation.dimensionSubgroup F G 4 := by
  fin_cases i
  · exact GroupAugmentation.fourth_pow_mem_dimension_four F G d
  · exact GroupAugmentation.commutator_square_mem_dimension_four F G b d
  · exact GroupAugmentation.fourth_pow_mem_dimension_four F G (f 2)
  · exact GroupAugmentation.fourth_pow_mem_dimension_four F G (f 3)
  · exact GroupAugmentation.fourth_pow_mem_dimension_four F G (f 4)
  · exact GroupAugmentation.fourth_pow_mem_dimension_four F G (s 0)
  · exact GroupAugmentation.fourth_pow_mem_dimension_four F G (s 1)
  · exact GroupAugmentation.fourth_pow_mem_dimension_four F G (s 2)
  · exact GroupAugmentation.fourth_pow_mem_dimension_four F G (s 3)
  · exact GroupAugmentation.fourth_pow_mem_dimension_four F G (s 4)

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] {x : Fin 7 → G}
  [TopologicalSpace Q] [DiscreteTopology Q]

/-- The complete twenty-seven-word cut retains the actual quadratic quotient
and admits a finite quotient with at least4096 conjugates of actual infinity. -/
theorem full_literal_cut_retains_and_detects
    (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x)
    (ρ : G →ₜ* Q) (hρ : ∀ i,(ρ (x i)).base=Pi.single i 1)
    (c : G) (t f : Fin 5 → G) (a b d : G) (s : Fin 5 → G)
    (hc : (ρ c).base=vector 1)
    (ht : ∀ i,(ρ (t i)).base=inertiaVector i)
    (hf : ∀ i,(ρ (f i)).base=frobeniusVector i)
    (ha : (ρ a).base=vector 2) (hb : (ρ b).base=vector 53) (hd : (ρ d).base=vector 89) :
    let N := closedNormalClosure (Set.range (presentationWords c t f a b d) ∪
      {dyadicWord b d} ∪ Set.range (deepWords b d f s))
    let ψ := freeCut hfree (relatorTails hfree (presentationWords c t f a b d))
    N ≤ ρ.toMonoidHom.ker ∧ N ≤ ψ.toMonoidHom.ker ∧
      4096 ≤ (Subgroup.centralizer
        ({(⟨ψ c,⟨c,rfl⟩⟩ : ψ.toMonoidHom.range)} : Set ψ.toMonoidHom.range)).index := by
  apply retained_and_cubic_cut_kernel hfree ρ hρ c t f a b d hc ht hf ha hb hd
  rintro g ⟨i,rfl⟩
  exact deepWords_mem_dimension_four b d f s i

end UnitDistance.RetainedQuadratic.Cut
