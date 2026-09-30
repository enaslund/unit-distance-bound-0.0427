module

public import UnitDistance.SigmaOriginalRelators
public import UnitDistance.ProfiniteGeneratedTameFiniteImage

@[expose] public section
set_option backward.privateInPublic true


/-! The selected actual odd inertia and decomposition generators generate
their images in every continuous discrete quotient of the arithmetic group. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.ArithmeticProP
variable {P : Type*} [Group P] [TopologicalSpace P] [DiscreteTopology P]

theorem sigmaOdd_discrete_generation (i : Fin 5) (f : SigmaGroup →ₜ* P) :
    (∀ x : SigmaOddInertia i,∃ n : ℤ,
      f (sigmaOddInertiaMap i x)=f (sigmaOddInertia i)^n) ∧
    (∀ y : SigmaOddDecomposition i,f (sigmaOddDecompositionMap i y)∈
      Subgroup.closure ({f (sigmaOddInertia i),f (sigmaOddFrobenius i)} : Set P)) :=
  ProfiniteTame.discrete_image_generates (sigmaOddInertiaMap i) (sigmaOddDecompositionMap i)
    (sigmaOddInertia i) (sigmaOddFrobenius i) (sigmaOdd_quotientGenerates i) f

theorem sigmaOdd_inertia_range (i : Fin 5) (f : SigmaGroup →ₜ* P) :
    (f.comp (sigmaOddInertiaMap i)).toMonoidHom.range=Subgroup.zpowers (f (sigmaOddInertia i)) := by
  apply le_antisymm
  · rintro g ⟨x,rfl⟩
    obtain ⟨n,hn⟩ := (sigmaOdd_discrete_generation i f).1 x
    exact ⟨n,hn.symm⟩
  · apply Subgroup.zpowers_le.mpr
    exact ⟨sigmaAbsoluteOddInertia i,rfl⟩

theorem sigmaOdd_decomposition_range (i : Fin 5) (f : SigmaGroup →ₜ* P) :
    (f.comp (sigmaOddDecompositionMap i)).toMonoidHom.range=
      Subgroup.closure ({f (sigmaOddInertia i),f (sigmaOddFrobenius i)} : Set P) := by
  apply le_antisymm
  · rintro g ⟨x,rfl⟩
    exact (sigmaOdd_discrete_generation i f).2 x
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases hg with rfl | rfl
    · exact ⟨(sigmaAbsoluteOddInertia i).val,rfl⟩
    · exact ⟨sigmaAbsoluteOddFrobenius i,rfl⟩

end UnitDistance.ArithmeticProP
