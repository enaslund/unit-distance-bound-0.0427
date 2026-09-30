module

public import UnitDistance.UniversalQuadraticGroup
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.FreeProC.Basic

@[expose] public section
set_option backward.privateInPublic true


/-!
# The universal quadratic detector of an actual free pro-two group

The finite class-two group is a pro-two group. Its seven specified generators
therefore extend through the actual free universal property; a detector map
need not be supplied as an independent existence hypothesis.
-/

noncomputable section

namespace UnitDistance.UniversalQuadratic

open ProCGroups ProCGroups.ProC ProCGroups.FreeProC

theorem hasPGroupOpenNormalBasis : HasPGroupOpenNormalBasis 2 Q := by
  apply HasOpenNormalBasisInClass.of_allOpenNormalQuotients
  intro U
  exact ⟨inferInstance, isTwoGroup.of_surjective (QuotientGroup.mk' (U : Subgroup Q))
    (QuotientGroup.mk'_surjective (U : Subgroup Q))⟩

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {x : Fin 7 → G}

/-- The actual continuous detector provided by the free universal property. -/
def freeDetector (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x) :
    G →ₜ* Q :=
  hfree.liftHom hasPGroupOpenNormalBasis generator continuous_of_discreteTopology

@[simp] theorem freeDetector_generator
    (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x) (i : Fin 7) :
    freeDetector hfree (x i) = generator i :=
  hfree.liftHom_apply hasPGroupOpenNormalBasis generator continuous_of_discreteTopology i

@[simp] theorem freeDetector_generator_base
    (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x) (i : Fin 7) :
    (freeDetector hfree (x i)).base = Pi.single i 1 := by
  rw [freeDetector_generator]
  rfl

end UnitDistance.UniversalQuadratic
