module

public import UnitDistance.SigmaCutOdd
public import UnitDistance.SigmaOddLocalImage

@[expose] public section
set_option backward.privateInPublic true


/-! The actual odd local images in each discrete quotient of the arithmetic
cut. Retaining M gives exact inertia and decomposition cardinalities. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.ArithmeticProP.SigmaCut
open ProCGroups.Presentations

variable (s : Fin 5 → Source)
  (hgen : closedNormalClosure (Set.range (fun i ↦ (sigmaOriginalRelator i : Source)))=
    (sigmaRelationKernel : Subgroup Source))

theorem retained_arithmeticProjection (g : SigmaGroup) :
    retained s (arithmeticProjection s hgen g)=sigmaRetainedModelMap g := by
  obtain ⟨x,rfl⟩ := sigmaFreeMap_surjective g
  rw [arithmeticProjection_free,retained_projection]
  rfl

theorem oddInertia_arithmeticProjection (i : Fin 5) :
    arithmeticProjection s hgen (sigmaOddInertia i)=oddInertia s i := by
  rw [←sigmaFreeOddInertia_image,arithmeticProjection_free]
  rfl

theorem oddFrobenius_arithmeticProjection (i : Fin 5) :
    arithmeticProjection s hgen (sigmaOddFrobenius i)=oddFrobenius s i := by
  rw [←sigmaFreeOddFrobenius_image,arithmeticProjection_free]
  rfl

variable {H : Type*} [Group H] [TopologicalSpace H] [DiscreteTopology H]
  (q : Quotient s →ₜ* H)

def oddDecompositionMap (i : Fin 5) : SigmaOddDecomposition i →ₜ* H :=
  (q.comp (arithmeticProjection s hgen)).comp (sigmaOddDecompositionMap i)

def oddInertiaMap (i : Fin 5) : SigmaOddInertia i →ₜ* H :=
  (q.comp (arithmeticProjection s hgen)).comp (sigmaOddInertiaMap i)

theorem odd_decomposition_range (i : Fin 5) :
    (oddDecompositionMap s hgen q i).toMonoidHom.range=
      (q.toMonoidHom.comp (oddMap s i)).range := by
  unfold oddDecompositionMap
  rw [sigmaOdd_decomposition_range,MonoidHom.range_comp]
  change Subgroup.closure ({q (arithmeticProjection s hgen (sigmaOddInertia i)),
      q (arithmeticProjection s hgen (sigmaOddFrobenius i))} : Set H)=_
  rw [oddInertia_arithmeticProjection,oddFrobenius_arithmeticProjection]
  have hr : (oddMap s i).range=Subgroup.closure
      ({oddInertia s i,oddFrobenius s i} : Set (Quotient s)) := OddLocal.map_range ..
  rw [hr,MonoidHom.map_closure]
  simp only [Set.image_insert_eq,Set.image_singleton]
  rfl

theorem odd_local_image_cards (r : H →* RetainedQuadratic.Q)
    (hr : r.comp q.toMonoidHom=(retained s).toMonoidHom) (i : Fin 5) :
    Nat.card (oddInertiaMap s hgen q i).toMonoidHom.range=2 ∧
      Nat.card (oddDecompositionMap s hgen q i).toMonoidHom.range=2*OddLocal.residueDegree i := by
  apply sigmaOdd_local_image_cards (q.comp (arithmeticProjection s hgen)) r
  · intro g
    change r (q (arithmeticProjection s hgen g))=sigmaRetainedModelMap g
    have he := DFunLike.congr_fun hr (arithmeticProjection s hgen g)
    exact he.trans (retained_arithmeticProjection s hgen g)
  · change q (arithmeticProjection s hgen (sigmaOddInertia i))^2=1
    rw [oddInertia_arithmeticProjection,←map_pow,oddInertia_square,map_one]
  · change q (arithmeticProjection s hgen (sigmaOddFrobenius i))^OddLocal.residueDegree i=1
    rw [oddFrobenius_arithmeticProjection,←map_pow,oddFrobenius_power,map_one]

end UnitDistance.ArithmeticProP.SigmaCut
