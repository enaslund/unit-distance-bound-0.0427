module

public import UnitDistance.SigmaCutCyclic

@[expose] public section
set_option backward.privateInPublic true


/-! The actual extra-prime decomposition and inertia images in every finite
cut quotient: cyclic order four and trivial inertia when M is retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.ArithmeticProP.SigmaCut
open OddLocal SigmaUnramified
open ProCGroups.Presentations

private theorem cyclicHom_range {H : Type*} [Group H] (n : ℕ) (f : Cyclic n →* H) :
    f.range=Subgroup.zpowers (f (cyclicGenerator n)) := by
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    obtain ⟨k,rfl⟩ := cyclic_eq_generator_zpow n x
    rw [map_zpow]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
  · exact Subgroup.zpowers_le.mpr ⟨cyclicGenerator n,rfl⟩

variable
  (hgen : closedNormalClosure (Set.range (fun i ↦ (sigmaOriginalRelator i : Source)))=
    (sigmaRelationKernel : Subgroup Source))

theorem extra_arithmeticProjection (i : Fin 5) :
    arithmeticProjection ExtraPrime.freeFrobenius hgen (ExtraPrime.sigmaFrobenius i)=
      extraElement ExtraPrime.freeFrobenius i := by
  rw [←ExtraPrime.freeFrobenius_image i,arithmeticProjection_free]
  rfl

variable {H : Type*} [Group H] [TopologicalSpace H] [DiscreteTopology H]
  (q : Quotient ExtraPrime.freeFrobenius →ₜ* H)

def extraDecompositionMap (i : Fin 5) : PrimeCompletion.AbsoluteDecomposition (ExtraPrime.prime i) →ₜ* H :=
  (q.comp (arithmeticProjection ExtraPrime.freeFrobenius hgen)).comp
    (decompositionMap (ExtraPrime.prime i))

/-- The full chosen absolute decomposition image equals the actual C4 image. -/
theorem extra_decomposition_range (i : Fin 5) :
    (extraDecompositionMap hgen q i).toMonoidHom.range=
      (q.toMonoidHom.comp (extraMap ExtraPrime.freeFrobenius i)).range := by
  rw [cyclicHom_range 4]
  change ((q.comp (arithmeticProjection ExtraPrime.freeFrobenius hgen)).comp
    (decompositionMap (ExtraPrime.prime i))).toMonoidHom.range=_
  rw [decomposition_range_eq_zpowers (ExtraPrime.prime i) (ExtraPrime.outside_support i)]
  change Subgroup.zpowers (q (arithmeticProjection ExtraPrime.freeFrobenius hgen
    (ExtraPrime.sigmaFrobenius i)))=Subgroup.zpowers (q (extraMap ExtraPrime.freeFrobenius i (cyclicGenerator 4)))
  rw [extra_arithmeticProjection]
  simp [extraMap]

/-- Actual inertia is killed before any additional global cuts. -/
theorem extra_inertia_killed (i : Fin 5)
    (τ : PrimeCompletion.AbsoluteInertia (ExtraPrime.prime i)) :
    extraDecompositionMap hgen q i τ.val=1 := by
  change q (arithmeticProjection ExtraPrime.freeFrobenius hgen
    (decompositionMap (ExtraPrime.prime i) τ.val))=1
  rw [inertia_killed (ExtraPrime.prime i) (ExtraPrime.outside_support i),map_one,map_one]

/-- Every finite quotient still mapping to M contains the same exact C4
local subgroup. -/
theorem extra_finiteMap_injective (r : H →* RetainedQuadratic.Q)
    (hr : r.comp q.toMonoidHom=(retained ExtraPrime.freeFrobenius).toMonoidHom) (i : Fin 5) :
    Function.Injective (q.toMonoidHom.comp (extraMap ExtraPrime.freeFrobenius i)) := by
  intro x y h
  apply RetainedCyclic.cyclicMap_injective 4 (sigmaFreeRetainedMap (ExtraPrime.freeFrobenius i))
    (extraRetained_fourth _ i) (ExtraPrime.retained_order i _ (ExtraPrime.freeFrobenius_base i))
  change extraRetained ExtraPrime.freeFrobenius i x=extraRetained ExtraPrime.freeFrobenius i y
  rw [←DFunLike.congr_fun (extraMap_retained _ i) x,←DFunLike.congr_fun (extraMap_retained _ i) y]
  change retained ExtraPrime.freeFrobenius (extraMap ExtraPrime.freeFrobenius i x)=
    retained ExtraPrime.freeFrobenius (extraMap ExtraPrime.freeFrobenius i y)
  have hcomp (z : Quotient ExtraPrime.freeFrobenius) : r (q z)=retained ExtraPrime.freeFrobenius z :=
    DFunLike.congr_fun hr z
  rw [←hcomp,←hcomp]
  exact congrArg r h

/-- Exact cardinality four for the actual decomposition image. -/
theorem extra_decomposition_card (r : H →* RetainedQuadratic.Q)
    (hr : r.comp q.toMonoidHom=(retained ExtraPrime.freeFrobenius).toMonoidHom) (i : Fin 5) :
    Nat.card (extraDecompositionMap hgen q i).toMonoidHom.range=4 := by
  rw [extra_decomposition_range hgen q i]
  have he := MonoidHom.ofInjective (extra_finiteMap_injective q r hr i)
  rw [←Nat.card_congr he.toEquiv]
  simp [Cyclic,Nat.card_eq_fintype_card]

end UnitDistance.ArithmeticProP.SigmaCut
