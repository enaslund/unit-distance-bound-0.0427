module

public import UnitDistance.Sqrt241.Presentation.Relators
public import UnitDistance.Sqrt241.Relation.Bound

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# The seven relators present `G_B`

`G_B ≅ F(8)/R` (`Tower.freeQuotientEquiv`). If the seven relators `A.relators r` of
lifts `A` with the labels of construction.md §3.4 have trivial image in `G_B`, their
closed normal closure is the whole relation kernel `R`
(`relators_generate`): their universal initials have the dual matrix of
`Universal.coordinate_initial` and `dim H²(G_B) ≤ 7` (`Relation.OmegaB_h2`, transported
along the bridge `Tower.bridge`). The parametric form `relators_generate_of_h2` takes the
bound as a hypothesis. In particular the lifted genuine relation at `𝔭₁` is a
consequence of the seven relators: `presentation : A.Presentation r` (the
presentation hypothesis `Cut.SourceLifts.Presentation` of the cut).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Presentation

open Tower GroupData ClassTwo ProCGroups ProCGroups.ProC ProCGroups.Presentations
open ClassFieldTower.ProP ClassFieldTower.Cohomology

/-- The seven relators (and the genuine relation at `𝔭₁`) have trivial image
in `G_B`. -/
structure RelatorsTrivial (A : Cut.SourceLifts) (r : Cut.LocalSource) : Prop where
  conj : ∀ k, freeMap (A.conj k) ^ 2 = 1
  tame : ∀ q, Lifts.tameWord (tameNorm q) (freeMap (A.tameInertia q))
    (freeMap (A.tameFrobenius q)) = 1
  dyadic : ∀ P, freeMap (A.dyadic P r) = 1

theorem relators_mem (A : Cut.SourceLifts) (r : Cut.LocalSource) (h : RelatorsTrivial A r)
    (i : Fin 7) : A.relators r i ∈ (relationKernel : Subgroup Free) := by
  rw [mem_relationKernel_iff]
  fin_cases i
  · change freeMap (A.conj 0 ^ 2) = 1
    rw [map_pow]
    exact h.conj 0
  · change freeMap (A.conj 1 ^ 2) = 1
    rw [map_pow]
    exact h.conj 1
  all_goals first
    | exact h.dyadic 1
    | (change freeMap.toMonoidHom
          (Lifts.tameWord (tameNorm _) (A.tameInertia _) (A.tameFrobenius _)) = 1
       rw [Lifts.map_tameWord freeMap.toMonoidHom]
       exact h.tame _)

/-- The relators as elements of the relation kernel. -/
def relatorElt (A : Cut.SourceLifts) (r : Cut.LocalSource) (h : RelatorsTrivial A r) :
    Fin 7 → relationKernel :=
  fun i ↦ ⟨A.relators r i, relators_mem A r h i⟩

theorem range_relatorElt (A : Cut.SourceLifts) (r : Cut.LocalSource) (h : RelatorsTrivial A r) :
    Set.range (fun i ↦ (relatorElt A r h i : Free)) = Set.range (A.relators r) :=
  rfl

/-- **Presentation, parametric form.** With the relation bound on `G_B` as a
hypothesis. -/
theorem relators_generate_of_h2 (A : Cut.SourceLifts) (hL : A.Labels) (r : Cut.LocalSource)
    (hr : Dyadic.ArithmeticPresentation.detector r = FreeThreeQuadratic.relation)
    (h : RelatorsTrivial A r)
    [FiniteDimensional (ZMod 2) (continuousCohomologyZModPLifted 2 GB 2)]
    (hbound : Module.finrank (ZMod 2) (continuousCohomologyZModPLifted 2 GB 2) ≤ 7) :
    closedNormalClosure (Set.range (A.relators r)) = (relationKernel : Subgroup Free) := by
  let e := continuousCohomologyZModPLiftedLinearEquiv (p := 2) freeQuotientEquiv 2
  have : FiniteDimensional (ZMod 2)
      (continuousCohomologyZModPLifted 2 (Free ⧸ (relationKernel : Subgroup Free)) 2) :=
    e.finiteDimensional
  rw [← range_relatorElt A r h]
  apply closedNormalClosure_eq_of_initials Universal.cocycle
    (FiniteFreeProTwo.isFree 8).hasOpenNormalBasisInClass relationKernel relationKernel_le_frattini
    (relatorElt A r h) detector Universal.coordinate Universal.initial
    (relators_central A hL r hr) Universal.coordinate_initial
  rw [← e.finrank_eq]
  exact hbound

/-- `dim H²(F(8)/R) ≤ 7` (`Relation.OmegaB_h2` through the bridge and `freeQuotientEquiv`). -/
theorem freeQuotient_h2 :
    FiniteDimensional (ZMod 2)
        (continuousCohomologyZModPLifted 2 (Free ⧸ (relationKernel : Subgroup Free)) 2) ∧
      Module.finrank (ZMod 2)
        (continuousCohomologyZModPLifted 2 (Free ⧸ (relationKernel : Subgroup Free)) 2) ≤ 7 :=
  Relation.h2_le_seven_of_continuousMulEquiv (bridge.trans freeQuotientEquiv.symm)

/-- `dim H²(G_B) ≤ 7` (`Relation.OmegaB_h2` through the bridge). -/
theorem GB_h2 :
    FiniteDimensional (ZMod 2) (continuousCohomologyZModPLifted 2 GB 2) ∧
      Module.finrank (ZMod 2) (continuousCohomologyZModPLifted 2 GB 2) ≤ 7 :=
  Relation.h2_le_seven_of_continuousMulEquiv bridge

/-- **Presentation.** The seven relators normally generate the relation kernel
(unconditional: the relation bound is `Relation.OmegaB_h2`). -/
theorem relators_generate (A : Cut.SourceLifts) (hL : A.Labels) (r : Cut.LocalSource)
    (hr : Dyadic.ArithmeticPresentation.detector r = FreeThreeQuadratic.relation)
    (h : RelatorsTrivial A r) :
    closedNormalClosure (Set.range (A.relators r)) = (relationKernel : Subgroup Free) := by
  obtain ⟨hfd, hb⟩ := GB_h2
  exact relators_generate_of_h2 A hL r hr h hb

/-- The genuine relation at `𝔭₁` is a consequence of the seven relators: the
presentation hypothesis `Cut.SourceLifts.Presentation` of the cut. -/
theorem presentation (A : Cut.SourceLifts) (hL : A.Labels) (r : Cut.LocalSource)
    (hr : Dyadic.ArithmeticPresentation.detector r = FreeThreeQuadratic.relation)
    (h : RelatorsTrivial A r) : A.Presentation r := by
  unfold Cut.SourceLifts.Presentation
  rw [relators_generate A hL r hr h]
  exact h.dyadic 0

end UnitDistance.Sqrt241.Presentation
