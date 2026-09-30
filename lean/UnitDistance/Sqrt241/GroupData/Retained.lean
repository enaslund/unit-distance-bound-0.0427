module

public import UnitDistance.Sqrt241.GroupData.Universal
public import Mathlib.Topology.Instances.Discrete

@[expose] public section
set_option backward.privateInPublic true


/-!
# The retained quadratic model `Q_B` over `ℚ(√241)`

`Q_B = F₂⁸ × F₂¹⁵` with the bilinear law `β_B = red ∘ β_U`, where
`red : F₂³⁶ → F₂¹⁵` is an explicit reduction of the universal quadratic
layer whose kernel is exactly the span of the 21 quadratic cut initials
(`reduction_ker`, both inclusions from finite column identities). Thus
`Q_B` is the quotient of the universal class-two group by the quadratic
cut relations; it has order `2²³` (construction.md §3.4: `L₂ = 15`).
Nothing arithmetic is assumed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.Sqrt241.Retained
open ClassTwo GroupData

abbrev W := Fin 15 → F

/-- The retained bilinear law (lower triangular, 15 central coordinates). -/
def cocycle : V →ₗ[F] V →ₗ[F] W := bilinearOfMasks 8 15 retainedCocycleMasks

abbrev Q := GroupModel cocycle

instance : Group Q := inferInstanceAs (Group (GroupModel cocycle))
instance retainedTopology : TopologicalSpace Q := ⊥
instance retainedDiscrete : DiscreteTopology Q := ⟨rfl⟩
instance retainedTopologicalGroup : IsTopologicalGroup Q := inferInstance
instance retainedT2 : T2Space Q := inferInstance
instance retainedCompact : CompactSpace Q := inferInstance
instance retainedTotallyDisconnected : TotallyDisconnectedSpace Q := inferInstance

theorem isTwoGroup : IsPGroup 2 Q := GroupModel.isTwoGroup cocycle

theorem card_Q : Nat.card Q = 2^23 := by
  rw [Nat.card_congr (GroupModel.equivProd cocycle),Nat.card_prod]
  simp only [V,W,Nat.card_fun,Nat.card_fin,Nat.card_zmod]
  norm_num

open ProCGroups ProCGroups.ProC in
theorem hasPGroupOpenNormalBasis : HasPGroupOpenNormalBasis 2 Q := by
  apply HasOpenNormalBasisInClass.of_allOpenNormalQuotients
  intro U
  exact ⟨inferInstance,isTwoGroup.of_surjective (QuotientGroup.mk' (U : Subgroup Q))
    (QuotientGroup.mk'_surjective (U : Subgroup Q))⟩

/-! ### The reduction of the universal quadratic layer -/

/-- The reduction `F₂³⁶ → F₂¹⁵`. -/
def reduction : Universal.W →ₗ[F] W := columnMap 36 15 quadraticColumns

/-- The 21 quadratic cut initials, as bit masks. -/
def relationVector (i : Fin 21) : Universal.W := bits 36 (cutInitialMasks i)

def relationExpansion : (Fin 21 → F) →ₗ[F] Universal.W := columnMap 21 36 cutInitialMasks
def relationCoefficients : Universal.W →ₗ[F] (Fin 21 → F) :=
  columnMap 36 21 relationCoefficientColumns
def freeExpansion : W →ₗ[F] Universal.W := columnMap 15 36 freeColumnMasks

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem relation_reduction_certificate : ∀ (i : Fin 21) (k : Fin 15),
    reduction (relationVector i) k = 0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem decomposition_certificate : ∀ (j k : Fin 36),
    (relationExpansion (relationCoefficients (Pi.single j 1)) +
      freeExpansion (reduction (Pi.single j 1))) k = (Pi.single j (1 : F) : Universal.W) k := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem section_certificate : ∀ (j k : Fin 15),
    reduction (freeExpansion (Pi.single j 1)) k = (Pi.single j (1 : F) : W) k := by
  decide +kernel

attribute [local irreducible] reduction relationExpansion relationCoefficients freeExpansion

theorem reduction_relationVector (i : Fin 21) : reduction (relationVector i) = 0 :=
  funext (relation_reduction_certificate i)

/-- Every universal quadratic vector is its relation part plus its retained part. -/
theorem decomposition (v : Universal.W) :
    relationExpansion (relationCoefficients v) + freeExpansion (reduction v) = v := by
  have he : relationExpansion.comp relationCoefficients + freeExpansion.comp reduction =
      LinearMap.id := by
    apply linearMap_ext_single
    intro j
    simpa only [LinearMap.add_apply,LinearMap.comp_apply,LinearMap.id_apply]
      using funext (decomposition_certificate j)
  exact congrArg (fun f : Universal.W →ₗ[F] Universal.W => f v) he

theorem relationExpansion_apply (a : Fin 21 → F) :
    relationExpansion a = ∑ i, a i • relationVector i := by
  unfold relationExpansion
  rfl

/-- The kernel of the reduction is exactly the span of the 21 cut initials. -/
theorem reduction_ker : LinearMap.ker reduction = Submodule.span F (Set.range relationVector) := by
  apply le_antisymm
  · intro v hv
    have hz := LinearMap.mem_ker.mp hv
    rw [← decomposition v,hz,map_zero,add_zero,relationExpansion_apply]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)
  · apply Submodule.span_le.mpr
    rintro v ⟨i,rfl⟩
    exact reduction_relationVector i

/-- All 15 retained coordinates are realized. -/
theorem reduction_surjective : Function.Surjective reduction := by
  have he : reduction.comp freeExpansion = LinearMap.id := by
    apply linearMap_ext_single
    intro j
    simpa only [LinearMap.comp_apply,LinearMap.id_apply] using funext (section_certificate j)
  intro v
  exact ⟨freeExpansion v,congrArg (fun f : W →ₗ[F] W => f v) he⟩

/-! ### Compatibility with the universal law -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem cocycle_certificate : ∀ (i j : Fin 8) (k : Fin 15),
    cocycle (Pi.single i 1) (Pi.single j 1) k =
      reduction (Universal.cocycle (Pi.single i 1) (Pi.single j 1)) k := by
  decide +kernel

/-- The retained law is the reduction of the universal law. -/
theorem cocycle_eq (v w : V) : cocycle v w = reduction (Universal.cocycle v w) := by
  have h : cocycle = (Universal.cocycle.compr₂ reduction) := by
    apply linearMap_ext_single
    intro i
    apply linearMap_ext_single
    intro j
    exact funext (cocycle_certificate i j)
  rw [h]
  rfl

/-- The quotient map of the universal class-two group onto `Q_B`. -/
def reductionHom : Universal.Q →* Q where
  toFun g := ⟨g.base,reduction g.central⟩
  map_one' := by
    apply GroupModel.ext
    · rfl
    · exact map_zero reduction
  map_mul' g h := by
    apply GroupModel.ext
    · rfl
    · change reduction (g.central+h.central+Universal.cocycle g.base h.base) =
        reduction g.central+reduction h.central+cocycle g.base h.base
      rw [map_add,map_add,cocycle_eq]

@[simp] theorem reductionHom_base (g : Universal.Q) : (reductionHom g).base = g.base := rfl
@[simp] theorem reductionHom_central (g : Universal.Q) :
    (reductionHom g).central = reduction g.central := rfl

theorem reductionHom_surjective : Function.Surjective reductionHom := by
  intro q
  obtain ⟨z,hz⟩ := reduction_surjective q.central
  exact ⟨⟨q.base,z⟩,GroupModel.ext rfl hz⟩

end UnitDistance.Sqrt241.Retained
