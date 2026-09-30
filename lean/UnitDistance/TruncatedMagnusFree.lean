module

public import UnitDistance.TruncatedMagnusConjugacyIndex
public import UnitDistance.TruncatedMagnusAugmentation
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.FreeProC.Basic
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.Presentations.Profinite

@[expose] public section
set_option backward.privateInPublic true


/-! The cubic detector is an actual continuous finite quotient of an actual
free pro-two source. Its images of genuine relators and actual augmentation
subgroups provide a factorization through the cut presentation. -/
noncomputable section
namespace UnitDistance.TruncatedMagnus
open ProCGroups ProCGroups.ProC ProCGroups.FreeProC ProCGroups.Presentations

instance : TopologicalSpace (Group (ZMod 2)) := ⊥
instance : DiscreteTopology (Group (ZMod 2)) := ⟨rfl⟩
instance : IsTopologicalGroup (Group (ZMod 2)) := by infer_instance

theorem hasPGroupOpenNormalBasis : HasPGroupOpenNormalBasis 2 (Group (ZMod 2)) := by
  apply HasOpenNormalBasisInClass.of_allOpenNormalQuotients
  intro U
  exact ⟨inferInstance,binaryGroup_isTwoGroup.of_surjective
    (QuotientGroup.mk' (U : Subgroup (Group (ZMod 2))))
    (QuotientGroup.mk'_surjective (U : Subgroup (Group (ZMod 2))))⟩

namespace Certificate
variable {G : Type} [_root_.Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {x : Fin 7 → G}

/-- The full cubic Magnus map follows from the actual free universal property. -/
def freeDetector (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x) :
    G →ₜ* Group F :=
  hfree.liftHom hasPGroupOpenNormalBasis generator continuous_of_discreteTopology

@[simp] theorem freeDetector_generator
    (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x) (i : Fin 7) :
    freeDetector hfree (x i)=generator i :=
  hfree.liftHom_apply hasPGroupOpenNormalBasis generator continuous_of_discreteTopology i

/-- The actual cut quotient, retaining the arbitrary actual cubic relator tails. -/
def freeCut (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x)
    (tails : Fin 16 → V₃ F) : G →ₜ* Cut tails where
  toMonoidHom := (quotientMap tails).comp (freeDetector hfree).toMonoidHom
  continuous_toFun :=
    (continuous_of_discreteTopology : Continuous (quotientMap tails)).comp
      (freeDetector hfree).continuous_toFun

@[simp] theorem freeCut_apply
    (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x)
    (tails : Fin 16 → V₃ F) (g : G) :
    freeCut hfree tails g=quotientMap tails (freeDetector hfree g) := rfl

@[simp] theorem freeCut_generator
    (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x)
    (tails : Fin 16 → V₃ F) (i : Fin 7) :
    freeCut hfree tails (x i)=quotientMap tails (generator i) := by simp

/-- The actual finite image already has at least4096 conjugates of its infinity generator. -/
theorem freeCut_image_conjugacy_index
    (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x)
    (tails : Fin 16 → V₃ F) :
    4096 ≤ (Subgroup.centralizer
      ({(⟨freeCut hfree tails (x 0),⟨x 0,rfl⟩⟩ : (freeCut hfree tails).toMonoidHom.range)} :
        Set (freeCut hfree tails).toMonoidHom.range)).index := by
  let H := (freeCut hfree tails).toMonoidHom.range
  have hgen (i : Fin 7) : quotientMap tails (generator i)∈H :=
    ⟨x i,freeCut_generator hfree tails i⟩
  simpa only [freeCut_generator] using conjugacy_index_lower_subgroup tails H hgen

/-- Actual cubic coefficients are read from the relators, not assigned or discarded. -/
def relatorTails (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x)
    (r : Fin 16 → G) : Fin 16 → V₃ F := fun i => (freeDetector hfree (r i)).third

theorem freeCut_relator_eq_one
    (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x) (r : Fin 16 → G)
    (h1 : ∀ i,(freeDetector hfree (r i)).first=0)
    (h2 : ∀ i,(freeDetector hfree (r i)).second=quadraticRow i) (i : Fin 16) :
    freeCut hfree (relatorTails hfree r) (r i)=1 := by
  rw [freeCut_apply]
  have he : freeDetector hfree (r i)=
      (⟨0,quadraticRow i,relatorTails hfree r i⟩ : Group F) :=
    Group.ext (h1 i) (h2 i) rfl
  rw [he]
  exact (QuotientGroup.eq_one_iff _).mpr (relator_mem_cutSubgroup _ i)

theorem freeCut_dyadic_eq_one
    (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x)
    (tails : Fin 16 → V₃ F) (k : G)
    (hk : freeDetector hfree k=(⟨0,0,dyadicCubic⟩ : Group F)) : freeCut hfree tails k=1 := by
  rw [freeCut_apply,hk]
  exact (QuotientGroup.eq_one_iff _).mpr (dyadic_mem_cutSubgroup tails)

/-- Every actual degree-four element is killed by the finite Magnus map. -/
theorem freeDetector_eq_one_of_dimension_four
    (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x) (g : G)
    (hg : g∈GroupAugmentation.dimensionSubgroup F G 4) : freeDetector hfree g=1 := by
  have h := GroupAugmentation.map_dimensionSubgroup_le F G
    (freeDetector hfree).toMonoidHom 4 ⟨g,hg,rfl⟩
  rw [dimensionSubgroup_four,Subgroup.mem_bot] at h
  exact h

/-- The entire actual closed normal cut kernel is annihilated by this continuous finite map. -/
theorem closedNormalClosure_le_freeCut_ker
    (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x) (r : Fin 16 → G)
    (h1 : ∀ i,(freeDetector hfree (r i)).first=0)
    (h2 : ∀ i,(freeDetector hfree (r i)).second=quadraticRow i)
    (k : G) (hk : freeDetector hfree k=(⟨0,0,dyadicCubic⟩ : Group F))
    (deep : Set G) (hdeep : ∀ g∈deep,g∈GroupAugmentation.dimensionSubgroup F G 4) :
    closedNormalClosure (Set.range r ∪ {k} ∪ deep) ≤
      (freeCut hfree (relatorTails hfree r)).toMonoidHom.ker := by
  apply closedNormalClosure_le_closed_normal
    (ProCGroups.ContinuousMonoidHom.isClosed_ker (freeCut hfree (relatorTails hfree r)))
  intro g hg
  rcases hg with (⟨i,rfl⟩ | rfl) | hg
  · exact freeCut_relator_eq_one hfree r h1 h2 i
  · exact freeCut_dyadic_eq_one hfree _ _ hk
  · change freeCut hfree (relatorTails hfree r) g=1
    rw [freeCut_apply,freeDetector_eq_one_of_dimension_four hfree g (hdeep g hg),map_one]

end Certificate
end UnitDistance.TruncatedMagnus
