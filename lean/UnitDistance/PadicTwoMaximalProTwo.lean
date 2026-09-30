module

public import UnitDistance.PadicTwoQuadraticClosure
public import UnitDistance.PadicTwoGenusField
public import UnitDistance.ProTwoElementaryQuotient
public import UnitDistance.FiniteFreeProTwo
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.ProC.MaximalQuotients.ResidualQuotient
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.ProC.MaximalQuotients.UniversalProperty
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.Galois.Profinite

@[expose] public section
set_option backward.privateInPublic true


/-! The actual maximal pro-two quotient of the absolute Galois group of Q₂.
Its genus quotient exhausts all quadratic quotients and proves exact rank three. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.PadicTwoMaximalProTwo
open ProCGroups ProCGroups.ProC ClassFieldTower.ProP
open ProCGroups.Generation ProCGroups.FiniteGeneration
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev Closure := AlgebraicClosure ℚ_[2]
abbrev AbsoluteGroup := Gal(Closure/ℚ_[2])
def core : Subgroup AbsoluteGroup := proCResidualCore (FiniteGroupClass.pGroup 2) AbsoluteGroup
instance core_normal : core.Normal := proCResidualCore_normal _ _
instance core_closed : IsClosed (core : Set AbsoluteGroup) := proCResidualCore_isClosed _ _
abbrev Group := AbsoluteGroup ⧸ core
instance group_totallyDisconnected : TotallyDisconnectedSpace Group :=
  totallyDisconnectedSpace_quotient_closedNormal core core_closed

def projection : AbsoluteGroup →ₜ* Group :=
  ⟨QuotientGroup.mk' core, QuotientGroup.continuous_mk⟩

theorem projection_surjective : Function.Surjective projection := QuotientGroup.mk'_surjective core

theorem proTwo : HasPGroupOpenNormalBasis 2 Group :=
  proCResidualCoreQuotient_hasOpenNormalBasisInClass (FiniteGroupClass.pGroup_formation 2)

abbrev VectorGroup := Multiplicative (Fin 3 → ZMod 2)
instance vectorTopology : TopologicalSpace VectorGroup := ⊥
instance vectorDiscrete : DiscreteTopology VectorGroup := ⟨rfl⟩
instance vectorTopologicalGroup : IsTopologicalGroup VectorGroup := inferInstance
instance vectorT2 : T2Space VectorGroup := inferInstance

theorem vector_card : Nat.card VectorGroup = 2^3 := by
  rw [Nat.card_congr (Multiplicative.toAdd : VectorGroup ≃ (Fin 3 → ZMod 2))]
  simp

theorem vector_proTwo : HasPGroupOpenNormalBasis 2 VectorGroup := by
  apply HasOpenNormalBasisInClass.of_finite_discrete (FiniteGroupClass.pGroup_formation 2).quotientClosed
  exact ⟨inferInstance,IsPGroup.of_card vector_card⟩

def genusEmbedding : PadicTwoGenus.GenusField →ₐ[ℚ_[2]] Closure := IsAlgClosed.lift

def genusImage : IntermediateField ℚ_[2] Closure := genusEmbedding.fieldRange

def genusEquiv : PadicTwoGenus.GenusField ≃ₐ[ℚ_[2]] genusImage := genusEmbedding.equivFieldRange
instance genus_finite : Module.Finite ℚ_[2] genusImage := genusEquiv.toLinearEquiv.finiteDimensional
instance genus_galois : IsGalois ℚ_[2] genusImage := IsGalois.of_algEquiv genusEquiv

/-- Actual Galois restriction, recorded as the three signs of −1, 2 and 5. -/
def absoluteSigns : AbsoluteGroup →ₜ* VectorGroup where
  toMonoidHom := PadicTwoGenus.signEquiv.toMonoidHom.comp
    ((AlgEquiv.autCongr genusEquiv.symm).toMonoidHom.comp
      (AlgEquiv.restrictNormalHom (F := ℚ_[2]) (K₁ := Closure) genusImage))
  continuous_toFun :=
    (continuous_of_discreteTopology : Continuous
      (fun σ : Gal(genusImage/ℚ_[2]) ↦ PadicTwoGenus.signEquiv (AlgEquiv.autCongr genusEquiv.symm σ))).comp
      (InfiniteGalois.restrictNormalHom_continuous genusImage)

theorem absoluteSigns_surjective : Function.Surjective absoluteSigns :=
  PadicTwoGenus.signEquiv.surjective.comp ((AlgEquiv.autCongr genusEquiv.symm).surjective.comp
    (AlgEquiv.restrictNormalHom_surjective Closure))

theorem absoluteSigns_ker : absoluteSigns.toMonoidHom.ker = genusImage.fixingSubgroup := by
  have hk : absoluteSigns.toMonoidHom.ker =
      (AlgEquiv.restrictNormalHom (F := ℚ_[2]) (K₁ := Closure) genusImage).ker := by
    ext σ
    change PadicTwoGenus.signEquiv (AlgEquiv.autCongr genusEquiv.symm
      (AlgEquiv.restrictNormalHom (F := ℚ_[2]) (K₁ := Closure) genusImage σ))=1 ↔ _
    rw [map_eq_one_iff _ PadicTwoGenus.signEquiv.injective,
      map_eq_one_iff _ (AlgEquiv.autCongr genusEquiv.symm).injective]
    rfl
  exact hk.trans genusImage.restrictNormalHom_ker

/-- The genus restriction factors through the actual maximal pro-two quotient. -/
def signs : Group →ₜ* VectorGroup :=
  lift_proCResidualCoreQuotient (FiniteGroupClass.pGroup_hereditary 2) absoluteSigns vector_proTwo

@[simp] theorem signs_projection (σ : AbsoluteGroup) : signs (projection σ)=absoluteSigns σ := rfl

theorem signs_surjective : Function.Surjective signs := by
  intro x
  obtain ⟨σ,hσ⟩ := absoluteSigns_surjective x
  exact ⟨projection σ,hσ⟩

theorem vector_pow_two (a : VectorGroup) : a^2=1 := by
  apply Multiplicative.toAdd.injective
  change (2 : ℕ) • a.toAdd=0
  funext i
  simp [show (2 : ZMod 2)=0 by decide]

/-- Every quadratic subfield of the algebraic closure lies in the actual genus image. -/
theorem quadratic_le_genusImage (L : IntermediateField ℚ_[2] Closure)
    (hL : Module.finrank ℚ_[2] L=2) : L≤genusImage := by
  let a := genusEquiv (PadicTwoGenus.roots 0)
  let b := genusEquiv (PadicTwoGenus.roots 1)
  let c := genusEquiv (PadicTwoGenus.roots 2)
  have h0 : (PadicTwoGenus.roots 0)^2=(-1 : PadicTwoGenus.GenusField) := by
    simpa [PadicTwo.independentRadicand] using PadicTwoGenus.roots_sq_int 0
  have h1 : (PadicTwoGenus.roots 1)^2=(2 : PadicTwoGenus.GenusField) := by
    simpa [PadicTwo.independentRadicand] using PadicTwoGenus.roots_sq_int 1
  have h2 : (PadicTwoGenus.roots 2)^2=(5 : PadicTwoGenus.GenusField) := by
    simpa [PadicTwo.independentRadicand] using PadicTwoGenus.roots_sq_int 2
  apply PadicTwo.quadratic_le Closure genusImage L a b c _ _ _ hL
  · dsimp [a]
    rw [←map_pow,h0]
    rw [map_neg,map_one]
  · dsimp [b]
    rw [←map_pow,h1]
    exact map_natCast genusEquiv 2
  · dsimp [c]
    rw [←map_pow,h2]
    exact map_natCast genusEquiv 5

/-- Pullback of each index-two quotient gives an actual quadratic fixed field,
so its kernel contains the kernel of the genus signs. -/
theorem signs_ker_le_index_two (U : OpenNormalSubgroup Group)
    (hU : (U : Subgroup Group).index=2) : signs.toMonoidHom.ker ≤ (U : Subgroup Group) := by
  let V := OpenNormalSubgroup.comap projection.toMonoidHom projection.continuous U
  let L := IntermediateField.fixedField (V : Subgroup AbsoluteGroup)
  have hfix : L.fixingSubgroup = (V : Subgroup AbsoluteGroup) :=
    InfiniteGalois.fixingSubgroup_fixedField (⟨(V : Subgroup AbsoluteGroup),V.isClosed⟩ : ClosedSubgroup AbsoluteGroup)
  have hL : Module.finrank ℚ_[2] L=2 := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index,hfix]
    exact ((U : Subgroup Group).index_comap_of_surjective projection_surjective).trans hU
  have hle : genusImage.fixingSubgroup ≤ (V : Subgroup AbsoluteGroup) := by
    rw [←hfix]
    exact IntermediateField.fixingSubgroup_le (quadratic_le_genusImage L hL)
  intro x hx
  obtain ⟨σ,rfl⟩ := projection_surjective x
  apply hle
  rw [←absoluteSigns_ker]
  exact hx

theorem generatorRank_three : TopologicallyGeneratedByAtMost 3 Group ∧
    topologicalGeneratorRank Group=3 :=
  ProTwoElementaryQuotient.generatorRank_of_quadratic_quotient proTwo signs signs_surjective
    vector_pow_two signs_ker_le_index_two 3 vector_card

/-- An actual minimal surjection from the constructed free pro-two group of rank three. -/
theorem exists_minimal_free_surjection :
    ∃ π : FiniteFreeProTwo.Carrier 3 →ₜ* Group,
      Function.Surjective π ∧ π.toMonoidHom.ker ≤
        closedPowerCommutator 2 (FiniteFreeProTwo.Carrier 3) := by
  have hfg : TopologicallyFinitelyGenerated Group := by
    obtain ⟨s,hs,hgen⟩ := generatorRank_three.1
    exact ⟨s,hgen⟩
  obtain ⟨x,hx⟩ := exists_generatingTuple_of_topologicalRank_le_of_finite hfg
    (topologicalRank_le_of_topologicallyGeneratedByAtMost generatorRank_three.1)
  obtain ⟨π,hπ,hker,_⟩ := FiniteFreeProTwo.exists_minimal_surjection_for_generators
    proTwo 3 x hx generatorRank_three.2
  exact ⟨π,hπ,hker⟩

/-- The actual three genus signs are the full Frattini quotient. -/
theorem signs_ker : signs.toMonoidHom.ker = closedPowerCommutator 2 Group :=
  (ProTwoElementaryQuotient.closedPowerCommutator_eq_ker proTwo signs
    vector_pow_two signs_ker_le_index_two).symm

def genusBasis (i : Fin 3) : VectorGroup := Multiplicative.ofAdd (Pi.single i 1)

theorem genusBasis_generates : TopologicallyGenerates (Set.range genusBasis) := by
  classical
  have htop : Subgroup.closure (Set.range genusBasis)=⊤ := by
    apply top_unique
    intro v _
    have hv : v=∏i : Fin 3,Multiplicative.ofAdd (Pi.single i (v.toAdd i)) := by
      rw [←ofAdd_sum,Finset.univ_sum_single]
      rfl
    rw [hv]
    apply Subgroup.prod_mem
    intro i _
    have binary : ∀a : ZMod 2,a=0 ∨ a=1 := by decide
    rcases binary (v.toAdd i) with hi | hi
    · rw [hi,Pi.single_zero]
      exact Subgroup.one_mem _
    · rw [hi]
      exact Subgroup.subset_closure ⟨i,rfl⟩
  simp [TopologicallyGenerates,htop]

/-- Every triple lifting the three independent signs generates the actual local group. -/
theorem generates_of_genusBasis (x : Fin 3 → Group)
    (hx : ∀i,signs (x i)=genusBasis i) : TopologicallyGenerates (Set.range x) := by
  letI : (closedPowerCommutator 2 Group).Normal := closedPowerCommutator_normal 2 _
  let e : powerCommutatorQuotient 2 Group ≃* VectorGroup :=
    QuotientGroup.liftEquiv _ signs_surjective signs_ker.symm
  have heval (g : Group) : e (powerCommutatorQuotientMk 2 Group g)=signs g := rfl
  have hgen := topologicallyGenerates_image_of_continuousSurjective
    e.symm.toMonoidHom continuous_of_discreteTopology e.symm.surjective genusBasis_generates
  change TopologicallyGenerates (e.symm '' Set.range genusBasis) at hgen
  apply (topologicallyGenerates_iff_powerCommutatorQuotient_image proTwo).mpr
  have himage : e.symm '' Set.range genusBasis=powerCommutatorQuotientMk 2 Group '' Set.range x := by
    ext a
    constructor
    · rintro ⟨_,⟨i,rfl⟩,rfl⟩
      refine ⟨x i,⟨i,rfl⟩,?_⟩
      apply e.injective
      simpa only [e.apply_symm_apply,heval] using hx i
    · rintro ⟨_,⟨i,rfl⟩,rfl⟩
      refine ⟨genusBasis i,⟨i,rfl⟩,?_⟩
      apply e.injective
      simpa only [e.apply_symm_apply,heval] using (hx i).symm
  rwa [himage] at hgen

def generator (i : Fin 3) : Group := Function.surjInv signs_surjective (genusBasis i)

@[simp] theorem generator_signs (i : Fin 3) : signs (generator i)=genusBasis i :=
  Function.surjInv_eq signs_surjective (genusBasis i)

theorem generator_generates : TopologicallyGenerates (Set.range generator) :=
  generates_of_genusBasis generator generator_signs

/-- The minimal free source can be chosen with each generator's three signs fixed. -/
theorem exists_minimal_free_surjection_with_signs :
    ∃π : FiniteFreeProTwo.Carrier 3 →ₜ* Group,
      Function.Surjective π ∧ π.toMonoidHom.ker ≤
        closedPowerCommutator 2 (FiniteFreeProTwo.Carrier 3) ∧
      ∀i,signs (π (FiniteFreeProTwo.generator 3 i))=genusBasis i := by
  obtain ⟨π,hπ,hker,hgen⟩ := FiniteFreeProTwo.exists_minimal_surjection_for_generators
    proTwo 3 generator generator_generates generatorRank_three.2
  exact ⟨π,hπ,hker,fun i ↦ (congrArg signs (hgen i)).trans (generator_signs i)⟩

end UnitDistance.PadicTwoMaximalProTwo
