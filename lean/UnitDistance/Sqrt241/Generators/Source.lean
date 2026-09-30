module

public import UnitDistance.Sqrt241.Generators.Frattini
public import UnitDistance.FiniteFreeProTwo
public import UnitDistance.ClassTwoCollection

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Generators of `G_B` and the free pro-2 source

`gen i ∈ G_B` (`i : Fin 8`) are fixed lifts of the basis vectors of `F₂⁸`
through the genus label; since `ker genusLabel` is the Frattini subgroup they
topologically generate `G_B`, and since the rank is `8` the induced map from
the free pro-2 group on eight generators is a minimal surjection
(`freeMap`, kernel inside the Frattini subgroup of the source). Its kernel is
`relationKernel`, and `freeQuotientEquiv` identifies the quotient with `G_B`.
Templates: `SigmaGenusGenerators`, `SigmaFreeSource` (ℚ package).
-/

noncomputable section

namespace UnitDistance.Sqrt241.Tower

open ClassFieldTower.ProP ProCGroups
open ProCGroups.Generation ProCGroups.FiniteGeneration

/-- The basis vectors of `F₂⁸`, written multiplicatively. -/
def labelBasis (i : Fin 8) : Multiplicative (Fin 8 → ZMod 2) :=
  Multiplicative.ofAdd (Pi.single i 1)

theorem labelBasis_generates : TopologicallyGenerates (Set.range labelBasis) := by
  classical
  have htop : Subgroup.closure (Set.range labelBasis) = ⊤ := by
    apply top_unique
    intro v _
    have hv : v = ∏ i : Fin 8, Multiplicative.ofAdd (Pi.single i (v.toAdd i)) := by
      rw [← ofAdd_sum, Finset.univ_sum_single]
      rfl
    rw [hv]
    apply Subgroup.prod_mem
    intro i _
    rcases ClassTwo.Collection.binary_cases (v.toAdd i) with hi | hi
    · rw [hi, Pi.single_zero]
      exact Subgroup.one_mem _
    · rw [hi]
      exact Subgroup.subset_closure ⟨i, rfl⟩
  simp [TopologicallyGenerates, htop]

/-- Any lifts of the eight label basis vectors topologically generate `G_B`. -/
theorem generators_of_labelBasis (x : Fin 8 → GB) (hx : ∀ i, genusLabel (x i) = labelBasis i) :
    TopologicallyGenerates (Set.range x) := by
  let : (closedPowerCommutator 2 GB).Normal := closedPowerCommutator_normal 2 _
  let e : powerCommutatorQuotient 2 GB ≃* Multiplicative (Fin 8 → ZMod 2) :=
    QuotientGroup.liftEquiv _ genusLabel_surjective genusLabel_ker.symm
  have heval (g : GB) : e (powerCommutatorQuotientMk 2 GB g) = genusLabel g := rfl
  have hgen := topologicallyGenerates_image_of_continuousSurjective
    e.symm.toMonoidHom continuous_of_discreteTopology e.symm.surjective labelBasis_generates
  change TopologicallyGenerates (e.symm '' Set.range labelBasis) at hgen
  apply (topologicallyGenerates_iff_powerCommutatorQuotient_image
    GB_hasPGroupOpenNormalBasis).mpr
  have himage : e.symm '' Set.range labelBasis =
      powerCommutatorQuotientMk 2 GB '' Set.range x := by
    ext a
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      refine ⟨x i, ⟨i, rfl⟩, ?_⟩
      apply e.injective
      simpa only [e.apply_symm_apply, heval] using hx i
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      refine ⟨labelBasis i, ⟨i, rfl⟩, ?_⟩
      apply e.injective
      simpa only [e.apply_symm_apply, heval] using (hx i).symm
  rwa [himage] at hgen

/-- The fixed generators of `G_B`: `genusLabel (gen i) = e_i`. -/
def gen (i : Fin 8) : GB := Function.surjInv genusLabel_surjective (labelBasis i)

theorem gen_label (i : Fin 8) : genusLabel (gen i) = Multiplicative.ofAdd (Pi.single i 1) :=
  Function.surjInv_eq genusLabel_surjective (labelBasis i)

theorem gen_generates : TopologicallyGenerates (Set.range gen) :=
  generators_of_labelBasis gen gen_label

theorem exists_freeMap :
    ∃ π : FiniteFreeProTwo.Carrier 8 →ₜ* GB,
      Function.Surjective π ∧
      π.toMonoidHom.ker ≤ closedPowerCommutator 2 (FiniteFreeProTwo.Carrier 8) ∧
      ∀ i, π (FiniteFreeProTwo.generator 8 i) = gen i :=
  FiniteFreeProTwo.exists_minimal_surjection_for_generators
    GB_hasPGroupOpenNormalBasis 8 gen gen_generates GB_generatorRank.2

/-- The minimal free presentation map `F(8) → G_B`, `generator i ↦ gen i`. -/
def freeMap : FiniteFreeProTwo.Carrier 8 →ₜ* GB :=
  Classical.choose exists_freeMap

theorem freeMap_surjective : Function.Surjective freeMap :=
  (Classical.choose_spec exists_freeMap).1

theorem freeMap_minimal :
    freeMap.toMonoidHom.ker ≤ closedPowerCommutator 2 (FiniteFreeProTwo.Carrier 8) :=
  (Classical.choose_spec exists_freeMap).2.1

theorem freeMap_generator (i : Fin 8) : freeMap (FiniteFreeProTwo.generator 8 i) = gen i :=
  (Classical.choose_spec exists_freeMap).2.2 i

theorem freeMap_generator_label (i : Fin 8) :
    genusLabel (freeMap (FiniteFreeProTwo.generator 8 i)) =
      Multiplicative.ofAdd (Pi.single i 1) := by
  rw [freeMap_generator, gen_label]

/-- The relation kernel of the presentation `F(8) → G_B`. -/
def relationKernel : ClosedSubgroup (FiniteFreeProTwo.Carrier 8) where
  toSubgroup := freeMap.toMonoidHom.ker
  isClosed' := ProCGroups.ContinuousMonoidHom.isClosed_ker freeMap

instance relationKernel_normal : relationKernel.Normal :=
  inferInstanceAs freeMap.toMonoidHom.ker.Normal

theorem mem_relationKernel_iff (g : FiniteFreeProTwo.Carrier 8) :
    g ∈ (relationKernel : Subgroup (FiniteFreeProTwo.Carrier 8)) ↔ freeMap g = 1 :=
  Iff.rfl

theorem relationKernel_le_frattini :
    (relationKernel : Subgroup (FiniteFreeProTwo.Carrier 8)) ≤
      closedPowerCommutator 2 (FiniteFreeProTwo.Carrier 8) :=
  freeMap_minimal

set_option maxHeartbeats 800000 in
/-- `F(8)/R ≃ₜ* G_B`. -/
def freeQuotientEquiv :
    (FiniteFreeProTwo.Carrier 8 ⧸ (relationKernel : Subgroup (FiniteFreeProTwo.Carrier 8))) ≃ₜ* GB := by
  let e := QuotientGroup.quotientKerEquivOfSurjective freeMap.toMonoidHom freeMap_surjective
  apply ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2 e.toMonoidHom _ e.bijective
  apply (QuotientGroup.isQuotientMap_mk freeMap.toMonoidHom.ker).continuous_iff.mpr
  exact freeMap.continuous_toFun

theorem freeQuotientEquiv_mk (g : FiniteFreeProTwo.Carrier 8) :
    freeQuotientEquiv (QuotientGroup.mk' (relationKernel : Subgroup (FiniteFreeProTwo.Carrier 8)) g) = freeMap g :=
  rfl

end UnitDistance.Sqrt241.Tower
