module

public import UnitDistance.Sqrt241.Generators.GenusInOmega
public import UnitDistance.Sqrt241.Genus.Degree
public import UnitDistance.QuadraticSignLift

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# The genus label `G_B → F₂⁸`

An element `g ∈ G_B` fixes `√241`, hence multiplies each genus root
`√α_k ∈ Ω` by a sign. `genusLabel g ∈ F₂⁸` records these signs
(`1 ↔ -1`, `Multiquadratic.binarySign`). It is a continuous surjective
homomorphism whose kernel is `G_B ∩ Gal(Ω/E)` (`E` the canonical genus field);
surjectivity is a counting argument: `[Ĝ : Gal(Ω/E)] = [E : ℚ] = 512` and
`[Ĝ : G_B] = 2`.
-/

open scoped NumberField
open NumberField

noncomputable section

namespace UnitDistance.Sqrt241.Tower

open Base CanonicalGenus IntermediateField Multiquadratic

/-! ### Genus roots in `Ω` -/

/-- `√α_k` as an element of `Ω`. -/
def genusRootOmega (k : Fin 8) : Omega := ⟨genusRoot k, genusRoot_mem_Omega k⟩

@[simp] theorem coe_genusRootOmega (k : Fin 8) : (genusRootOmega k : Closure) = genusRoot k :=
  rfl

/-- The radicand `α_k` as an element of `Ω`. -/
def radicandOmega (k : Fin 8) : Omega := ⟨radicand k, B_le_Omega (radicand_mem_B k)⟩

theorem genusRootOmega_sq (k : Fin 8) : genusRootOmega k ^ 2 = radicandOmega k :=
  Subtype.ext (genusRoot_sq k)

theorem radicandOmega_mem_BinOmega (k : Fin 8) : radicandOmega k ∈ BinOmega :=
  (mem_BinOmega_iff _).2 (radicand_mem_B k)

theorem genusRootOmega_ne_zero (k : Fin 8) : genusRootOmega k ≠ 0 := by
  intro h
  have h2 := genusRootOmega_sq k
  rw [h, zero_pow two_ne_zero] at h2
  have h3 : radicand k = 0 := congrArg (fun y : Omega ↦ (y : Closure)) h2.symm
  exact Genus.radicand_ne_zero k h3

theorem apply_genusRootOmega (g : GB) (k : Fin 8) :
    (g : Ghat) (genusRootOmega k) = genusRootOmega k ∨
      (g : Ghat) (genusRootOmega k) = -genusRootOmega k := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  rw [← map_pow, genusRootOmega_sq, fixes_BinOmega g _ (radicandOmega_mem_BinOmega k)]

/-! ### The label -/

open Classical in
/-- The genus character of `g ∈ G_B` at `k`: `0` if `g` fixes `√α_k`, `1` if it
negates it. -/
def genusChar (g : GB) (k : Fin 8) : ZMod 2 :=
  if (g : Ghat) (genusRootOmega k) = genusRootOmega k then 0 else 1

theorem genusChar_action (g : GB) (k : Fin 8) :
    (g : Ghat) (genusRootOmega k) = binarySign (genusChar g k) * genusRootOmega k := by
  classical
  unfold genusChar
  split_ifs with h
  · rw [binarySign_zero, one_mul, h]
  · rw [(apply_genusRootOmega g k).resolve_left h]
    simp [binarySign, binarySignInteger]

theorem genusChar_eq_zero_iff (g : GB) (k : Fin 8) :
    genusChar g k = 0 ↔ (g : Ghat) (genusRootOmega k) = genusRootOmega k := by
  classical
  unfold genusChar
  split_ifs with h
  · exact ⟨fun _ ↦ h, fun _ ↦ rfl⟩
  · exact ⟨fun h' ↦ absurd h' (by decide), fun h' ↦ absurd h' h⟩

/-- The genus label as a group homomorphism. -/
def genusLabelHom : GB →* Multiplicative (Fin 8 → ZMod 2) where
  toFun g := Multiplicative.ofAdd (genusChar g)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext k
    change genusChar 1 k = 0
    rw [genusChar_eq_zero_iff]
    rfl
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    funext k
    apply binarySign_injective (E := Omega)
    apply mul_right_cancel₀ (genusRootOmega_ne_zero k)
    change binarySign (genusChar (g * h) k) * genusRootOmega k =
      binarySign (genusChar g k + genusChar h k) * genusRootOmega k
    rw [← genusChar_action, binarySign_add, Subgroup.coe_mul, AlgEquiv.mul_apply,
      genusChar_action h, map_mul, genusChar_action g]
    have hs : ∀ ε : ZMod 2, (g : Ghat) (binarySign ε) = binarySign ε := by
      intro ε
      simp [binarySign]
    rw [hs]
    ring

theorem genusLabelHom_apply (g : GB) (k : Fin 8) :
    (genusLabelHom g).toAdd k = genusChar g k :=
  rfl

/-- The canonical genus field as a subfield of `Ω`. -/
def EOmega : IntermediateField ℚ Omega :=
  IntermediateField.adjoin ℚ (insert rootOmega (Set.range genusRootOmega))

theorem rootOmega_mem_EOmega : rootOmega ∈ EOmega :=
  IntermediateField.subset_adjoin ℚ _ (Set.mem_insert _ _)

theorem genusRootOmega_mem_EOmega (k : Fin 8) : genusRootOmega k ∈ EOmega :=
  IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem _ ⟨k, rfl⟩)

theorem lift_EOmega : IntermediateField.lift EOmega = CanonicalGenus.field := by
  rw [EOmega, IntermediateField.lift_adjoin, Set.image_insert_eq, ← Set.range_comp]
  rfl

theorem finrank_EOmega : Module.finrank ℚ EOmega = 512 := by
  rw [(IntermediateField.liftAlgEquiv EOmega).toLinearEquiv.finrank_eq, lift_EOmega]
  exact Genus.finrank_carrier

instance EOmega_finiteDimensional : FiniteDimensional ℚ EOmega :=
  Module.finite_of_finrank_pos (by rw [finrank_EOmega]; norm_num)

theorem BinOmega_le_EOmega : BinOmega ≤ EOmega := by
  intro x hx
  obtain ⟨a, b, rfl⟩ := exists_coords_BinOmega x hx
  exact add_mem (IntermediateField.algebraMap_mem _ a)
    (mul_mem (IntermediateField.algebraMap_mem _ b) rootOmega_mem_EOmega)

theorem EOmega_fixingSubgroup_le_GB : EOmega.fixingSubgroup ≤ GB :=
  IntermediateField.fixingSubgroup_antitone BinOmega_le_EOmega

/-- An automorphism fixing every element of a generating set fixes the
generated intermediate field. -/
theorem mem_fixingSubgroup_adjoin {K L : Type*} [Field K] [Field L] [Algebra K L]
    (σ : L ≃ₐ[K] L) {s : Set L} (h : ∀ a ∈ s, σ a = a) :
    σ ∈ (IntermediateField.adjoin K s).fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have key : (σ : L →ₐ[K] L).comp (IntermediateField.adjoin K s).val =
      (IntermediateField.adjoin K s).val := by
    apply IntermediateField.adjoin_algHom_ext
    intro y hy
    exact h y hy
  exact congrArg (fun φ : IntermediateField.adjoin K s →ₐ[K] L ↦ φ ⟨x, hx⟩) key

theorem mem_ker_genusLabelHom_iff (g : GB) :
    g ∈ genusLabelHom.ker ↔ (g : Ghat) ∈ EOmega.fixingSubgroup := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hg
    apply mem_fixingSubgroup_adjoin
    rintro a (rfl | ⟨k, rfl⟩)
    · exact (mem_GB_iff _).1 g.2
    · have hk := congrArg (fun v : Multiplicative (Fin 8 → ZMod 2) ↦ v.toAdd k) hg
      exact (genusChar_eq_zero_iff g k).1 hk
  · intro hg
    apply Multiplicative.toAdd.injective
    funext k
    exact (genusChar_eq_zero_iff g k).2
      ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hg _ (genusRootOmega_mem_EOmega k))

theorem ker_genusLabelHom : genusLabelHom.ker = EOmega.fixingSubgroup.subgroupOf GB := by
  ext g
  rw [mem_ker_genusLabelHom_iff, Subgroup.mem_subgroupOf]

theorem genusLabelHom_surjective : Function.Surjective genusLabelHom := by
  have hE : EOmega.fixingSubgroup.index = 512 := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index, finrank_EOmega]
  have hrel : (EOmega.fixingSubgroup.subgroupOf GB).index = 256 := by
    have h := Subgroup.relIndex_mul_index EOmega_fixingSubgroup_le_GB
    rw [hE, GB_index] at h
    change (EOmega.fixingSubgroup.subgroupOf GB).index * 2 = 512 at h
    omega
  have hcard : Nat.card genusLabelHom.range = 256 := by
    rw [← Subgroup.index_ker, ker_genusLabelHom, hrel]
  have htop : genusLabelHom.range = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hcard, Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 8 → ZMod 2) ≃ _)]
    simp
  exact MonoidHom.range_eq_top.mp htop

/-- A homomorphism into a discrete group whose kernel contains an open
subgroup is continuous. -/
theorem continuous_of_le_ker {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [DiscreteTopology H] (f : G →* H) (U : Subgroup G)
    (hU : IsOpen (U : Set G)) (hUf : U ≤ f.ker) : Continuous f := by
  refine continuous_of_continuousAt_one f ?_
  rw [ContinuousAt, map_one, Filter.Tendsto]
  intro s hs
  rw [Filter.mem_map]
  have h1 : (1 : H) ∈ s := mem_of_mem_nhds hs
  apply Filter.mem_of_superset (hU.mem_nhds U.one_mem)
  intro g hg
  change f g ∈ s
  rw [hUf hg]
  exact h1

theorem EOmega_fixingSubgroup_subgroupOf_isOpen :
    IsOpen ((EOmega.fixingSubgroup.subgroupOf GB : Subgroup GB) : Set GB) :=
  (IntermediateField.fixingSubgroup_isOpen EOmega).preimage continuous_subtype_val

/-- The genus label `G_B →ₜ* F₂⁸`: `genusLabel g` records the signs by which
`g` acts on the genus roots `√α_k`. -/
def genusLabel : GB →ₜ* Multiplicative (Fin 8 → ZMod 2) where
  toMonoidHom := genusLabelHom
  continuous_toFun := continuous_of_le_ker genusLabelHom _
    EOmega_fixingSubgroup_subgroupOf_isOpen ker_genusLabelHom.ge

theorem genusLabel_apply (g : GB) (k : Fin 8) : (genusLabel g).toAdd k = genusChar g k :=
  rfl

theorem genusLabel_surjective : Function.Surjective genusLabel :=
  genusLabelHom_surjective

theorem genusLabel_ker_eq_fixing :
    genusLabel.toMonoidHom.ker = EOmega.fixingSubgroup.subgroupOf GB :=
  ker_genusLabelHom

/-- `g ∈ G_B` acts on `√α_k` through its label. -/
theorem genusLabel_action (g : GB) (k : Fin 8) :
    ((g : Ghat) (genusRootOmega k) : Closure) =
      binarySign ((genusLabel g).toAdd k) * genusRoot k := by
  rw [genusLabel_apply, genusChar_action]
  simp [binarySign]

/-- Recognizing a label from the action on the genus roots (in the closure). -/
theorem genusLabel_eq_of_action (g : GB) (v : Fin 8 → ZMod 2)
    (h : ∀ k, ((g : Ghat) (genusRootOmega k) : Closure) = binarySign (v k) * genusRoot k) :
    genusLabel g = Multiplicative.ofAdd v := by
  apply Multiplicative.toAdd.injective
  funext k
  apply binarySign_injective (E := Closure)
  apply mul_right_cancel₀ (Genus.genusRoot_ne_zero k)
  rw [← genusLabel_action, h k]
  rfl

end UnitDistance.Sqrt241.Tower
