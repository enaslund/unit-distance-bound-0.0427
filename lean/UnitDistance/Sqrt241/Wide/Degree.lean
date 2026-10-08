module

public import UnitDistance.Sqrt241.Wide.Character

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# `[E_W : ℚ] = 8192`

`E_W` (as `EWOmega ≤ Ω`) contains the genus field `E`, of degree `512`. On the subgroup
`Gal(Ω/E)` of `G_B` the four D4 characters restrict to the signs on `√β_i`, a homomorphism
`ψ : Gal(Ω/E) → F₂⁴` whose kernel is `Gal(Ω/E_W)`. It is surjective: the square of the generator
`gen 0` and the commutators `[gen 0, gen 1]`, `[gen 0, gen 4]`, `[gen 1, gen 3]` have independent
images, read off from the D4 law (`GroupModel.square_coordinates`, `commutator_coordinates`).
Hence `[Gal(Ω/E) : Gal(Ω/E_W)] = 16` and `[E_W : ℚ] = 512 · 16`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Wide

open Tower Base CanonicalGenus CanonicalWide IntermediateField ClassTwo GroupData Multiquadratic

/-- `E_W` as a subfield of `Ω`. -/
def EWOmega : IntermediateField ℚ Omega :=
  IntermediateField.adjoin ℚ (insert rootOmega (Set.range genusRootOmega ∪ Set.range wOm))

theorem lift_EWOmega : IntermediateField.lift EWOmega = CanonicalWide.field := by
  rw [EWOmega, IntermediateField.lift_adjoin, Set.image_insert_eq, Set.image_union,
    ← Set.range_comp, ← Set.range_comp]
  rfl

instance EWOmega_finiteDimensional : FiniteDimensional ℚ EWOmega := by
  apply IntermediateField.finiteDimensional_adjoin
  intro x _
  exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).isIntegral

theorem EOmega_le_EWOmega : EOmega ≤ EWOmega := by
  rw [EOmega, IntermediateField.adjoin_le_iff]
  rintro x (rfl | ⟨k, rfl⟩)
  · exact IntermediateField.subset_adjoin ℚ _ (Set.mem_insert _ _)
  · exact IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem _ (Or.inl ⟨k, rfl⟩))

/-- `Gal(Ω/E)` and `Gal(Ω/E_W)`. -/
abbrev Efix : Subgroup Ghat := EOmega.fixingSubgroup
abbrev EWfix : Subgroup Ghat := EWOmega.fixingSubgroup

theorem EWfix_le_Efix : EWfix ≤ Efix := IntermediateField.fixingSubgroup_antitone EOmega_le_EWOmega

theorem index_Efix : Efix.index = 512 := by
  rw [← IntermediateField.finrank_eq_fixingSubgroup_index, finrank_EOmega]

/-- Elements of `Gal(Ω/E)` as elements of `G_B`. -/
def toGB : Efix →* GB := Subgroup.inclusion EOmega_fixingSubgroup_le_GB

theorem label_toGB (h : Efix) : genusLabel (toGB h) = 1 :=
  (mem_ker_genusLabelHom_iff (toGB h)).mpr h.2

theorem aBit_toGB (i : Fin 4) (h : Efix) : aBit i (toGB h) = 0 := by
  simp [aBit, label_toGB]

theorem bBit_toGB (i : Fin 4) (h : Efix) : bBit i (toGB h) = 0 := by
  simp [bBit, label_toGB]

/-- The four signs on `√β_i` of an element fixing `E`. -/
def psiHom : Efix →* Multiplicative (Fin 4 → F) where
  toFun h := Multiplicative.ofAdd (fun i => (chiHom i (toGB h)).central)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext i
    simp
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    funext i
    simp only [map_mul, GroupModel.mul_central, toAdd_ofAdd, toAdd_mul, Pi.add_apply]
    rw [show (chiHom i (toGB g)).base = 0 by
      funext c; fin_cases c <;> simp [chiHom_apply, aBit_toGB, bBit_toGB]]
    simp

theorem psiHom_apply (h : Efix) (i : Fin 4) :
    (psiHom h).toAdd i = sgn i (toGB h) := rfl

/-- `g` fixes `E_W` iff it fixes the generators. -/
theorem mem_EWfix_iff (g : Ghat) :
    g ∈ EWfix ↔ g rootOmega = rootOmega ∧ (∀ k, g (genusRootOmega k) = genusRootOmega k) ∧
      ∀ i, g (wOm i) = wOm i := by
  constructor
  · intro hg
    have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg
    refine ⟨hfix _ (IntermediateField.subset_adjoin ℚ _ (Set.mem_insert _ _)),
      fun k => hfix _ (IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem _ (Or.inl ⟨k, rfl⟩))),
      fun i => hfix _ (IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem _ (Or.inr ⟨i, rfl⟩)))⟩
  · rintro ⟨h0, hk, hi⟩
    apply mem_fixingSubgroup_adjoin
    rintro a (rfl | (⟨k, rfl⟩ | ⟨i, rfl⟩))
    · exact h0
    · exact hk k
    · exact hi i

theorem act_wOm_of_Efix (i : Fin 4) (h : Efix) :
    ((toGB h : GB) : Ghat) (wOm i) = binarySign (sgn i (toGB h)) * wOm i := by
  rw [act_wOm, aBit_toGB, bBit_toGB]
  simp [uOm]

theorem ker_psiHom : psiHom.ker = EWfix.subgroupOf Efix := by
  ext h
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have hE := (IntermediateField.mem_fixingSubgroup_iff _ _).1 h.2
  constructor
  · intro h1
    rw [mem_EWfix_iff]
    refine ⟨hE _ rootOmega_mem_EOmega, fun k => hE _ (genusRootOmega_mem_EOmega k), fun i => ?_⟩
    have hs : sgn i (toGB h) = 0 := by
      have := congrArg (fun v : Multiplicative (Fin 4 → F) => v.toAdd i) h1
      simpa [psiHom_apply] using this
    have := act_wOm_of_Efix i h
    rw [hs, binarySign_zero, one_mul] at this
    exact this
  · intro h1
    apply Multiplicative.toAdd.injective
    funext i
    rw [psiHom_apply]
    have hw := ((mem_EWfix_iff _).1 h1).2.2 i
    have := act_wOm_of_Efix i h
    rw [show ((toGB h : GB) : Ghat) = (h : Ghat) from rfl, hw] at this
    apply binarySign_injective (E := Omega)
    apply mul_right_cancel₀ (wOm_ne_zero i)
    rw [← this]
    simp

/-! ### Surjectivity -/

/-- The image of `chiHom i (gen a)` in `F₂²`. -/
theorem chiHom_gen_base (i : Fin 4) (a : Fin 8) :
    (chiHom i (gen a)).base = ![rowA i a, rowB i a] := by
  funext c
  fin_cases c
  · simp [chiHom_apply, aBit_gen, phi1_apply_zero, Pi.single_apply]
  · simp [chiHom_apply, bBit_gen, phi1_apply_one, Pi.single_apply]

/-- `x⁻¹ y⁻¹ x y`. -/
def comm (x y : GB) : GB := x⁻¹ * y⁻¹ * x * y

theorem label_sq_gen (a : Fin 8) : genusLabel (gen a ^ 2) = 1 := by
  rw [map_pow, gen_label]
  apply Multiplicative.toAdd.injective
  simp only [toAdd_pow, toAdd_ofAdd, toAdd_one]
  funext k
  simp only [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply]
  have h : ∀ x : F, (2 : F) * x = 0 := by decide
  push_cast
  exact h _

theorem label_comm (x y : GB) : genusLabel (comm x y) = 1 := by
  simp only [comm, map_mul, map_inv]
  rw [mul_comm (genusLabel x)⁻¹]
  group

theorem chi_sq_central (i : Fin 4) (a : Fin 8) :
    (chiHom i (gen a ^ 2)).central = bilFormula i ![rowA i a, rowB i a] ![rowA i a, rowB i a] := by
  rw [map_pow, GroupModel.square_coordinates, chiHom_gen_base, bilD4_apply]

theorem chi_comm_central (i : Fin 4) (a b : Fin 8) :
    (chiHom i (comm (gen a) (gen b))).central =
      bilFormula i ![rowA i a, rowB i a] ![rowA i b, rowB i b] -
        bilFormula i ![rowA i b, rowB i b] ![rowA i a, rowB i a] := by
  rw [comm, map_mul, map_mul, map_mul, map_inv, map_inv, GroupModel.commutator_coordinates,
    chiHom_gen_base, chiHom_gen_base, bilD4_apply, bilD4_apply]

/-- The four elements of `Gal(Ω/E)` with independent signs. -/
def testElt (j : Fin 4) : GB :=
  ![gen 0 ^ 2, comm (gen 0) (gen 1), comm (gen 0) (gen 4), comm (gen 1) (gen 3)] j

theorem testElt_label (j : Fin 4) : genusLabel (testElt j) = 1 := by
  fin_cases j
  · exact label_sq_gen 0
  · exact label_comm _ _
  · exact label_comm _ _
  · exact label_comm _ _

theorem testElt_mem (j : Fin 4) : ((testElt j : GB) : Ghat) ∈ Efix :=
  (mem_ker_genusLabelHom_iff (testElt j)).mp (testElt_label j)

/-- Their sign vectors. -/
def testVec (j : Fin 4) : Fin 4 → F :=
  ![![1, 0, 0, 0], ![1, 1, 1, 0], ![1, 1, 0, 1], ![1, 1, 0, 0]] j

theorem testVec_certificate : ∀ j i : Fin 4,
    (![bilFormula i ![rowA i 0, rowB i 0] ![rowA i 0, rowB i 0],
      bilFormula i ![rowA i 0, rowB i 0] ![rowA i 1, rowB i 1] -
        bilFormula i ![rowA i 1, rowB i 1] ![rowA i 0, rowB i 0],
      bilFormula i ![rowA i 0, rowB i 0] ![rowA i 4, rowB i 4] -
        bilFormula i ![rowA i 4, rowB i 4] ![rowA i 0, rowB i 0],
      bilFormula i ![rowA i 1, rowB i 1] ![rowA i 3, rowB i 3] -
        bilFormula i ![rowA i 3, rowB i 3] ![rowA i 1, rowB i 1]] : Fin 4 → F) j = testVec j i := by
  decide

theorem psiHom_testElt (j : Fin 4) :
    (psiHom ⟨_, testElt_mem j⟩).toAdd = testVec j := by
  funext i
  rw [psiHom_apply, ← testVec_certificate j i]
  change (chiHom i (testElt j)).central = _
  fin_cases j
  · exact chi_sq_central i 0
  · exact chi_comm_central i 0 1
  · exact chi_comm_central i 0 4
  · exact chi_comm_central i 1 3

/-- Every vector of `F₂⁴` is a combination of the four test vectors. -/
theorem testVec_span : ∀ t : Fin 4 → F, ∃ c : Fin 4 → F, t = ∑ j, c j • testVec j := by
  decide

theorem psiHom_surjective : Function.Surjective psiHom := by
  intro t
  obtain ⟨c, hc⟩ := testVec_span t.toAdd
  let x : Fin 4 → Efix := fun j => ⟨_, testElt_mem j⟩
  have h : ∀ (x : F) (j : Fin 4), x.val • (testVec j) = x • testVec j := by
    intro x j
    rw [← Nat.cast_smul_eq_nsmul F, ZMod.natCast_zmod_val]
  refine ⟨x 0 ^ (c 0).val * x 1 ^ (c 1).val * x 2 ^ (c 2).val * x 3 ^ (c 3).val, ?_⟩
  apply Multiplicative.toAdd.injective
  simp only [map_mul, map_pow, toAdd_mul, toAdd_pow, x, psiHom_testElt, h]
  rw [hc, Fin.sum_univ_four]

theorem relIndex_EWfix : (EWfix.subgroupOf Efix).index = 16 := by
  rw [← ker_psiHom, Subgroup.index_ker, MonoidHom.range_eq_top.mpr psiHom_surjective,
    Subgroup.card_top, Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 4 → F) ≃ _)]
  simp

/-- **`[E_W : ℚ] = 8192`.** -/
theorem finrank_field : Module.finrank ℚ CanonicalWide.Carrier = 8192 := by
  change Module.finrank ℚ CanonicalWide.field = 8192
  rw [← lift_EWOmega, ← (IntermediateField.liftAlgEquiv EWOmega).toLinearEquiv.finrank_eq,
    IntermediateField.finrank_eq_fixingSubgroup_index]
  have h := Subgroup.relIndex_mul_index EWfix_le_Efix
  rw [index_Efix] at h
  change (EWfix.subgroupOf Efix).index * 512 = EWfix.index at h
  rw [relIndex_EWfix] at h
  exact h.symm.trans (by norm_num)

end UnitDistance.Sqrt241.Wide
