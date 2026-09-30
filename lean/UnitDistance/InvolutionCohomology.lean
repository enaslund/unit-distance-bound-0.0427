module

public import Mathlib.GroupTheory.IndexNSmul
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.LinearAlgebra.Dimension.Localization

@[expose] public section
set_option backward.privateInPublic true


/-!
# Integral index identities for an involution

The plus and minus groups below are actual kernels, with no assumed integral
splitting. The index of their sum is accounted for explicitly on both sides.
This is the integral-group prerequisite of the Herbrand quotient formula.
-/

noncomputable section

namespace UnitDistance.InvolutionCohomology

variable {M : Type*} [AddCommGroup M]

/-- The cyclic norm `1 + σ`. -/
def norm (σ : M ≃+ M) : M →+ M := AddMonoidHom.id M + σ.toAddMonoidHom

/-- The cyclic boundary `1 - σ`. -/
def boundary (σ : M ≃+ M) : M →+ M := AddMonoidHom.id M - σ.toAddMonoidHom

def plus (σ : M ≃+ M) : AddSubgroup M := (boundary σ).ker

def minus (σ : M ≃+ M) : AddSubgroup M := (norm σ).ker

@[simp] theorem norm_apply (σ : M ≃+ M) (x : M) : norm σ x = x + σ x := rfl
@[simp] theorem boundary_apply (σ : M ≃+ M) (x : M) : boundary σ x = x - σ x := rfl

@[simp] theorem mem_plus (σ : M ≃+ M) (x : M) : x ∈ plus σ ↔ σ x = x := by
  change x - σ x = 0 ↔ σ x = x
  rw [sub_eq_zero, eq_comm]

@[simp] theorem mem_minus (σ : M ≃+ M) (x : M) : x ∈ minus σ ↔ σ x = -x := by
  simp [minus, norm, eq_neg_iff_add_eq_zero, add_comm]

variable (σ : M ≃+ M) (hσ : Function.Involutive σ)

include hσ in
theorem range_norm_le_plus : (norm σ).range ≤ plus σ := by
  rintro x ⟨y, rfl⟩
  simp [hσ y, add_comm]

include hσ in
theorem range_boundary_le_minus : (boundary σ).range ≤ minus σ := by
  rintro x ⟨y, rfl⟩
  simp [hσ y, neg_sub]

/-- On actual fixed elements, the norm is doubling. -/
theorem map_plus_norm : (plus σ).map (norm σ) =
    (plus σ).map (nsmulAddMonoidHom (α := M) 2) := by
  ext z
  simp only [AddSubgroup.mem_map]
  refine exists_congr fun x ↦ and_congr_right fun hx ↦ ?_
  simp [(mem_plus σ x).mp hx, two_nsmul]

/-- On actual anti-fixed elements, the boundary is doubling. -/
theorem map_minus_boundary : (minus σ).map (boundary σ) =
    (minus σ).map (nsmulAddMonoidHom (α := M) 2) := by
  ext z
  simp only [AddSubgroup.mem_map]
  refine exists_congr fun x ↦ and_congr_right fun hx ↦ ?_
  simp [(mem_minus σ x).mp hx, two_nsmul]

/-- The full integral preimage is the sum of the two actual eigengroups. -/
theorem comap_double_plus_norm :
    ((plus σ).map (nsmulAddMonoidHom (α := M) 2)).comap (norm σ) = plus σ ⊔ minus σ := by
  rw [← map_plus_norm, AddSubgroup.comap_map_eq]
  rfl

theorem comap_double_minus_boundary :
    ((minus σ).map (nsmulAddMonoidHom (α := M) 2)).comap (boundary σ) = plus σ ⊔ minus σ := by
  rw [← map_minus_boundary, AddSubgroup.comap_map_eq]
  exact sup_comm _ _

/-- The same integral-splitting index occurs on the norm side. -/
theorem relIndex_double_plus_range_norm :
    ((plus σ).map (nsmulAddMonoidHom (α := M) 2)).relIndex (norm σ).range =
      (plus σ ⊔ minus σ).index := by
  rw [← AddSubgroup.index_comap, comap_double_plus_norm]

/-- The same integral-splitting index occurs on the boundary side. -/
theorem relIndex_double_minus_range_boundary :
    ((minus σ).map (nsmulAddMonoidHom (α := M) 2)).relIndex (boundary σ).range =
      (plus σ ⊔ minus σ).index := by
  rw [← AddSubgroup.index_comap, comap_double_minus_boundary]

include hσ in
/-- The norm-side index factors through its actual image. -/
theorem double_plus_index_factorization :
    ((plus σ).map (nsmulAddMonoidHom (α := M) 2)).relIndex (plus σ) =
      (plus σ ⊔ minus σ).index * (norm σ).range.relIndex (plus σ) := by
  rw [← AddSubgroup.relIndex_mul_relIndex _ (norm σ).range (plus σ)]
  · rw [relIndex_double_plus_range_norm]
  · rw [← map_plus_norm]
    exact AddSubgroup.map_le_range _ _
  · exact range_norm_le_plus σ hσ

include hσ in
/-- The boundary-side index has the identical intermediate factor. -/
theorem double_minus_index_factorization :
    ((minus σ).map (nsmulAddMonoidHom (α := M) 2)).relIndex (minus σ) =
      (plus σ ⊔ minus σ).index * (boundary σ).range.relIndex (minus σ) := by
  rw [← AddSubgroup.relIndex_mul_relIndex _ (boundary σ).range (minus σ)]
  · rw [relIndex_double_minus_range_boundary]
  · rw [← map_minus_boundary]
    exact AddSubgroup.map_le_range _ _
  · exact range_boundary_le_minus σ hσ

include hσ in
/-- Exact cross-index identity before using finite generation or ranks.
It holds without splitting the integral group into its eigengroups. -/
theorem herbrand_cross_index :
    (norm σ).range.relIndex (plus σ) *
        ((minus σ).map (nsmulAddMonoidHom (α := M) 2)).relIndex (minus σ) =
      (boundary σ).range.relIndex (minus σ) *
        ((plus σ).map (nsmulAddMonoidHom (α := M) 2)).relIndex (plus σ) := by
  rw [double_plus_index_factorization σ hσ, double_minus_index_factorization σ hσ]
  ac_rfl

include hσ in
/-- Every double is the sum of a norm and a boundary, so the actual eigengroup
sum has finite index whenever the ambient abelian group is finitely generated. -/
theorem double_range_le_eigen_sum :
    (nsmulAddMonoidHom (α := M) 2).range ≤ plus σ ⊔ minus σ := by
  rintro x ⟨y, rfl⟩
  have hn : norm σ y ∈ plus σ := range_norm_le_plus σ hσ ⟨y, rfl⟩
  have hd : boundary σ y ∈ minus σ := range_boundary_le_minus σ hσ ⟨y, rfl⟩
  convert AddSubgroup.add_mem_sup hn hd using 1
  simp [two_nsmul, sub_eq_add_neg, add_assoc, add_left_comm]

include hσ in
theorem eigen_sum_finiteIndex [AddGroup.FG M] : (plus σ ⊔ minus σ).FiniteIndex := by
  letI := AddSubgroup.finiteIndex_range_nsmulAddMonoidHom_of_fg M (by decide : (2 : ℕ) ≠ 0)
  exact AddSubgroup.finiteIndex_of_le (double_range_le_eigen_sum σ hσ)

set_option backward.isDefEq.respectTransparency false in
/-- A finitely generated abelian group splits as its actual torsion subgroup and
its torsion-free quotient. The section is constructed by projectivity. -/
def torsionProdQuotientEquiv [Module.Finite ℤ M] :
    ((Submodule.torsion ℤ M) × (M ⧸ Submodule.torsion ℤ M)) ≃ₗ[ℤ] M := by
  let h := Module.projective_lifting_property _ LinearMap.id
    (Submodule.torsion ℤ M).mkQ_surjective
  let f := Classical.choose h
  have hf := Classical.choose_spec h
  exact lequivProdOfRightSplitExact (Submodule.torsion ℤ M).injective_subtype
    (by rw [Submodule.range_subtype, Submodule.ker_mkQ]) hf

variable {N : Type*} [AddCommGroup N]

/-- Kernel of doubling is preserved by an additive isomorphism. -/
def doubleKernelEquiv (e : M ≃+ N) :
    (nsmulAddMonoidHom (α := M) 2).ker ≃+
      (nsmulAddMonoidHom (α := N) 2).ker where
  toFun x := ⟨e x, by
    change 2 • e (x : M) = 0
    rw [← map_nsmul, show 2 • (x : M) = 0 from x.prop, map_zero]⟩
  invFun x := ⟨e.symm x, by
    change 2 • e.symm (x : N) = 0
    rw [← map_nsmul, show 2 • (x : N) = 0 from x.prop, map_zero]⟩
  left_inv x := by ext; simp
  right_inv x := by ext; simp
  map_add' x y := by ext; simp

theorem double_range_prod :
    (nsmulAddMonoidHom (α := M × N) 2).range =
      (nsmulAddMonoidHom (α := M) 2).range.prod
        (nsmulAddMonoidHom (α := N) 2).range := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨⟨a, b⟩, h⟩
    exact ⟨⟨a, congrArg Prod.fst h⟩, ⟨b, congrArg Prod.snd h⟩⟩
  · rintro ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
    exact ⟨(a, b), rfl⟩

/-- A torsion-free factor contributes no elements to the kernel of doubling. -/
def doubleKernelProdEquiv [Module.IsTorsionFree ℤ N] :
    (nsmulAddMonoidHom (α := M × N) 2).ker ≃+
      (nsmulAddMonoidHom (α := M) 2).ker where
  toFun x := ⟨x.val.1, congrArg Prod.fst x.prop⟩
  invFun x := ⟨(x.val, 0), by ext <;> simp [show 2 • (x : M) = 0 from x.prop]⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree
        (M := N) (by decide : (2 : ℕ) ≠ 0))
        (by
          change 2 • (0 : N) = 2 • x.val.2
          rw [nsmul_zero]
          exact (congrArg Prod.snd x.prop).symm)
  right_inv x := rfl
  map_add' x y := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Exact index of doubling for every finitely generated abelian group,
including its finite torsion contribution. -/
theorem index_double [Module.Finite ℤ M] :
    (nsmulAddMonoidHom (α := M) 2).range.index =
      2 ^ Module.finrank ℤ M * Nat.card (nsmulAddMonoidHom (α := M) 2).ker := by
  let T := Submodule.torsion ℤ M
  let Q := M ⧸ T
  letI : Module ℤ Q := Submodule.Quotient.module T
  letI : Module.IsTorsionFree ℤ Q := inferInstance
  let e := (torsionProdQuotientEquiv (M := M)).toAddEquiv
  letI : Finite T := Module.finite_of_fg_torsion T (@Submodule.torsion_isTorsion ℤ M _ _ _)
  have hcard : Nat.card (nsmulAddMonoidHom (α := M) 2).ker =
      Nat.card (nsmulAddMonoidHom (α := T) 2).ker :=
    Nat.card_congr ((doubleKernelEquiv e.symm).trans doubleKernelProdEquiv).toEquiv
  have hrank : Module.finrank ℤ Q = Module.finrank ℤ M :=
    finrank_quotient_eq_of_le_torsion (le_refl T)
  have hindex : (nsmulAddMonoidHom (α := M) 2).range.index =
      (nsmulAddMonoidHom (α := T × Q) 2).range.index := by
    simpa [AddEquiv.map_range_nsmulAddMonoidHom] using
      AddSubgroup.index_map_equiv (nsmulAddMonoidHom (α := T × Q) 2).range e
  rw [hindex, double_range_prod, AddSubgroup.index_prod,
    AddSubgroup.index_range, AddSubgroup.index_range_nsmul Q 2, hrank, hcard, mul_comm]

set_option backward.isDefEq.respectTransparency false in
/-- Finite generation passes to every subgroup of a finitely generated abelian group. -/
theorem subgroup_moduleFinite [Module.Finite ℤ M] (S : AddSubgroup M) :
    Module.Finite ℤ S := by
  exact inferInstanceAs (Module.Finite ℤ S.toIntSubmodule)

/-- The two actual eigengroups have the same two-torsion, even when they do not
split the integral group. -/
def eigenDoubleKernelEquiv (σ : M ≃+ M) :
    (nsmulAddMonoidHom (α := plus σ) 2).ker ≃+
      (nsmulAddMonoidHom (α := minus σ) 2).ker where
  toFun x := ⟨⟨x.val.val, by
    apply (mem_minus σ _).mpr
    rw [(mem_plus σ _).mp x.val.prop]
    apply eq_neg_iff_add_eq_zero.mpr
    have hx : 2 • x.val.val = 0 := congrArg Subtype.val x.prop
    simpa only [two_nsmul] using hx⟩, by
      apply Subtype.ext
      change 2 • x.val.val = 0
      exact congrArg (fun z : plus σ => (z : M)) x.prop⟩
  invFun x := ⟨⟨x.val.val, by
    apply (mem_plus σ _).mpr
    rw [(mem_minus σ _).mp x.val.prop]
    apply (eq_neg_iff_add_eq_zero.mpr ?_).symm
    have hx : 2 • x.val.val = 0 := congrArg Subtype.val x.prop
    simpa only [two_nsmul] using hx⟩, by
      apply Subtype.ext
      change 2 • x.val.val = 0
      exact congrArg (fun z : minus σ => (z : M)) x.prop⟩
  left_inv x := rfl
  right_inv x := rfl
  map_add' x y := rfl

/-- The doubling kernel of a finitely generated abelian group is finite. -/
theorem double_kernel_finite [Module.Finite ℤ M] :
    Finite (nsmulAddMonoidHom (α := M) 2).ker := by
  letI := subgroup_moduleFinite (nsmulAddMonoidHom (α := M) 2).ker
  apply Module.finite_of_fg_torsion
  intro x
  refine ⟨⟨2, by simp⟩, ?_⟩
  change (2 : ℤ) • x = 0
  apply Subtype.ext
  change (2 : ℤ) • (x : M) = 0
  simpa only [two_zsmul, two_nsmul] using (show 2 • (x : M) = 0 from x.prop)

/-- Relative doubling index, including torsion, for an arbitrary subgroup. -/
theorem relIndex_double [Module.Finite ℤ M] (S : AddSubgroup M) :
    (S.map (nsmulAddMonoidHom (α := M) 2)).relIndex S =
      2 ^ Module.finrank ℤ S * Nat.card (nsmulAddMonoidHom (α := S) 2).ker := by
  letI := subgroup_moduleFinite S
  simpa only [AddSubgroup.relIndex, AddSubgroup.addSubgroupOf_map_nsmulAddMonoidHom_eq_range]
    using index_double (M := S)

include hσ in
/-- The Herbrand quotient identity for an involution on any finitely generated
abelian group. The common two-torsion factor cancels, and the two ranks are
those of the actual integral kernels. -/
theorem herbrand_rank_index [Module.Finite ℤ M] :
    (norm σ).range.relIndex (plus σ) * 2 ^ Module.finrank ℤ (minus σ) =
      (boundary σ).range.relIndex (minus σ) * 2 ^ Module.finrank ℤ (plus σ) := by
  have h := herbrand_cross_index σ hσ
  rw [relIndex_double, relIndex_double] at h
  have hc := Nat.card_congr (eigenDoubleKernelEquiv σ).toEquiv
  rw [hc] at h
  letI := subgroup_moduleFinite (minus σ)
  letI := double_kernel_finite (M := minus σ)
  have hpos : 0 < Nat.card (nsmulAddMonoidHom (α := minus σ) 2).ker := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (by simpa only [← mul_assoc] using h)

set_option backward.isDefEq.respectTransparency false in
/-- A subgroup of finite index in a finitely generated abelian group has the
same integral rank, including when the ambient group has torsion. -/
theorem finrank_eq_of_finiteIndex [Module.Finite ℤ M] (S : AddSubgroup M)
    [S.FiniteIndex] : Module.finrank ℤ S = Module.finrank ℤ M := by
  letI : Finite (M ⧸ S.toIntSubmodule) := inferInstanceAs (Finite (M ⧸ S))
  have hz : Module.finrank ℤ (M ⧸ S.toIntSubmodule) = 0 := by
    apply Module.finrank_eq_zero_iff_isTorsion.mpr
    exact AddMonoid.isTorsion_iff_isTorsion_int.mp is_add_torsion_of_finite
  have h := S.toIntSubmodule.finrank_quotient_add_finrank
  rw [hz, zero_add] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Integral rank-nullity for an additive map between finitely generated abelian groups. -/
theorem rank_range_add_rank_ker [Module.Finite ℤ M] (f : M →+ N) :
    Module.finrank ℤ f.range + Module.finrank ℤ f.ker = Module.finrank ℤ M := by
  have h := f.toIntLinearMap.ker.finrank_quotient_add_finrank
  rw [f.toIntLinearMap.quotKerEquivRange.finrank_eq] at h
  exact h

end UnitDistance.InvolutionCohomology
