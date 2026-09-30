module

public import UnitDistance.DyadicGroup
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section
set_option backward.privateInPublic true


/-!
# The actual dyadic group algebra and its common annihilator

All products here are Mathlib's convolution products in `𝔽₂[D]` for the
concrete normal-form group. In particular these are not ranks of unattached
matrices. The common left annihilator of the generator differences is proved
to be the line spanned by the sum of all 32 group elements. The augmentation
kernel has dimension 31. The deeper augmentation filtration dimensions and
the degree-seven placement of the socle remain separate obligations.
-/

noncomputable section

open scoped BigOperators

namespace UnitDistance.Dyadic

abbrev F := ZMod 2
abbrev AlgebraD := MonoidAlgebra F D

namespace AlgebraD

/-- The basis group element in the ordinary convolution algebra. -/
def delta (g : D) : AlgebraD := MonoidAlgebra.single g 1

@[simp] theorem delta_one : delta 1 = 1 := rfl
@[simp] theorem delta_mul (g h : D) : delta g * delta h = delta (g * h) := by
  simp [delta, MonoidAlgebra.single_mul_single]

/-- Sum of all basis group elements; every coefficient is one. -/
def normSum : AlgebraD := ∑ g : D, delta g

@[simp] theorem coeff_normSum (g : D) : normSum.coeff g = 1 := by
  simp [normSum, delta, MonoidAlgebra.coeff_sum]

theorem normSum_ne_zero : normSum ≠ 0 := by
  intro h
  have := congrArg (fun v : AlgebraD => v.coeff 1) h
  simp at this

/-- The augmentation is the sum of the actual group-algebra coefficients. -/
def augmentation : AlgebraD →ₗ[F] F where
  toFun v := ∑ g : D, v.coeff g
  map_add' _ _ := by simp [Finset.sum_add_distrib]
  map_smul' _ _ := by simp [Finset.mul_sum]

@[simp] theorem augmentation_delta (g : D) : augmentation (delta g) = 1 := by
  change (∑ x : D, (MonoidAlgebra.single g (1 : F)).coeff x) = 1
  simp [MonoidAlgebra.coeff_single]

@[simp] theorem augmentation_single (g : D) (a : F) :
    augmentation (MonoidAlgebra.single g a) = a := by
  change (∑ x : D, (MonoidAlgebra.single g a).coeff x) = a
  simp [MonoidAlgebra.coeff_single]

@[simp] theorem augmentation_one : augmentation 1 = 1 :=
  augmentation_delta 1

/-- The coefficient sum is the usual ring augmentation, not just a linear
functional chosen for its kernel dimension. -/
theorem augmentation_mul (v w : AlgebraD) :
    augmentation (v * w) = augmentation v * augmentation w := by
  induction v using MonoidAlgebra.induction_linear with
  | zero => simp
  | add v₁ v₂ h₁ h₂ => simp [add_mul, h₁, h₂]
  | single g a =>
    induction w using MonoidAlgebra.induction_linear with
    | zero => simp
    | add w₁ w₂ h₁ h₂ => simp [mul_add, h₁, h₂]
    | single h b => simp [MonoidAlgebra.single_mul_single]

def augmentationRingHom : AlgebraD →+* F where
  toFun := augmentation
  map_one' := augmentation_one
  map_mul' := augmentation_mul
  map_zero' := map_zero augmentation
  map_add' := map_add augmentation

theorem augmentation_surjective : Function.Surjective augmentation := by
  intro a
  refine ⟨a • delta 1, ?_⟩
  simp only [map_smul, augmentation_delta, smul_eq_mul, mul_one]

theorem finrank_algebra : Module.finrank F AlgebraD = 32 := by
  rw [Module.finrank_eq_card_basis (MonoidAlgebra.basis D F)]
  exact D.card

instance : FiniteDimensional F AlgebraD :=
  Module.Finite.of_basis (MonoidAlgebra.basis D F)

theorem finrank_augmentation_kernel : Module.finrank F augmentation.ker = 31 := by
  have h := augmentation.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr augmentation_surjective,
    finrank_top, Module.finrank_self, finrank_algebra] at h
  omega

/-- Right multiplication by a fixed group-algebra element is linear. -/
def rightMul (b : AlgebraD) : AlgebraD →ₗ[F] AlgebraD where
  toFun v := v * b
  map_add' _ _ := add_mul ..
  map_smul' _ _ := smul_mul_assoc ..

/-- The common left annihilator of every augmentation generator `g - 1`. -/
def socle : Submodule F AlgebraD := ⨅ g : D, (rightMul (delta g - 1)).ker

@[simp] theorem mem_socle (v : AlgebraD) :
    v ∈ socle ↔ ∀ g : D, v * (delta g - 1) = 0 := by
  simp [socle, rightMul]

theorem mul_delta_sub_one_eq_zero_iff (v : AlgebraD) (g : D) :
    v * (delta g - 1) = 0 ↔ v * delta g = v := by
  rw [mul_sub, mul_one, sub_eq_zero]

/-- The elements whose right translations fix a chosen algebra vector form
an actual subgroup of `D`. -/
def rightFixed (v : AlgebraD) : Subgroup D where
  carrier := {g | v * delta g = v}
  one_mem' := by simp
  mul_mem' {g h} hg hh := by
    change v * delta (g * h) = v
    rw [← delta_mul, ← mul_assoc, hg, hh]
  inv_mem' {g} hg := by
    change v * delta g⁻¹ = v
    have h := congrArg (fun u : AlgebraD => u * delta g⁻¹) hg
    simpa only [mul_assoc, delta_mul, mul_inv_cancel, delta_one, mul_one] using h.symm

/-- It suffices to annihilate the three named generator differences. -/
theorem mem_socle_iff_generators (v : AlgebraD) :
    v ∈ socle ↔
      v * (delta D.x - 1) = 0 ∧
      v * (delta D.y - 1) = 0 ∧
      v * (delta D.z - 1) = 0 := by
  constructor
  · intro h
    exact ⟨(mem_socle v).mp h D.x, (mem_socle v).mp h D.y,
      (mem_socle v).mp h D.z⟩
  · rintro ⟨hx, hy, hz⟩
    have hcl : Subgroup.closure ({D.x, D.y, D.z} : Set D) ≤ rightFixed v := by
      apply (Subgroup.closure_le (rightFixed v)).mpr
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · exact (mul_delta_sub_one_eq_zero_iff v D.x).mp hx
      · exact (mul_delta_sub_one_eq_zero_iff v D.y).mp hy
      · exact (mul_delta_sub_one_eq_zero_iff v D.z).mp hz
    rw [D.generators] at hcl
    apply (mem_socle v).mpr
    intro g
    exact (mul_delta_sub_one_eq_zero_iff v g).mpr (hcl (Subgroup.mem_top g))

/-- A vector is in the common annihilator precisely when its ordinary
coefficients are constant on the whole group. -/
theorem mem_socle_iff_coeff (v : AlgebraD) :
    v ∈ socle ↔ ∀ g : D, v.coeff g = v.coeff 1 := by
  constructor
  · intro h g
    have hg := (mul_delta_sub_one_eq_zero_iff v g).mp ((mem_socle v).mp h g)
    have hc := congrArg (fun u : AlgebraD => u.coeff g) hg
    simpa [delta] using hc.symm
  · intro h
    apply (mem_socle v).mpr
    intro g
    apply (mul_delta_sub_one_eq_zero_iff v g).mpr
    ext k
    simp only [delta, MonoidAlgebra.coeff_mul_single_apply, mul_one]
    exact (h _).trans (h _).symm

theorem socle_eq_span : socle = Submodule.span F {normSum} := by
  ext v
  rw [Submodule.mem_span_singleton]
  constructor
  · intro h
    refine ⟨v.coeff 1, ?_⟩
    ext g
    simp [(mem_socle_iff_coeff v).mp h g]
  · rintro ⟨a, rfl⟩
    apply (mem_socle_iff_coeff _).mpr
    intro g
    simp

/-- The common left annihilator of `x-1,y-1,z-1` has dimension one. -/
theorem finrank_socle : Module.finrank F socle = 1 := by
  rw [socle_eq_span]
  exact finrank_span_singleton normSum_ne_zero

theorem sum_smul_delta (v : AlgebraD) :
    ∑ g : D, v.coeff g • delta g = v := by
  ext h
  simp [delta, MonoidAlgebra.coeff_sum]

/-- Every augmentation-zero vector is the expected linear combination of
the differences `g - 1`. -/
theorem augmentation_zero_expansion (v : AlgebraD) (hv : augmentation v = 0) :
    ∑ g : D, v.coeff g • (delta g - 1) = v := by
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib, sum_smul_delta, ← Finset.sum_smul]
  change v - augmentation v • 1 = v
  simp [hv]

/-- This identifies the common-annihilator definition with the ordinary
left socle of the augmentation ideal. -/
theorem mem_socle_iff_annihilates_augmentation (v : AlgebraD) :
    v ∈ socle ↔ ∀ b : AlgebraD, augmentation b = 0 → v * b = 0 := by
  constructor
  · intro hv b hb
    rw [← augmentation_zero_expansion b hb, Finset.mul_sum]
    simp only [mul_smul_comm, (mem_socle v).mp hv, smul_zero, Finset.sum_const_zero]
  · intro h
    apply (mem_socle v).mpr
    intro g
    apply h
    simp

theorem augmentation_normSum : augmentation normSum = 0 := by
  norm_num [normSum, D.card]
  decide

theorem socle_le_augmentation_kernel : socle ≤ augmentation.ker := by
  rw [socle_eq_span]
  apply Submodule.span_le.mpr
  intro v hv
  rw [Set.mem_singleton_iff] at hv
  rw [hv]
  exact augmentation_normSum

end AlgebraD
end UnitDistance.Dyadic
