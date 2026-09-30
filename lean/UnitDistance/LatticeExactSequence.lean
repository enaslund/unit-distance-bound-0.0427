module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Algebra.Module.PID
public import Mathlib.LinearAlgebra.Basis.Prod

@[expose] public section
set_option backward.privateInPublic true


/-!
# Covolume multiplication for an actual coordinate projection of a lattice

The image and kernel lattices below are defined from an ordinary coordinate
projection. The integral section is constructed from freeness of the image.
The determinant calculation is linked to actual lattice covolumes.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open Module

namespace UnitDistance.LatticeExactSequence

variable {I J : Type*}

/-- Inclusion into the first coordinate block. -/
def leftEmbed : (I → ℝ) →ₗ[ℤ] (I ⊕ J → ℝ) where
  toFun x := Sum.elim x 0
  map_add' x y := by ext (i | j) <;> simp
  map_smul' r x := by ext (i | j) <;> simp

/-- Projection onto the second coordinate block. -/
def rightProj : (I ⊕ J → ℝ) →ₗ[ℤ] (J → ℝ) where
  toFun x j := x (Sum.inr j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (L : Submodule ℤ (I ⊕ J → ℝ))

/-- The actual coordinate kernel lattice, expressed in its first block. -/
def kernelLattice : Submodule ℤ (I → ℝ) := L.comap leftEmbed

/-- The actual projected image lattice. -/
def imageLattice : Submodule ℤ (J → ℝ) := L.map rightProj

def kernelInclusion : kernelLattice L →ₗ[ℤ] L where
  toFun x := ⟨leftEmbed x.val, x.prop⟩
  map_add' x y := by apply Subtype.ext; exact map_add leftEmbed x.val y.val
  map_smul' r x := by apply Subtype.ext; exact map_smul leftEmbed r x.val

def imageProjection : L →ₗ[ℤ] imageLattice L where
  toFun x := ⟨rightProj x.val, ⟨x.val, x.prop, rfl⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem kernelInclusion_injective : Function.Injective (kernelInclusion L) := by
  intro x y h
  apply Subtype.ext
  funext i
  exact congrArg (fun z : L ↦ z.val (Sum.inl i)) h

theorem imageProjection_surjective : Function.Surjective (imageProjection L) := by
  rintro ⟨y, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

@[simp] theorem imageProjection_kernelInclusion (x : kernelLattice L) :
    imageProjection L (kernelInclusion L x) = 0 := rfl

theorem kernelInclusion_range : (kernelInclusion L).range = (imageProjection L).ker := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rfl
  · intro hx
    have hz : ∀ j, x.val (Sum.inr j) = 0 := fun j ↦
      congrArg (fun y : imageLattice L ↦ y.val j) hx
    have he : leftEmbed (fun i ↦ x.val (Sum.inl i)) = x.val := by
      ext (i | j)
      · rfl
      · exact (hz j).symm
    exact ⟨⟨fun i ↦ x.val (Sum.inl i), by
      change leftEmbed (fun i ↦ x.val (Sum.inl i)) ∈ L
      rw [he]
      exact x.prop⟩, Subtype.ext he⟩

variable [Fintype I] [Fintype J] [DiscreteTopology (imageLattice L)]

/-- An actual integral section exists because the image lattice is free. -/
def imageSection : imageLattice L →ₗ[ℤ] L :=
  Classical.choose (Module.projective_lifting_property
    (imageProjection L) LinearMap.id (imageProjection_surjective L))

omit [Fintype I] in
@[simp] theorem imageProjection_imageSection (y : imageLattice L) :
    imageProjection L (imageSection L y) = y :=
  LinearMap.congr_fun (Classical.choose_spec (Module.projective_lifting_property
    (imageProjection L) LinearMap.id (imageProjection_surjective L))) y

/-- An integral splitting of the coordinate-projection exact sequence. -/
def latticeSplitEquiv : (kernelLattice L × imageLattice L) ≃ₗ[ℤ] L :=
  LinearEquiv.ofBijective ((kernelInclusion L).coprod (imageSection L)) (by
    constructor
    · rintro ⟨k, n⟩ ⟨k', n'⟩ h
      have hn : n = n' := by
        have hp := congrArg (imageProjection L) h
        simpa only [LinearMap.coprod_apply, map_add, imageProjection_kernelInclusion,
          imageProjection_imageSection, zero_add] using hp
      apply Prod.ext
      · apply kernelInclusion_injective L
        change kernelInclusion L k + imageSection L n =
          kernelInclusion L k' + imageSection L n' at h
        rw [hn] at h
        exact add_right_cancel h
      · exact hn
    · intro x
      have hx : x - imageSection L (imageProjection L x) ∈ (imageProjection L).ker := by
        simp [LinearMap.mem_ker]
      rw [← kernelInclusion_range] at hx
      obtain ⟨k, hk⟩ := hx
      refine ⟨(k, imageProjection L x), ?_⟩
      change kernelInclusion L k + imageSection L (imageProjection L x) = x
      rw [hk, sub_add_cancel])

omit [Fintype I] in
@[simp] theorem latticeSplitEquiv_apply (k : kernelLattice L) (n : imageLattice L) :
    latticeSplitEquiv L (k, n) = kernelInclusion L k + imageSection L n := rfl

variable [DiscreteTopology L] [IsZLattice ℝ L]

/-- Fullness of the projected image follows from the original lattice. -/
instance imageLattice_isZLattice : IsZLattice ℝ (imageLattice L) where
  span_top := by
    have hp : ∀ x : I ⊕ J → ℝ, x ∈ Submodule.span ℝ (L : Set (I ⊕ J → ℝ)) →
        rightProj x ∈ Submodule.span ℝ (imageLattice L : Set (J → ℝ)) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
      | zero => exact Submodule.zero_mem _
      | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
      | smul r x _ hx =>
        change r • rightProj x ∈ _
        exact Submodule.smul_mem _ r hx
    apply top_unique
    intro y _
    have hx : Sum.elim (0 : I → ℝ) y ∈ Submodule.span ℝ (L : Set (I ⊕ J → ℝ)) := by
      rw [IsZLattice.span_top]
      trivial
    exact hp (Sum.elim 0 y) hx

/-- The actual kernel lattice is discrete, by injective continuous coordinate inclusion. -/
instance kernelLattice_discrete : DiscreteTopology (kernelLattice L) := by
  let f : (I → ℝ) →ₗ[ℝ] (I ⊕ J → ℝ) :=
    { toFun := fun x ↦ Sum.elim x 0
      map_add' := by intros; ext (i | j) <;> simp
      map_smul' := by intros; ext (i | j) <;> simp }
  exact DiscreteTopology.preimage_of_continuous_injective (L : Set (I ⊕ J → ℝ))
    f.continuous_of_finiteDimensional (fun x y h ↦ funext fun i ↦ congrFun h (Sum.inl i))

/-- The actual kernel rank is the number of its coordinate directions. -/
theorem kernelLattice_rank : Module.finrank ℤ (kernelLattice L) = Fintype.card I := by
  have h := (latticeSplitEquiv L).finrank_eq
  rw [Module.finrank_prod, ZLattice.rank ℝ (imageLattice L), ZLattice.rank ℝ L,
    Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card,
    Fintype.card_sum] at h
  exact Nat.add_right_cancel h

/-- No fullness hypothesis on the kernel is needed: the exact integral sequence
and the real/integer rank comparison for discrete groups prove it. -/
instance kernelLattice_isZLattice : IsZLattice ℝ (kernelLattice L) where
  span_top := by
    apply Submodule.eq_top_of_finrank_eq
    have hd : DiscreteTopology (Submodule.span ℤ (kernelLattice L : Set (I → ℝ))) := by
      rw [Submodule.span_eq]
      infer_instance
    have hr := Real.finrank_eq_int_finrank_of_discrete hd
    rw [Set.finrank, Set.finrank, Submodule.span_eq, kernelLattice_rank] at hr
    simpa only [Module.finrank_fintype_fun_eq_card] using hr

/-- A product basis transported by the constructed integral section is a basis
of the actual original lattice. -/
def latticeSplitBasis : Basis (I ⊕ J) ℤ L :=
  ((IsZLattice.basis (kernelLattice L)).prod (IsZLattice.basis (imageLattice L))).map
    (latticeSplitEquiv L)

/-- The coordinate matrix of the actual lattice basis is block triangular. -/
theorem latticeSplitBasis_matrix :
    Matrix.of (fun i ↦ ((latticeSplitBasis L i : L) : I ⊕ J → ℝ)) =
      Matrix.fromBlocks
        (Matrix.of (fun i ↦ ((IsZLattice.basis (kernelLattice L) i : kernelLattice L) : I → ℝ)))
        0
        (Matrix.of (fun j i ↦ (imageSection L (IsZLattice.basis (imageLattice L) j)).val (Sum.inl i)))
        (Matrix.of (fun j ↦ ((IsZLattice.basis (imageLattice L) j : imageLattice L) : J → ℝ))) := by
  ext (i | j) (i' | j')
  · simp [latticeSplitBasis, Basis.prod_apply, kernelInclusion, leftEmbed]
  · simp [latticeSplitBasis, Basis.prod_apply, kernelInclusion, leftEmbed]
  · simp [latticeSplitBasis, Basis.prod_apply, kernelInclusion, leftEmbed]
  · have h := congrArg (fun y : imageLattice L ↦ y.val j')
      (imageProjection_imageSection L (IsZLattice.basis (imageLattice L) j))
    simpa [latticeSplitBasis, Basis.prod_apply, kernelInclusion, leftEmbed,
      imageProjection, rightProj] using h

/-- Covolumes multiply in an exact coordinate-projection lattice sequence.
All three covolumes are ordinary Lebesgue covolumes of independently defined
lattices, including in zero-dimensional coordinate blocks. -/
theorem covolume_eq_kernel_mul_image :
    ZLattice.covolume L =
      ZLattice.covolume (kernelLattice L) * ZLattice.covolume (imageLattice L) := by
  rw [ZLattice.covolume_eq_det L (latticeSplitBasis L),
    ZLattice.covolume_eq_det (kernelLattice L) (IsZLattice.basis (kernelLattice L)),
    ZLattice.covolume_eq_det (imageLattice L) (IsZLattice.basis (imageLattice L))]
  change |(Matrix.of (fun i ↦ ((latticeSplitBasis L i : L) : I ⊕ J → ℝ))).det| = _
  rw [latticeSplitBasis_matrix, Matrix.det_fromBlocks_zero₁₂, abs_mul]
  rfl

end UnitDistance.LatticeExactSequence
