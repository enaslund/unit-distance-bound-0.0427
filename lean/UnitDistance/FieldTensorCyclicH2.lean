module

public import UnitDistance.TensorUnitCohomologyNorm
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.FiniteCyclicH2CoefficientNorm
public import Mathlib.FieldTheory.Fixed
public import Mathlib.RepresentationTheory.Invariants

@[expose] public section
set_option backward.privateInPublic true


/-! Actual scalar representatives and their tensor localization in cyclic H².
The fixed-value descent argument is adapted from `FiniteCyclicBaseUnitsH2`
at Yamaguchi/Sawin commit 3a455e1aa9140dbbe7b7d68f508392a69c86d0f4
(Apache-2.0); the tensor compatibility and norm detection below are new. -/
noncomputable section
open CategoryTheory
open scoped TensorProduct BigOperators
open ClassFieldTower.Cohomology
namespace UnitDistance.ArithmeticProP

/-- Periodic representatives commute with actual coefficient morphisms. -/
theorem cyclicH2_scalar_naturality
    {R G : Type} [CommRing R] [CommGroup G] [Fintype G]
    (A B : Rep R G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (φ : A ⟶ B)
    (a : LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap)
    (b : LinearMap.ker (Rep.applyAsHom B g - 𝟙 B).hom.toLinearMap)
    (hab : φ.hom a.1 = b.1) :
    groupCohomology.map (MonoidHom.id G) φ 2
      (Rep.FiniteCyclicGroup.groupCohomologyπEven A g hg 2 (by decide) a) =
    Rep.FiniteCyclicGroup.groupCohomologyπEven B g hg 2 (by decide) b := by
  rw [← H2π_finiteCyclicCarryTwoCocycle,← H2π_finiteCyclicCarryTwoCocycle,
    groupCohomology.H2π_comp_map_apply]
  congr 1
  apply Subtype.ext
  funext xy
  change φ.hom (finiteCyclicCarry g hg xy.1 xy.2 • a.1) =
    finiteCyclicCarry g hg xy.1 xy.2 • b.1
  rw [map_nsmul,hab]

variable (K L : Type) [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
local instance : CommGroup Gal(L/K) := IsCyclic.commGroup

/-- A base-field unit gives an actual fixed coefficient in field-unit H². -/
def fieldScalarUnitFixed (g : Gal(L/K)) (b : Kˣ) :
    LinearMap.ker (Rep.applyAsHom (Rep.ofAlgebraAutOnUnits K L) g - 𝟙 _).hom.toLinearMap := by
  refine ⟨Additive.ofMul (Units.map (algebraMap K L).toMonoidHom b),?_⟩
  change Additive.ofMul (Units.map g.toRingEquiv.toMonoidHom
    (Units.map (algebraMap K L).toMonoidHom b)) - _ = 0
  apply sub_eq_zero.mpr
  apply Units.ext
  exact g.commutes (b : K)

/-- Every cyclic field-unit H² class has an actual base-field-unit scalar
representative, with the generator held fixed. -/
theorem exists_fieldScalarUnitH2
    (g : Gal(L/K)) (hg : ∀ x : Gal(L/K), x ∈ Subgroup.zpowers g)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) :
    ∃ b : Kˣ, Rep.FiniteCyclicGroup.groupCohomologyπEven
      (Rep.ofAlgebraAutOnUnits K L) g hg 2 (by decide) (fieldScalarUnitFixed K L g b) = x := by
  obtain ⟨a,ha⟩ := finiteCyclicGroupH2_piEven_surjective
    (Rep.ofAlgebraAutOnUnits K L) g hg x
  have hag : (Rep.ofAlgebraAutOnUnits K L).ρ g a.val = a.val := by
    have h := a.property
    change (Rep.ofAlgebraAutOnUnits K L).ρ g a.val - a.val = 0 at h
    exact sub_eq_zero.mp h
  have hfixed : ∀ σ : Gal(L/K), (Rep.ofAlgebraAutOnUnits K L).ρ σ a.val = a.val :=
    (Representation.mem_invariants_iff_of_forall_mem_zpowers
      (Rep.ofAlgebraAutOnUnits K L).ρ g hg a.val).mpr hag
  have hfix (σ : Gal(L/K)) :
      σ ((show Additive Lˣ from a.val).toMul : L) = ((show Additive Lˣ from a.val).toMul : L) :=
    congrArg Units.val (hfixed σ)
  obtain ⟨b,hb⟩ := (IsGalois.mem_range_algebraMap_iff_fixed
    (F := K) (E := L) ((show Additive Lˣ from a.val).toMul : L)).mpr hfix
  have hb0 : b ≠ 0 := by
    intro h
    apply Units.ne_zero (show Additive Lˣ from a.val).toMul
    rw [← hb,h,map_zero]
  refine ⟨Units.mk0 b hb0,?_⟩
  have hab : fieldScalarUnitFixed K L g (Units.mk0 b hb0) = a := by
    apply Subtype.ext
    apply Units.ext
    exact hb
  rw [hab]
  exact ha

/-- The field-unit representation norm is the actual field norm. -/
theorem fieldUnits_rep_norm (u : Lˣ) :
    (Rep.ofAlgebraAutOnUnits K L).norm.hom (Additive.ofMul u) =
      Additive.ofMul (Units.map (algebraMap K L).toMonoidHom
        (Units.map (Algebra.norm K : L →* K) u)) := by
  change (Rep.ofMulDistribMulAction Gal(L/K) Lˣ).norm.hom (Additive.ofMul u) = _
  apply Additive.toMul.injective
  unfold Rep.ofMulDistribMulAction
  change Additive.toMul
      ((Representation.ofMulDistribMulAction Gal(L/K) Lˣ).norm
        (Additive.ofMul u)) = _
  rw [Representation.norm_ofMulDistribMulAction_eq]
  apply Units.ext
  change (↑(∏ σ : Gal(L/K), σ • u) : L) = algebraMap K L (Algebra.norm K (u : L))
  rw [Units.coe_prod]
  exact (Algebra.norm_eq_prod_automorphisms K (u : L)).symm

/-- A scalar cyclic field-unit H² class vanishes precisely when its scalar
is an actual global field norm. -/
theorem fieldScalarUnitH2_eq_zero_iff_norm
    (g : Gal(L/K)) (hg : ∀ σ : Gal(L/K), σ ∈ Subgroup.zpowers g) (b : Kˣ) :
    Rep.FiniteCyclicGroup.groupCohomologyπEven
      (Rep.ofAlgebraAutOnUnits K L) g hg 2 (by decide)
      (fieldScalarUnitFixed K L g b) = 0 ↔
    b ∈ (Units.map (Algebra.norm K : L →* K)).range := by
  rw [Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff]
  constructor
  · rintro ⟨u,hu⟩
    refine ⟨(show Additive Lˣ from u).toMul,?_⟩
    apply Units.ext
    apply (algebraMap K L).injective
    have hn := (fieldUnits_rep_norm K L
      (show Additive Lˣ from u).toMul).symm.trans hu
    exact congrArg (fun z : Additive Lˣ => (z.toMul : L)) hn
  · rintro ⟨u,rfl⟩
    exact ⟨Additive.ofMul u,fieldUnits_rep_norm K L u⟩

variable (A : Type) [CommRing A] [Algebra K A]
local instance : MulDistribMulAction Gal(L/K) (A ⊗[K] L)ˣ :=
  scalarTensorUnitsAction (K := K) (L := L) (A := A)

/-- Tensor localization sends the same actual scalar representative to its
coefficient-algebra image. -/
theorem fieldScalarUnitH2_tensor
    (g : Gal(L/K)) (hg : ∀ σ : Gal(L/K), σ ∈ Subgroup.zpowers g) (b : Kˣ) :
    (fieldUnitsTensorH2 K L A).hom
      (Rep.FiniteCyclicGroup.groupCohomologyπEven
        (Rep.ofAlgebraAutOnUnits K L) g hg 2 (by decide) (fieldScalarUnitFixed K L g b)) =
    Rep.FiniteCyclicGroup.groupCohomologyπEven
      (Rep.ofMulDistribMulAction Gal(L/K) (A ⊗[K] L)ˣ) g hg 2 (by decide)
      (tensorScalarUnitFixed K L A g (Units.map (algebraMap K A).toMonoidHom b)) := by
  apply cyclicH2_scalar_naturality
  apply Units.ext
  change (1 : A) ⊗ₜ[K] algebraMap K L (b : K) = algebraMap K A (b : K) ⊗ₜ[K] (1 : L)
  exact (Algebra.TensorProduct.tmul_one_eq_one_tmul (R := K) (A := A) (B := L) (b : K)).symm

/-- Actual tensor localization of a cyclic scalar class is zero exactly when
the scalar is an actual determinant norm from the tensor algebra. -/
theorem fieldScalarUnitH2_tensor_eq_zero_iff_norm [Infinite K] [Nontrivial A]
    (g : Gal(L/K)) (hg : ∀ σ : Gal(L/K), σ ∈ Subgroup.zpowers g) (b : Kˣ) :
    (fieldUnitsTensorH2 K L A).hom
      (Rep.FiniteCyclicGroup.groupCohomologyπEven
        (Rep.ofAlgebraAutOnUnits K L) g hg 2 (by decide) (fieldScalarUnitFixed K L g b)) = 0 ↔
    Units.map (algebraMap K A).toMonoidHom b ∈
      (Units.map (Algebra.norm A : (A ⊗[K] L) →* A)).range := by
  rw [fieldScalarUnitH2_tensor]
  exact tensorScalarUnitH2_eq_zero_iff_norm K L A g hg _

end UnitDistance.ArithmeticProP
