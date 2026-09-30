module

public import UnitDistance.TensorBaseChangeH2
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.GaloisNorm
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic

@[expose] public section
set_option backward.privateInPublic true


/-! The norm in the actual tensor-unit representation is the actual
determinant norm of the local tensor algebra. -/
noncomputable section
open CategoryTheory
open scoped TensorProduct BigOperators
namespace UnitDistance.ArithmeticProP

variable (K L A : Type) [Field K] [Field L] [Algebra K L]
variable [FiniteDimensional K L] [IsGalois K L] [Infinite K]
variable [CommRing A] [Algebra K A] [Nontrivial A]

local instance tensorNormAction : MulDistribMulAction Gal(L/K) (A ⊗[K] L)ˣ :=
  scalarTensorUnitsAction (K := K) (L := L) (A := A)

/-- The two tensor action presentations are the same actual ring map. -/
theorem scalarTensorConjugation_eq_scalarConjugation (σ : Gal(L/K)) (z : A ⊗[K] L) :
    scalarTensorConjugation (K := K) (L := L) (A := A) σ z =
      RelativeIdeleGroup.scalarConjugation A σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp [hx,hy]

/-- The representation norm on tensor units is the actual determinant norm,
followed by inclusion of the coefficient algebra. -/
theorem tensorUnits_rep_norm (u : (A ⊗[K] L)ˣ) :
    (Rep.ofMulDistribMulAction Gal(L/K) (A ⊗[K] L)ˣ).norm.hom (Additive.ofMul u) =
      Additive.ofMul (Units.map
        (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] L).toMonoidHom
        (Units.map (Algebra.norm A : (A ⊗[K] L) →* A) u)) := by
  apply Additive.toMul.injective
  unfold Rep.ofMulDistribMulAction
  change Additive.toMul
      ((Representation.ofMulDistribMulAction Gal(L/K) (A ⊗[K] L)ˣ).norm
        (Additive.ofMul u)) = _
  rw [Representation.norm_ofMulDistribMulAction_eq]
  apply Units.ext
  change (↑(∏ σ : Gal(L/K), σ • u) : A ⊗[K] L) =
    (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] L)
      (Algebra.norm A (u : A ⊗[K] L))
  rw [Units.coe_prod]
  simp only [scalarTensorUnitsAction_coe,scalarTensorConjugation_eq_scalarConjugation]
  exact (RelativeIdeleGroup.includeLeft_norm_eq_prod_scalarConjugations
    (K := K) (L := L) A (u : A ⊗[K] L)).symm

/-- A coefficient-algebra unit lies in the representation norm range exactly
when it is an actual determinant norm from the tensor algebra. -/
theorem tensorScalarUnit_mem_rep_norm_range_iff (b : Aˣ) :
    Additive.ofMul (Units.map
      (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] L).toMonoidHom b) ∈
      LinearMap.range (Rep.ofMulDistribMulAction Gal(L/K) (A ⊗[K] L)ˣ).norm.hom.toLinearMap ↔
    b ∈ (Units.map (Algebra.norm A : (A ⊗[K] L) →* A)).range := by
  constructor
  · rintro ⟨u,hu⟩
    refine ⟨(show Additive (A ⊗[K] L)ˣ from u).toMul,?_⟩
    apply Units.ext
    apply Algebra.TensorProduct.includeLeft_injective
      (R := K) (S := K) (A := A) (B := L) (algebraMap K L).injective
    have hn := (tensorUnits_rep_norm K L A
      (show Additive (A ⊗[K] L)ˣ from u).toMul).symm.trans hu
    exact congrArg (fun z : Additive (A ⊗[K] L)ˣ => (z.toMul : A ⊗[K] L)) hn
  · rintro ⟨u,rfl⟩
    exact ⟨Additive.ofMul u,tensorUnits_rep_norm K L A u⟩

section Cyclic
variable [IsCyclic Gal(L/K)]
local instance : CommGroup Gal(L/K) := IsCyclic.commGroup

/-- A unit of the coefficient algebra is fixed by every tensor automorphism. -/
def tensorScalarUnitFixed (g : Gal(L/K)) (b : Aˣ) :
    LinearMap.ker (Rep.applyAsHom
      (Rep.ofMulDistribMulAction Gal(L/K) (A ⊗[K] L)ˣ) g - 𝟙 _).hom.toLinearMap := by
  refine ⟨Additive.ofMul (Units.map
    (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] L).toMonoidHom b),?_⟩
  change Additive.ofMul (g • Units.map
    (Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] L).toMonoidHom b) - _ = 0
  apply sub_eq_zero.mpr
  apply Units.ext
  change scalarTensorConjugation (K := K) (L := L) (A := A) g
    ((b:A) ⊗ₜ[K] (1:L)) = (b:A) ⊗ₜ[K] (1:L)
  simp

/-- A cyclic local H² scalar class is zero precisely when its scalar is an
actual determinant norm from the local tensor algebra. -/
theorem tensorScalarUnitH2_eq_zero_iff_norm
    (g : Gal(L/K)) (hg : ∀ σ : Gal(L/K), σ ∈ Subgroup.zpowers g) (b : Aˣ) :
    Rep.FiniteCyclicGroup.groupCohomologyπEven
      (Rep.ofMulDistribMulAction Gal(L/K) (A ⊗[K] L)ˣ) g hg 2 (by decide)
      (tensorScalarUnitFixed K L A g b) = 0 ↔
    b ∈ (Units.map (Algebra.norm A : (A ⊗[K] L) →* A)).range := by
  rw [Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff]
  exact tensorScalarUnit_mem_rep_norm_range_iff K L A b

end Cyclic
end UnitDistance.ArithmeticProP
