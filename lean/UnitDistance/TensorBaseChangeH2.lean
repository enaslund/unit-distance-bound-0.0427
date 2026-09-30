module

public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Adele.RestrictedAction
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.TateComparison
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

@[expose] public section
set_option backward.privateInPublic true


/-! Actual coefficient maps for local tensor base change. These support
zero-detection after restricting a global cocycle to an intermediate field. -/
noncomputable section
open CategoryTheory
open scoped TensorProduct
namespace UnitDistance.ArithmeticProP

variable (K F L A B : Type) [Field K] [Field F] [Field L]
variable [Algebra K F] [Algebra F L] [Algebra K L] [IsScalarTower K F L]
variable [CommRing A] [Algebra K A]
variable [CommRing B] [Algebra F B] [Algebra K B] [IsScalarTower K F B]

/-- Change the coefficient completion and the base of the local tensor
product along the actual algebra homomorphism `f`. -/
def localTensorBaseChange (f : A →ₐ[K] B) : A ⊗[K] L →ₐ[K] B ⊗[F] L :=
  Algebra.TensorProduct.lift
    (((Algebra.TensorProduct.includeLeft : B →ₐ[F] B ⊗[F] L).restrictScalars K).comp f)
    ((Algebra.TensorProduct.includeRight : L →ₐ[F] B ⊗[F] L).restrictScalars K)
    (fun _ _ => Commute.all _ _)

@[simp] theorem localTensorBaseChange_tmul (f : A →ₐ[K] B) (a : A) (x : L) :
    localTensorBaseChange K F L A B f (a ⊗ₜ[K] x) = f a ⊗ₜ[F] x := by
  simp [localTensorBaseChange,Algebra.TensorProduct.lift_tmul,
    Algebra.TensorProduct.includeLeft,Algebra.TensorProduct.includeRight,
    Algebra.TensorProduct.tmul_mul_tmul]

/-- Tensor coefficient base change intertwines the actual automorphism
restriction and tensor actions. -/
theorem localTensorBaseChange_conjugation (f : A →ₐ[K] B)
    (σ : L ≃ₐ[F] L) (z : A ⊗[K] L) :
    localTensorBaseChange K F L A B f
      (scalarTensorConjugation (K := K) (L := L) (A := A) (σ.restrictScalars K) z) =
    scalarTensorConjugation (K := F) (L := L) (A := B) σ
      (localTensorBaseChange K F L A B f z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp
  | add x y hx hy => simp [hx,hy]

local instance sourceTensorAction : MulDistribMulAction Gal(L/K) (A ⊗[K] L)ˣ :=
  scalarTensorUnitsAction (K := K) (L := L) (A := A)
local instance targetTensorAction : MulDistribMulAction Gal(L/F) (B ⊗[F] L)ˣ :=
  scalarTensorUnitsAction (K := F) (L := L) (A := B)

/-- The actual equivariant coefficient morphism on local tensor units. -/
def localTensorBaseChangeRepHom (f : A →ₐ[K] B) :
    Rep.res (AlgEquiv.restrictScalarsHom K)
      (Rep.ofMulDistribMulAction Gal(L/K) (A ⊗[K] L)ˣ) ⟶
    Rep.ofMulDistribMulAction Gal(L/F) (B ⊗[F] L)ˣ := by
  apply Rep.ofHom
  refine ⟨(Units.map (localTensorBaseChange K F L A B f).toMonoidHom).toAdditive.toIntLinearMap,?_⟩
  intro σ
  apply LinearMap.ext
  intro z
  apply Units.ext
  exact localTensorBaseChange_conjugation K F L A B f σ ((show Additive (A ⊗[K] L)ˣ from z).toMul : A ⊗[K] L)

/-- Restriction/base change on the actual local tensor H² groups. -/
def localTensorBaseChangeH2 (f : A →ₐ[K] B) :
    groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) (A ⊗[K] L)ˣ) 2 ⟶
    groupCohomology (Rep.ofMulDistribMulAction Gal(L/F) (B ⊗[F] L)ˣ) 2 :=
  groupCohomology.map (AlgEquiv.restrictScalarsHom K)
    (localTensorBaseChangeRepHom K F L A B f) 2

/-- Actual field units embed as the right factor of the local tensor algebra. -/
def fieldUnitsTensorRepHom : Rep.ofAlgebraAutOnUnits K L ⟶
    Rep.ofMulDistribMulAction Gal(L/K) (A ⊗[K] L)ˣ := by
  apply Rep.ofHom
  refine ⟨(Units.map (Algebra.TensorProduct.includeRight :
    L →ₐ[K] A ⊗[K] L).toMonoidHom).toAdditive.toIntLinearMap,?_⟩
  intro σ
  apply LinearMap.ext
  intro z
  apply Units.ext
  rfl

/-- Actual tensor localization on field-unit H². -/
def fieldUnitsTensorH2 :
    groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 ⟶
    groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) (A ⊗[K] L)ˣ) 2 :=
  groupCohomology.map (MonoidHom.id Gal(L/K)) (fieldUnitsTensorRepHom K L A) 2

/-- Restriction on field units does not change their values. -/
def fieldUnitsRestrictionRepHom :
    Rep.res (AlgEquiv.restrictScalarsHom K) (Rep.ofAlgebraAutOnUnits K L) ⟶
    Rep.ofAlgebraAutOnUnits F L :=
  Rep.ofHom ⟨LinearMap.id,fun _ => rfl⟩

def fieldUnitsRestrictionH2 :
    groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 ⟶
    groupCohomology (Rep.ofAlgebraAutOnUnits F L) 2 :=
  groupCohomology.map (AlgEquiv.restrictScalarsHom K)
    (fieldUnitsRestrictionRepHom K F L) 2

/-- The actual restriction/localization square commutes before any Shapiro
or norm-quotient identifications are chosen. -/
theorem fieldUnitsTensorH2_baseChange (f : A →ₐ[K] B) :
    fieldUnitsTensorH2 K L A ≫ localTensorBaseChangeH2 K F L A B f =
      fieldUnitsRestrictionH2 K F L ≫ fieldUnitsTensorH2 F L B := by
  unfold fieldUnitsTensorH2 localTensorBaseChangeH2 fieldUnitsRestrictionH2
  rw [← groupCohomology.map_comp,← groupCohomology.map_comp]
  apply groupCohomology.map_congr
  · ext σ x
    rfl
  · apply LinearMap.ext
    intro z
    apply Units.ext
    change localTensorBaseChange K F L A B f
      (1 ⊗ₜ[K] ((show Additive Lˣ from z).toMul : L)) =
      1 ⊗ₜ[F] ((show Additive Lˣ from z).toMul : L)
    simp

/-- A locally trivial field-unit class stays locally trivial after base
change and restriction, using the actual tensor coefficient map. -/
theorem fieldUnitsTensorRestriction_eq_zero_of_eq_zero (f : A →ₐ[K] B)
    (x : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2)
    (hx : (fieldUnitsTensorH2 K L A).hom x = 0) :
    (fieldUnitsTensorH2 F L B).hom ((fieldUnitsRestrictionH2 K F L).hom x) = 0 := by
  have h := congrArg (fun m => m.hom x) (fieldUnitsTensorH2_baseChange K F L A B f)
  change (localTensorBaseChangeH2 K F L A B f).hom ((fieldUnitsTensorH2 K L A).hom x) =
    (fieldUnitsTensorH2 F L B).hom ((fieldUnitsRestrictionH2 K F L).hom x) at h
  rw [hx,map_zero] at h
  exact h.symm

end UnitDistance.ArithmeticProP
