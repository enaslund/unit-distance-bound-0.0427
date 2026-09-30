module

public import UnitDistance.PadicTwoMaximalProTwo
public import UnitDistance.GaloisEmbeddingRestriction
public import UnitDistance.PadicTwoQuadraticAction

@[expose] public section
set_option backward.privateInPublic true


/-! Actual finite Galois restrictions of the maximal pro-two Q₂ group. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.PadicTwoMaximalProTwo
open ProCGroups ProCGroups.ProC ClassFieldTower.ProP
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

section FiniteRestriction
variable {M : Type} [Field M] [Algebra ℚ_[2] M] [Module.Finite ℚ_[2] M] [IsGalois ℚ_[2] M]

omit [IsGalois ℚ_[2] M] in
theorem finiteGalois_proTwo (hM : IsPGroup 2 Gal(M/ℚ_[2])) :
    HasPGroupOpenNormalBasis 2 Gal(M/ℚ_[2]) :=
  HasOpenNormalBasisInClass.of_finite_discrete (FiniteGroupClass.pGroup_formation 2).quotientClosed
    ⟨inferInstance,hM⟩

/-- Restriction to any actual finite Galois two-extension, through a specified embedding. -/
def finiteRestriction (hM : IsPGroup 2 Gal(M/ℚ_[2])) (f : M →ₐ[ℚ_[2]] Closure) :
    Group →ₜ* Gal(M/ℚ_[2]) :=
  lift_proCResidualCoreQuotient (FiniteGroupClass.pGroup_hereditary 2)
    (GaloisEmbedding.restriction f) (finiteGalois_proTwo hM)

@[simp] theorem finiteRestriction_projection (hM : IsPGroup 2 Gal(M/ℚ_[2]))
    (f : M →ₐ[ℚ_[2]] Closure) (σ : AbsoluteGroup) :
    finiteRestriction hM f (projection σ)=GaloisEmbedding.restriction f σ := rfl

theorem finiteRestriction_surjective (hM : IsPGroup 2 Gal(M/ℚ_[2]))
    (f : M →ₐ[ℚ_[2]] Closure) : Function.Surjective (finiteRestriction hM f) := by
  intro τ
  obtain ⟨σ,hσ⟩ := GaloisEmbedding.restriction_surjective f τ
  exact ⟨projection σ,hσ⟩

/-- The quotient restriction acts through the actual specified field embedding. -/
theorem finiteRestriction_commutes (hM : IsPGroup 2 Gal(M/ℚ_[2]))
    (f : M →ₐ[ℚ_[2]] Closure) (σ : AbsoluteGroup) (x : M) :
    f (finiteRestriction hM f (projection σ) x)=σ (f x) :=
  GaloisEmbedding.restriction_commutes f σ x

private local instance genusAutCommutative : IsMulCommutative Gal(PadicTwoGenus.GenusField/ℚ_[2]) :=
  IsMulCommutative.of_comm fun σ τ ↦ PadicTwoGenus.signEquiv.injective (by
    rw [map_mul,map_mul,mul_comm])

variable [Algebra PadicTwoGenus.GenusField M] [IsScalarTower ℚ_[2] PadicTwoGenus.GenusField M]

/-- Actual genus signs agree for every chosen embedding of a finite extension
containing the genus field. No compatibility of embeddings is assumed. -/
theorem finiteRestriction_genus (hM : IsPGroup 2 Gal(M/ℚ_[2]))
    (f : M →ₐ[ℚ_[2]] Closure) (g : Group) :
    PadicTwoGenus.signEquiv ((finiteRestriction hM f g).restrictNormal PadicTwoGenus.GenusField)=
      signs g := by
  obtain ⟨σ,rfl⟩ := projection_surjective g
  rw [finiteRestriction_projection,signs_projection]
  change PadicTwoGenus.signEquiv ((GaloisEmbedding.restriction f σ).restrictNormal PadicTwoGenus.GenusField)=
    PadicTwoGenus.signEquiv (GaloisEmbedding.restriction genusEmbedding σ)
  congr 1
  let b := IsScalarTower.toAlgHom ℚ_[2] PadicTwoGenus.GenusField M
  have h := GaloisEmbedding.restriction_independent (f.comp b) genusEmbedding σ
  rw [GaloisEmbedding.restriction_comp] at h
  have hb : GaloisEmbedding.restriction b (GaloisEmbedding.restriction f σ)=
      (GaloisEmbedding.restriction f σ).restrictNormal PadicTwoGenus.GenusField := by
    apply GaloisEmbedding.restriction_unique
    intro x
    exact AlgEquiv.restrictNormal_commutes (GaloisEmbedding.restriction f σ) PadicTwoGenus.GenusField x
  exact hb.symm.trans h

end FiniteRestriction

/-- A fixed actual embedding of the constructed degree-256 field. -/
def quadraticEmbedding : PadicTwoQuadratic.QuadraticField →ₐ[ℚ_[2]] Closure := IsAlgClosed.lift

/-- The actual degree-256 Galois quotient of the maximal local pro-two group. -/
def quadraticRestriction : Group →ₜ* PadicTwoQuadratic.G :=
  finiteRestriction PadicTwoQuadratic.isPGroup quadraticEmbedding

theorem quadraticRestriction_surjective : Function.Surjective quadraticRestriction :=
  finiteRestriction_surjective PadicTwoQuadratic.isPGroup quadraticEmbedding

theorem quadraticRestriction_genusVector (g : Group) :
    PadicTwoQuadratic.genusVector (quadraticRestriction g)=(signs g).toAdd :=
  congrArg Multiplicative.toAdd (finiteRestriction_genus PadicTwoQuadratic.isPGroup quadraticEmbedding g)

@[simp] theorem quadraticRestriction_generator_genusVector (i : Fin 3) :
    PadicTwoQuadratic.genusVector (quadraticRestriction (generator i))=Pi.single i 1 := by
  rw [quadraticRestriction_genusVector,generator_signs]
  rfl

end UnitDistance.PadicTwoMaximalProTwo
