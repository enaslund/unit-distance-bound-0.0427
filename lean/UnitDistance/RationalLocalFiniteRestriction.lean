module

public import UnitDistance.RationalLocalAbsoluteEmbedding
public import UnitDistance.FiniteAbsoluteInertiaImage

@[expose] public section
set_option backward.privateInPublic true


/-! Exact finite restriction through the chosen rational local decomposition map. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.GaloisEmbedding
variable {F M Ω : Type*} [Field F] [Field M] [Field Ω]
  [Algebra F M] [Algebra F Ω] [Module.Finite F M] [IsGalois F M]

theorem restriction_eq_one_of_embedding_change (f g : M →ₐ[F] Ω)
    (σ : Gal(Ω/F)) (hσ : restriction f σ=1) : restriction g σ=1 := by
  obtain ⟨a,ha⟩ := exists_embedding_change f g
  apply restriction_unique
  intro x
  change g x=σ (g x)
  rw [←ha,←restriction_commutes,hσ]
  rfl

theorem restriction_eq_one_iff (f g : M →ₐ[F] Ω) (σ : Gal(Ω/F)) :
    restriction f σ=1 ↔ restriction g σ=1 :=
  ⟨restriction_eq_one_of_embedding_change f g σ,
    restriction_eq_one_of_embedding_change g f σ⟩

end UnitDistance.GaloisEmbedding
namespace UnitDistance.PrimeCompletion
open ArithmeticProP
attribute [local instance] primeFact baseRationalAlgebra

variable (p : Nat.Primes) (M : Type) [Field M] [NumberField M] [IsGalois ℚ M]
  (j : M →ₐ[ℚ] AlgebraicClosure ℚ)

def decompositionRestriction : AbsoluteDecomposition p →* Gal(M/ℚ) :=
  (GaloisEmbedding.restriction j).toMonoidHom.comp (AbsoluteDecomposition p).subtype

def localRestriction : Gal(SeparableClosure (Base p)/Base p) →* Gal(M/ℚ) :=
  (GaloisEmbedding.restriction ((absoluteEmbedding p).comp j)).toMonoidHom.comp
    (AlgEquiv.restrictScalarsHom ℚ)

/-- The actual local-global comparison commutes with every finite rational restriction. -/
theorem localRestriction_decomposition (σ : AbsoluteDecomposition p) :
    localRestriction p M j (decompositionEquiv p σ)=decompositionRestriction p M j σ := by
  apply GaloisEmbedding.restriction_unique
  intro x
  change absoluteEmbedding p (j (GaloisEmbedding.restriction j σ.val x))=
    decompositionEquiv p σ (absoluteEmbedding p (j x))
  rw [GaloisEmbedding.restriction_commutes,decomposition_commutes]

/-- A finite local embedding can be used to test whether the corresponding
actual global decomposition element fixes the finite rational field. -/
theorem decompositionRestriction_eq_one_iff
    (f : M →ₐ[ℚ] SeparableClosure (Base p)) (σ : AbsoluteDecomposition p) :
    decompositionRestriction p M j σ=1 ↔
      GaloisEmbedding.restriction f ((decompositionEquiv p σ).restrictScalars ℚ)=1 := by
  rw [←localRestriction_decomposition]
  exact GaloisEmbedding.restriction_eq_one_iff ((absoluteEmbedding p).comp j) f _

end UnitDistance.PrimeCompletion
