module

public import UnitDistance.SIntegerFundamentalDomain

@[expose] public section
set_option backward.privateInPublic true


/-!
# The actual diagonal S-integers project injectively to the Euclidean plane

The real base place supplies a compact complex embedding. Its restriction
to actual S-integers sends every relative-norm-one displacement to an ordinary
Euclidean unit vector, even when the field element is nonintegral.
-/

noncomputable section
open NumberField NumberField.InfinitePlace IsDedekindDomain
open scoped Classical nonZeroDivisors
namespace UnitDistance.SIntegerCRT

variable {K : Type} [Field K] [NumberField K] {T : Type*} [Fintype T]

def diagonalEmbeddingEquiv (P : T → HeightOneSpectrum (𝓞 K)) :
    (Set.range P).integer K ≃+ diagonalSIntegers P :=
  AddEquiv.ofBijective (diagonalEmbedding P).rangeRestrict (by
    constructor
    · intro x y h
      exact diagonalEmbedding_injective P (congrArg Subtype.val h)
    · rintro ⟨x, y, hy⟩
      exact ⟨y, Subtype.ext hy⟩)

@[simp] theorem diagonalEmbeddingEquiv_coe (P : T → HeightOneSpectrum (𝓞 K))
    (x : (Set.range P).integer K) :
    (diagonalEmbeddingEquiv P x : EuclideanIdeal.Space K × LocalProduct P) =
      diagonalEmbedding P x := rfl

def sIntegerPlaneProjection (P : T → HeightOneSpectrum (𝓞 K)) (σ : K →+* ℂ) :
    diagonalSIntegers P →+ ℂ :=
  (σ.comp ((Set.range P).integer K).subtype).toAddMonoidHom.comp
    (diagonalEmbeddingEquiv P).symm.toAddMonoidHom

theorem sIntegerPlaneProjection_injective (P : T → HeightOneSpectrum (𝓞 K))
    (σ : K →+* ℂ) : Function.Injective (sIntegerPlaneProjection P σ) := by
  intro x y h
  apply (diagonalEmbeddingEquiv P).symm.injective
  apply Subtype.ext
  exact σ.injective h

@[simp] theorem sIntegerPlaneProjection_embedding (P : T → HeightOneSpectrum (𝓞 K))
    (σ : K →+* ℂ) (x : (Set.range P).integer K) :
    sIntegerPlaneProjection P σ (diagonalEmbeddingEquiv P x) = σ (x : K) := by
  change σ (((diagonalEmbeddingEquiv P).symm (diagonalEmbeddingEquiv P x) :
    (Set.range P).integer K) : K) = σ (x : K)
  rw [AddEquiv.symm_apply_apply]

end UnitDistance.SIntegerCRT

namespace UnitDistance.RelativeUnits
open SIntegerCRT

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K] [IsTotallyComplex K]
  {T : Type*} [Fintype T]

theorem exists_sIntegerPlaneProjection (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (hb : 0 < nrRealPlaces F) (P : T → HeightOneSpectrum (𝓞 K)) :
    ∃ φ : diagonalSIntegers P →+ ℂ, Function.Injective φ ∧
      ∀ x : (Set.range P).integer K, Algebra.norm F (x : K) = 1 →
        ‖φ (diagonalEmbeddingEquiv P x)‖ = 1 := by
  obtain ⟨ρ, σ, hbase, hconj⟩ := exists_complexifying_embeddings ι hι hb
  refine ⟨sIntegerPlaneProjection P σ, sIntegerPlaneProjection_injective P σ, ?_⟩
  intro x hn
  rw [sIntegerPlaneProjection_embedding]
  apply complex_norm_of_relative_norm_one σ ι.toRingHom hconj
  change (x : K)*ι (x : K) = 1
  rw [← norm_eq_mul_involution ι hι, hn, map_one]

end UnitDistance.RelativeUnits
