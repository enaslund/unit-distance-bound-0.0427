module

public import UnitDistance.GaloisEmbeddingRestriction
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings

@[expose] public section
set_option backward.privateInPublic true


/-! Complex conjugation descends through an actual embedded finite Galois field. -/
noncomputable section
namespace UnitDistance.GaloisEmbedding
open NumberField.ComplexEmbedding
variable {F K Ω : Type*} [Field F] [Field K] [Field Ω]
  [Algebra F K] [Algebra F Ω] [Module.Finite F K] [IsGalois F K]

theorem restriction_isConj (f : K →ₐ[F] Ω) (φ : Ω →+* ℂ) (c : Gal(Ω/F))
    (hc : IsConj φ c) : IsConj (φ.comp f.toRingHom) (restriction f c) := by
  ext x
  change star (φ (f x)) = φ (f (restriction f c x))
  rw [restriction_commutes, hc.eq]

end UnitDistance.GaloisEmbedding
