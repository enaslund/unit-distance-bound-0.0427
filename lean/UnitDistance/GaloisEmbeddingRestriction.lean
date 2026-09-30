module

public import Mathlib.FieldTheory.Galois.Profinite

@[expose] public section
set_option backward.privateInPublic true


/-! Actual continuous Galois restriction along a specified field embedding. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.GaloisEmbedding

variable {F K Ω : Type*} [Field F] [Field K] [Field Ω]
  [Algebra F K] [Algebra F Ω] [Module.Finite F K] [IsGalois F K]

private instance rangeFinite (f : K →ₐ[F] Ω) : Module.Finite F f.fieldRange :=
  f.equivFieldRange.toLinearEquiv.finiteDimensional

private instance rangeGalois (f : K →ₐ[F] Ω) : IsGalois F f.fieldRange :=
  IsGalois.of_algEquiv f.equivFieldRange

/-- Restrict an actual ambient automorphism to the specified finite Galois
embedded field, and transport it back to the original field. -/
def restriction (f : K →ₐ[F] Ω) : Gal(Ω/F) →ₜ* Gal(K/F) where
  toMonoidHom := (AlgEquiv.autCongr f.equivFieldRange.symm).toMonoidHom.comp
    (AlgEquiv.restrictNormalHom (F := F) (K₁ := Ω) f.fieldRange)
  continuous_toFun :=
    (continuous_of_discreteTopology : Continuous
      (AlgEquiv.autCongr f.equivFieldRange.symm)).comp
      (InfiniteGalois.restrictNormalHom_continuous f.fieldRange)

/-- Restriction is characterized by its actual action under the embedding. -/
theorem restriction_commutes (f : K →ₐ[F] Ω) (σ : Gal(Ω/F)) (x : K) :
    f (restriction f σ x) = σ (f x) := by
  change (f.equivFieldRange
    (f.equivFieldRange.symm ((σ.restrictNormal f.fieldRange) (f.equivFieldRange x))) : Ω) = _
  rw [f.equivFieldRange.apply_symm_apply]
  exact AlgEquiv.restrictNormal_commutes σ f.fieldRange (f.equivFieldRange x)

theorem restriction_surjective [IsGalois F Ω] (f : K →ₐ[F] Ω) :
    Function.Surjective (restriction f) :=
  (AlgEquiv.autCongr f.equivFieldRange.symm).surjective.comp
    (AlgEquiv.restrictNormalHom_surjective Ω)

theorem restriction_unique (f : K →ₐ[F] Ω) (σ : Gal(Ω/F)) (τ : Gal(K/F))
    (h : ∀ x, f (τ x) = σ (f x)) : restriction f σ = τ := by
  ext x
  apply f.injective
  exact (restriction_commutes f σ x).trans (h x).symm

omit [Module.Finite F K] in
/-- Two embeddings of a normal field differ by an actual automorphism of it. -/
theorem exists_embedding_change (f g : K →ₐ[F] Ω) :
    ∃ a : Gal(K/F), ∀ x, f (a x) = g x := by
  letI : Algebra K Ω := f.toRingHom.toAlgebra
  letI : IsScalarTower F K Ω := IsScalarTower.of_algebraMap_eq fun x ↦ (f.commutes x).symm
  refine ⟨g.restrictNormal' K, ?_⟩
  intro x
  exact g.restrictNormal_commutes K x

/-- Restriction to an abelian normal field is independent of its chosen
embedding. This is an actual equality of field automorphisms. -/
theorem restriction_independent [IsMulCommutative Gal(K/F)]
    (f g : K →ₐ[F] Ω) (σ : Gal(Ω/F)) : restriction f σ = restriction g σ := by
  obtain ⟨a, ha⟩ := exists_embedding_change f g
  symm
  apply restriction_unique
  intro x
  rw [← ha (restriction f σ x)]
  have hc : a (restriction f σ x) = restriction f σ (a x) :=
    congrArg (fun b : Gal(K/F) ↦ b x) (mul_comm' a (restriction f σ))
  rw [hc, restriction_commutes, ha]

/-- The embedding-based definition agrees with ordinary restriction to a
literal intermediate field followed by an actual field isomorphism. -/
theorem restriction_subfield (L : IntermediateField F Ω)
    [Module.Finite F L] [IsGalois F L] (e : L ≃ₐ[F] K) (σ : Gal(Ω/F)) :
    restriction (L.val.comp e.symm.toAlgHom) σ =
      AlgEquiv.autCongr e (σ.restrictNormal L) := by
  apply restriction_unique
  intro x
  change (e.symm (e ((σ.restrictNormal L) (e.symm x))) : Ω) = σ (e.symm x : Ω)
  rw [e.symm_apply_apply]
  exact AlgEquiv.restrictNormal_commutes σ L (e.symm x)

variable {E : Type*} [Field E] [Algebra F E] [Module.Finite F E] [IsGalois F E]

theorem restriction_comp (f : K →ₐ[F] Ω) (g : E →ₐ[F] K) (σ : Gal(Ω/F)) :
    restriction (f.comp g) σ = restriction g (restriction f σ) := by
  apply restriction_unique
  intro x
  simp only [AlgHom.comp_apply, restriction_commutes]

end UnitDistance.GaloisEmbedding
