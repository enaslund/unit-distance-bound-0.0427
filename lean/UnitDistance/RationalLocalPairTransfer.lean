module

public import UnitDistance.RationalLocalFiniteRestriction

@[expose] public section
set_option backward.privateInPublic true


/-! Transfer of finite local tame pairs to the actual chosen rational absolute
inertia/decomposition groups, including independently embedded abelian labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
namespace UnitDistance.PrimeCompletion
open ArithmeticProP LocalClassFieldTheory
attribute [local instance] primeFact baseRationalAlgebra

variable (p : Nat.Primes) (M : Type) [Field M] [NumberField M] [IsGalois ℚ M]
  (j : M →ₐ[ℚ] AlgebraicClosure ℚ)
  (A : Type) [Field A] [NumberField A] [IsGalois ℚ A] [IsMulCommutative Gal(A/ℚ)]
  (g : A →ₐ[ℚ] M)

theorem decomposition_label_independent
    (f : M →ₐ[ℚ] SeparableClosure (Base p)) (σ : AbsoluteDecomposition p) :
    GaloisEmbedding.restriction g (decompositionRestriction p M j σ)=
      GaloisEmbedding.restriction g
        (GaloisEmbedding.restriction f ((decompositionEquiv p σ).restrictScalars ℚ)) := by
  rw [←localRestriction_decomposition]
  change GaloisEmbedding.restriction g
    (GaloisEmbedding.restriction ((absoluteEmbedding p).comp j)
      ((decompositionEquiv p σ).restrictScalars ℚ))=_
  rw [←GaloisEmbedding.restriction_comp,←GaloisEmbedding.restriction_comp]
  exact GaloisEmbedding.restriction_independent _ _ _

/-- A locally lifted finite tame pair produces actual chosen absolute inertia
and decomposition elements with the prescribed abelian labels and relation. -/
theorem exists_absolute_pair_of_local_pair
    (f : M →ₐ[ℚ] SeparableClosure (Base p))
    (τ φ : Gal(SeparableClosure (Base p)/Base p))
    (hτ : τ∈(localResidueDegree (Base p)).toMonoidHom.ker)
    (a b : Gal(A/ℚ)) (q : ℕ)
    (ha : GaloisEmbedding.restriction g
      (GaloisEmbedding.restriction f (τ.restrictScalars ℚ))=a)
    (hb : GaloisEmbedding.restriction g
      (GaloisEmbedding.restriction f (φ.restrictScalars ℚ))=b)
    (hrel :
      let r : Gal(SeparableClosure (Base p)/Base p) →* Gal(M/ℚ) :=
        (GaloisEmbedding.restriction f).toMonoidHom.comp
          (AlgEquiv.restrictScalarsHom ℚ)
      r φ*r τ*(r φ)⁻¹=(r τ)^q) :
    ∃t : AbsoluteInertia p, ∃s : AbsoluteDecomposition p,
      GaloisEmbedding.restriction g (decompositionRestriction p M j t.val)=a ∧
      GaloisEmbedding.restriction g (decompositionRestriction p M j s)=b ∧
      decompositionRestriction p M j (s*t.val*s⁻¹*(t.val^q)⁻¹)=1 := by
  let t := (decompositionEquiv p).symm τ
  let s := (decompositionEquiv p).symm φ
  have ht : t∈AbsoluteInertia p := by
    rw [←decomposition_mem_inertia_iff]
    simpa only [t,ContinuousMulEquiv.apply_symm_apply] using hτ
  refine ⟨⟨t,ht⟩,s,?_,?_,?_⟩
  · rw [decomposition_label_independent p M j A g f]
    simpa only [t,ContinuousMulEquiv.apply_symm_apply] using ha
  · rw [decomposition_label_independent p M j A g f]
    simpa only [s,ContinuousMulEquiv.apply_symm_apply] using hb
  · apply (decompositionRestriction_eq_one_iff p M j f _).mpr
    let r : Gal(SeparableClosure (Base p)/Base p) →* Gal(M/ℚ) := (GaloisEmbedding.restriction f).toMonoidHom.comp
      (AlgEquiv.restrictScalarsHom ℚ)
    change r (decompositionEquiv p (s*t*s⁻¹*(t^q)⁻¹))=1
    simp only [map_mul,map_inv,map_pow,s,t,ContinuousMulEquiv.apply_symm_apply]
    exact mul_inv_eq_one.mpr hrel

end UnitDistance.PrimeCompletion
