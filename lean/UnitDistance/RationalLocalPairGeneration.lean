module

public import UnitDistance.RationalLocalPairTransfer
public import UnitDistance.HomKernelTransfer

@[expose] public section
set_option backward.privateInPublic true


/-! Transfer of finite local tame pairs to the actual chosen rational absolute
inertia/decomposition groups, including independently embedded abelian labels. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace UnitDistance.PrimeCompletion
open ArithmeticProP LocalClassFieldTheory
attribute [local instance] primeFact baseRationalAlgebra

variable (p : Nat.Primes) (M : Type) [Field M] [NumberField M] [IsGalois ℚ M]
  (j : M →ₐ[ℚ] AlgebraicClosure ℚ)
  (A : Type) [Field A] [NumberField A] [IsGalois ℚ A] [IsMulCommutative Gal(A/ℚ)]
  (g : A →ₐ[ℚ] M)

/-- A locally lifted finite tame pair produces actual chosen absolute inertia
and decomposition elements with the prescribed abelian labels and relation. -/
theorem exists_absolute_generating_pair_of_local_pair
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
      r φ*r τ*(r φ)⁻¹=(r τ)^q)
    (hIgen : ∀σ : Gal(SeparableClosure (Base p)/Base p),
      σ∈(localResidueDegree (Base p)).toMonoidHom.ker →
      ∃n : ℤ, GaloisEmbedding.restriction f (σ.restrictScalars ℚ)=
        (GaloisEmbedding.restriction f (τ.restrictScalars ℚ))^n)
    (hDgen : ∀σ : Gal(SeparableClosure (Base p)/Base p),
      GaloisEmbedding.restriction f (σ.restrictScalars ℚ)∈
        Subgroup.closure ({GaloisEmbedding.restriction f (τ.restrictScalars ℚ),
          GaloisEmbedding.restriction f (φ.restrictScalars ℚ)} : Set Gal(M/ℚ))) :
    ∃t : AbsoluteInertia p, ∃s : AbsoluteDecomposition p,
      GaloisEmbedding.restriction g (decompositionRestriction p M j t.val)=a ∧
      GaloisEmbedding.restriction g (decompositionRestriction p M j s)=b ∧
      decompositionRestriction p M j (s*t.val*s⁻¹*(t.val^q)⁻¹)=1 ∧
      (∀x : AbsoluteInertia p, ∃n : ℤ, decompositionRestriction p M j x.val=
        (decompositionRestriction p M j t.val)^n) ∧
      ∀y : AbsoluteDecomposition p, decompositionRestriction p M j y∈
        Subgroup.closure ({decompositionRestriction p M j t.val,
          decompositionRestriction p M j s} : Set Gal(M/ℚ)) := by
  let t := (decompositionEquiv p).symm τ
  let s := (decompositionEquiv p).symm φ
  have ht : t∈AbsoluteInertia p := by
    rw [←decomposition_mem_inertia_iff]
    simpa only [t,ContinuousMulEquiv.apply_symm_apply] using hτ
  let r : Gal(SeparableClosure (Base p)/Base p) →* Gal(M/ℚ) :=
    (GaloisEmbedding.restriction f).toMonoidHom.comp (AlgEquiv.restrictScalarsHom ℚ)
  let rj := localRestriction p M j
  have hker : r.ker≤rj.ker := by
    intro σ hσ
    exact GaloisEmbedding.restriction_eq_one_of_embedding_change f
      ((absoluteEmbedding p).comp j) (σ.restrictScalars ℚ) hσ
  have hτj : rj τ=decompositionRestriction p M j t := by
    have h := localRestriction_decomposition p M j t
    simpa only [t,ContinuousMulEquiv.apply_symm_apply] using h
  have hφj : rj φ=decompositionRestriction p M j s := by
    have h := localRestriction_decomposition p M j s
    simpa only [s,ContinuousMulEquiv.apply_symm_apply] using h
  refine ⟨⟨t,ht⟩,s,?_,?_,?_,?_,?_⟩
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
  · intro x
    obtain ⟨n,hn⟩ := hIgen (decompositionEquiv p x.val)
      ((decomposition_mem_inertia_iff p x.val).mpr x.property)
    refine ⟨n,?_⟩
    have hnR : r (decompositionEquiv p x.val)=(r τ)^n := hn
    have hg := HomKernelTransfer.eq_zpow_of_eq_zpow r rj hker
      (x:=decompositionEquiv p x.val) (t:=τ) (n:=n) hnR
    change rj (decompositionEquiv p x.val)=(rj τ)^n at hg
    rw [show rj (decompositionEquiv p x.val)=decompositionRestriction p M j x.val from
      localRestriction_decomposition p M j x.val,hτj] at hg
    exact hg
  · intro y
    have hr : r (decompositionEquiv p y)∈Subgroup.closure (r '' ({τ,φ} : Set _)) := by
      have h := hDgen (decompositionEquiv p y)
      change r (decompositionEquiv p y)∈Subgroup.closure ({r τ,r φ} : Set Gal(M/ℚ)) at h
      simpa only [Set.image_insert_eq,Set.image_singleton] using h
    have hg := HomKernelTransfer.mem_closure_image r rj hker
      (S:=({τ,φ} : Set _)) (x:=decompositionEquiv p y) hr
    rw [Set.image_insert_eq,Set.image_singleton,hτj,hφj] at hg
    change rj (decompositionEquiv p y)∈_ at hg
    rw [show rj (decompositionEquiv p y)=decompositionRestriction p M j y from
      localRestriction_decomposition p M j y] at hg
    exact hg

end UnitDistance.PrimeCompletion
