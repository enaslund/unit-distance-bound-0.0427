module

public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedComparison
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.LocalUnramifiedH2Vanishing

@[expose] public section
set_option backward.privateInPublic true


/-! Restriction of actual absolute local inertia into the actual finite residue kernel. -/
noncomputable section
open scoped ValuativeRel
namespace UnitDistance.ArithmeticProP
open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField LocalClassFieldTheory
open ClassFieldTower.Martinet.Shafarevich

variable (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L]

/-- An actual absolute inertia automorphism acts through finite residue inertia
on every compatibly embedded finite Galois local extension. -/
theorem finiteResidueInertia_of_absoluteInertia
    (f : L →ₐ[K] SeparableClosure K)
    (τ : Gal(SeparableClosure K/K))
    (hτ : τ ∈ (localResidueDegree K).toMonoidHom.ker)
    (σ : Gal(L/K)) (hσ : ∀ x : L, τ (f x) = f (σ x)) :
    σ ∈ (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker := by
  let τB := (intrinsicAbstractBaseEquivAbsolute K).symm τ
  have hτB : τB.1 = τ := intrinsicAbstractBaseEquivAbsolute_symm_apply_val K τ
  have hact : localSeparableResidueAlgAction K τ = 1 := by
    have h := hτ
    rw [localResidueDegree_ker_eq_residueAction_ker] at h
    exact h
  have hq : finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L f
      (QuotientGroup.mk τB) = σ := by
    ext x
    apply f.injective
    calc
      f (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L f
          (QuotientGroup.mk τB) x) = τB.1 (f x) :=
        finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply K L f τB x
      _ = τ (f x) := congrArg (fun g => g (f x)) hτB
      _ = f (σ x) := hσ x
  change galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L σ = 1
  apply AlgEquiv.ext
  intro x
  apply (finiteGaloisResidueEmbeddingOfEmbedding K L f).injective
  change finiteGaloisResidueEmbeddingOfEmbedding K L f
      (galoisGroupResidueAlgEquivOfIsIntegralClosure K L σ x) =
    finiteGaloisResidueEmbeddingOfEmbedding K L f x
  rw [← hq, finiteGaloisResidueEmbeddingOfEmbedding_equivariant, hτB, hact]
  rfl

end UnitDistance.ArithmeticProP
