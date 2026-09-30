module

public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Tensor
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Algebra

@[expose] public section
set_option backward.privateInPublic true


/-! Adapted from GlobalClassFieldTheory/Reciprocity/FinitePlaceArtin/TowerRestriction
at Yamaguchi/Sawin commit 3a455e1aa9140dbbe7b7d68f508392a69c86d0f4 (Apache-2.0).
Both finite global extensions need only be Galois. The actual local normality
comes from the proved Galois certificate; embedding compatibility is explicit.
-/
noncomputable section
namespace UnitDistance.ArithmeticProP
open AlgebraicNumberTheory.Valuations HilbertRamification LocalClassFieldTheory
variable {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L]

/-- A compatible embedding of algebraic localizations carries
restriction of decomposition-group elements to restriction of the
corresponding local automorphisms. -/
theorem localizationAut_restrict_of_commutes_galois
    {E : Type}
    [Field E] [Algebra K E] [Algebra E L]
    [IsScalarTower K E L]
    [FiniteDimensional K E] [IsGalois K E]
    (vK : AbsoluteValue K ℝ)
    (hvK : vK.IsNontrivial)
    (wE : AbsoluteValueExtension vK E)
    (wL : AbsoluteValueExtension vK L) :
    letI hEK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := K) wE.1
    letI : SMul K wE.1.Completion := hEK.toSMul
    letI : Algebra vK.Completion wE.1.Completion :=
      AbsoluteValue.completionAlgebra vK wE.1 wE.2
    letI hLK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := K) wL.1
    letI : SMul K wL.1.Completion := hLK.toSMul
    letI : Algebra vK.Completion wL.1.Completion :=
      AbsoluteValue.completionAlgebra vK wL.1 wL.2
    let EL := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wE
    let LL := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wL
    ∀ (localizationEmbedding : EL →ₐ[vK.Completion] LL),
      letI hELL : Algebra EL LL :=
        localizationEmbedding.toRingHom.toAlgebra
      letI : SMul EL LL := hELL.toSMul
      letI : IsScalarTower vK.Completion EL LL :=
        IsScalarTower.of_algebraMap_eq' (by
          apply RingHom.ext
          intro x
          exact (localizationEmbedding.commutes x).symm)
      letI : FiniteDimensional vK.Completion EL :=
        AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite
          vK hvK wE
      letI : IsGalois vK.Completion EL :=
        LocalClassFieldTheory.localizedCompletionIsGalois vK wE
      let eDE :
          absoluteValueDecompositionGroup K wE.1 ≃*
            (EL ≃ₐ[vK.Completion] EL) :=
        decompositionGroupEquivAlgebraicLocalizationAut
          vK hvK wE
      let eDL :
          absoluteValueDecompositionGroup K wL.1 ≃*
            (LL ≃ₐ[vK.Completion] LL) :=
        decompositionGroupEquivAlgebraicLocalizationAut
          vK hvK wL
      (∀ z : E,
        localizationEmbedding
            (AbsoluteValue.toAlgebraicLocalization
              vK wE.1 wE.2 z) =
          AbsoluteValue.toAlgebraicLocalization
            vK wL.1 wL.2 (algebraMap E L z)) →
        ∀ tauL : LL ≃ₐ[vK.Completion] LL,
          AlgEquiv.restrictNormalHom E
              ((eDL.symm tauL).1 : L ≃ₐ[K] L) =
            ((eDE.symm
              (AlgEquiv.restrictNormalHom EL tauL)).1 :
                E ≃ₐ[K] E) := by
  let hEK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) wE.1
  let : SMul K wE.1.Completion := hEK.toSMul
  let : Algebra vK.Completion wE.1.Completion :=
    AbsoluteValue.completionAlgebra vK wE.1 wE.2
  let hLK :=
    AbsoluteValue.extensionCompletionAlgebra
      (K := K) wL.1
  let : SMul K wL.1.Completion := hLK.toSMul
  let : Algebra vK.Completion wL.1.Completion :=
    AbsoluteValue.completionAlgebra vK wL.1 wL.2
  let EL := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wE
  let LL := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wL
  change
    ∀ localizationEmbedding : EL →ₐ[vK.Completion] LL, _
  intro localizationEmbedding
  let hELL : Algebra EL LL :=
    localizationEmbedding.toRingHom.toAlgebra
  let : SMul EL LL := hELL.toSMul
  let : IsScalarTower vK.Completion EL LL :=
    IsScalarTower.of_algebraMap_eq' (by
      apply RingHom.ext
      intro x
      exact (localizationEmbedding.commutes x).symm)
  let : FiniteDimensional vK.Completion EL :=
    AlgebraicNumberTheory.Valuations.localizedCompletionModuleFinite
      vK hvK wE
  let : IsGalois vK.Completion EL :=
    LocalClassFieldTheory.localizedCompletionIsGalois vK wE
  let eDE :
      absoluteValueDecompositionGroup K wE.1 ≃*
        (EL ≃ₐ[vK.Completion] EL) :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK wE
  let eDL :
      absoluteValueDecompositionGroup K wL.1 ≃*
        (LL ≃ₐ[vK.Completion] LL) :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK wL
  change
    (∀ z : E,
      localizationEmbedding
          (AbsoluteValue.toAlgebraicLocalization
            vK wE.1 wE.2 z) =
        AbsoluteValue.toAlgebraicLocalization
          vK wL.1 wL.2 (algebraMap E L z)) →
      ∀ tauL : LL ≃ₐ[vK.Completion] LL, _
  intro hlocalization tauL
  let rhoL : absoluteValueDecompositionGroup K wL.1 :=
    eDL.symm tauL
  let tauE := AlgEquiv.restrictNormalHom EL tauL
  let rhoE : absoluteValueDecompositionGroup K wE.1 :=
    eDE.symm tauE
  change
    AlgEquiv.restrictNormalHom E
        (rhoL.1 : L ≃ₐ[K] L) =
      (rhoE.1 : E ≃ₐ[K] E)
  apply AlgEquiv.ext
  intro z
  apply (algebraMap E L).injective
  apply
    (AbsoluteValue.toAlgebraicLocalization
      vK wL.1 wL.2).injective
  let u : EL :=
    AbsoluteValue.toAlgebraicLocalization
      vK wE.1 wE.2 z
  have hcommutes :
      tauL (localizationEmbedding u) =
        localizationEmbedding
          ((AlgEquiv.restrictNormalHom EL tauL) u) := by
    change
      tauL (algebraMap EL LL u) =
        algebraMap EL LL
          ((AlgEquiv.restrictNormalHom EL tauL) u)
    exact
      (AlgEquiv.restrictNormal_commutes
        tauL EL u).symm
  calc
    AbsoluteValue.toAlgebraicLocalization vK wL.1 wL.2
        (algebraMap E L
          ((AlgEquiv.restrictNormalHom E
            (rhoL.1 : L ≃ₐ[K] L)) z)) =
      AbsoluteValue.toAlgebraicLocalization vK wL.1 wL.2
        ((rhoL.1 : L ≃ₐ[K] L)
          (algebraMap E L z)) := by
            exact congrArg
              (AbsoluteValue.toAlgebraicLocalization
                vK wL.1 wL.2)
              (AlgEquiv.restrictNormal_commutes
                (rhoL.1 : L ≃ₐ[K] L) E z)
    _ = eDL rhoL
        (AbsoluteValue.toAlgebraicLocalization
          vK wL.1 wL.2 (algebraMap E L z)) := by
            rw [localizationRamificationGroups_decompositionGroupEquiv_toLocalization]
    _ = tauL
        (AbsoluteValue.toAlgebraicLocalization
          vK wL.1 wL.2 (algebraMap E L z)) := by
            rw [eDL.apply_symm_apply]
    _ = tauL
        (localizationEmbedding
          (AbsoluteValue.toAlgebraicLocalization
            vK wE.1 wE.2 z)) := by
            rw [hlocalization]
    _ = localizationEmbedding
        ((AlgEquiv.restrictNormalHom EL tauL)
          (AbsoluteValue.toAlgebraicLocalization
            vK wE.1 wE.2 z)) := by
            exact hcommutes
    _ = localizationEmbedding
        (tauE
          (AbsoluteValue.toAlgebraicLocalization
            vK wE.1 wE.2 z)) := by
            rfl
    _ = localizationEmbedding
        (eDE rhoE
          (AbsoluteValue.toAlgebraicLocalization
            vK wE.1 wE.2 z)) := by
            rw [eDE.apply_symm_apply]
    _ = localizationEmbedding
        (AbsoluteValue.toAlgebraicLocalization vK wE.1 wE.2
          ((rhoE.1 : E ≃ₐ[K] E) z)) := by
            rw [localizationRamificationGroups_decompositionGroupEquiv_toLocalization]
    _ = AbsoluteValue.toAlgebraicLocalization vK wL.1 wL.2
        (algebraMap E L
          ((rhoE.1 : E ≃ₐ[K] E) z)) := by
            rw [hlocalization]


end UnitDistance.ArithmeticProP
