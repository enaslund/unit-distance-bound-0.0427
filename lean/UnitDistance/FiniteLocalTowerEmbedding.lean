module

public import UnitDistance.LocalTowerRestriction
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Completion.AdicCompletionMap

@[expose] public section
set_option backward.privateInPublic true


/-! Adapted from the first four declarations of FinitePlaceArtin/TowerRestriction
at Yamaguchi/Sawin commit 3a455e1aa9140dbbe7b7d68f508392a69c86d0f4 (Apache-2.0).
The top extension is only Galois, and the named algebra providers are the
underlying completion providers rather than Artin-map wrappers. -/
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField
namespace UnitDistance.ArithmeticProP
open AlgebraicNumberTheory.Valuations HilbertRamification LocalClassFieldTheory
variable {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L]
variable [FiniteDimensional K L] [IsGalois K L]

/-- Restrict an extension of a finite place through an intermediate
field in a scalar tower. -/
def restrictFinitePlaceExtension
    {E : Type}
    [Field E] [Algebra K E] [Algebra E L]
    [IsScalarTower K E L]
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) E where
  val :=
    w.1.comp (f := algebraMap E L)
      (algebraMap E L).injective
  property x := by
    change
      w.1 (algebraMap E L (algebraMap K E x)) =
        NumberField.HeightOneSpectrum.adicAbv K v x
    rw [← IsScalarTower.algebraMap_apply K E L]
    exact w.2 x

omit [NumberField K] [FiniteDimensional K L]
    [IsGalois K L] in
/-- Completion maps compose along a scalar tower when the three
absolute values extend one another. -/
theorem absoluteValueCompletionMap_comp_of_isScalarTower
    {E : Type}
    [Field E] [Algebra K E] [Algebra E L]
    [IsScalarTower K E L]
    (vK : AbsoluteValue K ℝ)
    (vE : AbsoluteValue E ℝ)
    (vL : AbsoluteValue L ℝ)
    (hKE : AbsoluteValue.Extends vK vE)
    (hEL : AbsoluteValue.Extends vE vL)
    (hKL : AbsoluteValue.Extends vK vL) :
    (AbsoluteValue.completionMap vE vL hEL).comp
        (AbsoluteValue.completionMap vK vE hKE) =
      AbsoluteValue.completionMap vK vL hKL := by
  ext x
  refine
    UniformSpace.Completion.induction_on
      (α := WithAbs vK) x ?_ ?_
  · exact isClosed_eq
      ((AbsoluteValue.completionMap_isometry
          vE vL hEL).continuous.comp
        (AbsoluteValue.completionMap_isometry
          vK vE hKE).continuous)
      (AbsoluteValue.completionMap_isometry
        vK vL hKL).continuous
  · intro a
    have ha : (a : vK.Completion) =
        algebraMap K vK.Completion
          (WithAbs.equiv vK a) := by
      change (a : vK.Completion) =
        (((WithAbs.equiv vK).symm
          (WithAbs.equiv vK a) : WithAbs vK) :
            vK.Completion)
      exact congrArg
        (fun z : WithAbs vK => (z : vK.Completion))
        ((WithAbs.equiv vK).symm_apply_apply a).symm
    rw [ha]
    change
      AbsoluteValue.completionMap vE vL hEL
          (AbsoluteValue.completionMap vK vE hKE
            (algebraMap K vK.Completion
              (WithAbs.equiv vK a))) =
        AbsoluteValue.completionMap vK vL hKL
          (algebraMap K vK.Completion
            (WithAbs.equiv vK a))
    rw [AbsoluteValue.completionMap_coe,
      AbsoluteValue.toCompletion_eq_algebraMap,
      AbsoluteValue.completionMap_coe,
      AbsoluteValue.completionMap_coe,
      IsScalarTower.algebraMap_apply K E L]

/-- The completion map in a number-field tower restricts to the
corresponding algebraic localizations. -/
noncomputable def finitePlaceRestrictedLocalizedCompletionAlgHom
    {E : Type}
    [Field E] [Algebra K E] [Algebra E L]
    [IsScalarTower K E L]
    [FiniteDimensional K E] [IsGalois K E]
    (v : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let wE :=
      restrictFinitePlaceExtension
        (K := K) (L := L) (E := E) v wL
    let EL := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wE
    let LL := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wL
    letI : Algebra vK.Completion EL :=
      localizedCompletionBaseAlgebra vK wE
    letI : Algebra vK.Completion LL :=
      localizedCompletionBaseAlgebra vK wL
    EL →ₐ[vK.Completion] LL := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let wE :=
    restrictFinitePlaceExtension
      (K := K) (L := L) (E := E) v wL
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
  let hwEL : AbsoluteValue.Extends wE.1 wL.1 := by
    intro x
    rfl
  letI : Algebra wE.1.Completion wL.1.Completion :=
    AbsoluteValue.completionAlgebra wE.1 wL.1 hwEL
  have hcompletion :
      (AbsoluteValue.completionMap wE.1 wL.1 hwEL).comp
          (AbsoluteValue.completionMap vK wE.1 wE.2) =
        AbsoluteValue.completionMap vK wL.1 wL.2 :=
    absoluteValueCompletionMap_comp_of_isScalarTower
      (K := K) (L := L) (E := E)
      vK wE.1 wL.1 wE.2 hwEL wL.2
  let completionAlgHom :
      wE.1.Completion →ₐ[vK.Completion]
        wL.1.Completion :=
    { __ := AbsoluteValue.completionMap wE.1 wL.1 hwEL
      commutes' := fun x => by
        change
          AbsoluteValue.completionMap wE.1 wL.1 hwEL
              (AbsoluteValue.completionMap
                vK wE.1 wE.2 x) =
            AbsoluteValue.completionMap
              vK wL.1 wL.2 x
        exact DFunLike.congr_fun hcompletion x }
  let EL :=
    AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wE
  let LL :=
    AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wL
  let eE :
      EL ≃ₐ[vK.Completion] wE.1.Completion :=
    AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
      vK hvK wE
  let eL :
      LL ≃ₐ[vK.Completion] wL.1.Completion :=
    AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
      vK hvK wL
  let localizationAlgHom :
      EL →ₐ[vK.Completion] LL :=
    eL.symm.toAlgHom.comp
      (completionAlgHom.comp eE.toAlgHom)
  exact localizationAlgHom

omit [IsGalois K L] in
/-- The restricted-localization map agrees with the original
number-field embedding on the intermediate field. -/
theorem finitePlaceRestrictedLocalizedCompletionAlgHom_toAlgebraicLocalization
    {E : Type}
    [Field E] [Algebra K E] [Algebra E L]
    [IsScalarTower K E L]
    [FiniteDimensional K E] [IsGalois K E]
    (v : HeightOneSpectrum (𝓞 K))
    (wL : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (x : E) :
    let vK := NumberField.HeightOneSpectrum.adicAbv K v
    let wE :=
      restrictFinitePlaceExtension
        (K := K) (L := L) (E := E) v wL
    let EL := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wE
    let LL := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wL
    letI : Algebra vK.Completion EL :=
      localizedCompletionBaseAlgebra vK wE
    letI : Algebra vK.Completion LL :=
      localizedCompletionBaseAlgebra vK wL
    finitePlaceRestrictedLocalizedCompletionAlgHom
        (K := K) (L := L) (E := E) v wL
        (AbsoluteValue.toAlgebraicLocalization
          vK wE.1 wE.2 x) =
      AbsoluteValue.toAlgebraicLocalization
        vK wL.1 wL.2 (algebraMap E L x) := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let hvK : vK.IsNontrivial :=
    RayClass.adicAbv_isNontrivial v
  let wE :=
    restrictFinitePlaceExtension
      (K := K) (L := L) (E := E) v wL
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
  let hwEL : AbsoluteValue.Extends wE.1 wL.1 := by
    intro z
    rfl
  let : Algebra wE.1.Completion wL.1.Completion :=
    AbsoluteValue.completionAlgebra wE.1 wL.1 hwEL
  let LL := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK wL
  let eL :
      LL ≃ₐ[vK.Completion] wL.1.Completion :=
    AlgebraicNumberTheory.Valuations.localizedCompletionEquivCompletion
      vK hvK wL
  apply eL.injective
  change
    AbsoluteValue.completionMap wE.1 wL.1 hwEL
        (AbsoluteValue.toCompletion wE.1 x) =
      AbsoluteValue.toCompletion wL.1
        (algebraMap E L x)
  rw [AbsoluteValue.toCompletion_eq_algebraMap,
    AbsoluteValue.completionMap_coe]


end UnitDistance.ArithmeticProP
