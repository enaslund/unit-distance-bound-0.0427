/- Retyped from `UnitDistance/ProPStageLocalConditions.lean` (adapted from
Yamaguchi/Sawin RealProPStageLocalConditions at commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, Apache-2.0): ℚ is replaced by an
arbitrary number field `F`. Only the finite-place statement is retained. -/
module

public import UnitDistance.Sqrt241.ProP.FinitePExtension
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.LocalBlocks
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.IdealToCompletion

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false
/-!
# Local conditions of finite p-layers over `F`

The global ramification conditions on an admissible finite layer imply the
chosen-completion conditions used by finite H² localization.
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace UnitDistance.Sqrt241.ProP

variable (F : Type) [Field F] [NumberField F]

/-- Every admissible stage is a number field. -/
instance stageNumberField (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 F))) (E : FinitePExtension F p T) : NumberField E.val :=
  NumberField.of_module_finite F E.val

/-- Every admissible stage is Galois over `F`. -/
instance stageIsGalois (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 F))) (E : FinitePExtension F p T) :
    IsGalois F E.val.toIntermediateField := E.val.isGalois

/-- The chosen completion of an admissible layer is unramified at every
finite place outside its allowed support. -/
theorem finitePExtension_chosenFinitePlaceIsUnramified
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 F))) (E : FinitePExtension F p T)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ T) :
    ChosenFinitePlaceIsUnramified (K := F) (L := E.val) v := by
  apply chosenFinitePlaceIsUnramified_of_isUnramifiedAt
  apply E.property.2
  simpa only [finitePlaceBelow_finitePlaceExtensionCentre] using hv

end UnitDistance.Sqrt241.ProP
