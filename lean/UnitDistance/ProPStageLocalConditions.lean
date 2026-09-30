/- Adapted from Yamaguchi/Sawin RealProPStageLocalConditions at commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4 (Apache-2.0). Only the finite-place
statement is retained; infinite places are unrestricted. -/
module

public import UnitDistance.FinitePExtension
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SPlaces.LocalBlocks
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Completion.UnramifiedComparison.IdealToCompletion

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false
/-!
# Local conditions of actual finite p-layers

The global ramification certificates on an admissible finite layer imply
the actual chosen-completion conditions used by finite H² localization.
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace UnitDistance.ArithmeticProP

private local instance stageNumberField (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 ℚ))) (E : FinitePExtension p T) : NumberField E.val :=
  NumberField.of_module_finite ℚ E.val

private local instance stageIsGalois (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 ℚ))) (E : FinitePExtension p T) :
    IsGalois ℚ E.val.toIntermediateField := E.val.isGalois

/-- The actual chosen completion of an admissible layer is unramified
at every finite place outside its allowed support. -/
theorem finitePExtension_chosenFinitePlaceIsUnramified
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ))) (E : FinitePExtension p T)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v ∉ T) :
    ChosenFinitePlaceIsUnramified (K := ℚ) (L := E.val) v := by
  apply chosenFinitePlaceIsUnramified_of_isUnramifiedAt
  apply E.property.2
  simpa only [finitePlaceBelow_finitePlaceExtensionCentre] using hv


end UnitDistance.ArithmeticProP
