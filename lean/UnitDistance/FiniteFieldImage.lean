module

public import UnitDistance.UnramifiedAwayEquiv
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Galois.GaloisClosure
public import Mathlib.GroupTheory.PGroup

@[expose] public section
set_option backward.privateInPublic true


/-! Actual finite number fields inside the fixed algebraic closure of Q.
No abstract arithmetic realization datum is used. -/
noncomputable section
open NumberField
namespace UnitDistance.ArithmeticProP
open QuadraticRamification
variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]

/-- A chosen actual embedding into the fixed algebraic closure. -/
def rationalClosureEmbedding : K →ₐ[ℚ] AlgebraicClosure ℚ := IsAlgClosed.lift

/-- The image is an actual finite Galois intermediate field. -/
def finiteGaloisImage : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) := by
  let f := rationalClosureEmbedding K
  exact { toIntermediateField := f.fieldRange
          finiteDimensional := f.equivFieldRange.toLinearEquiv.finiteDimensional
          isGalois := IsGalois.of_algEquiv f.equivFieldRange }

instance finiteGaloisImage_numberField : NumberField (finiteGaloisImage K) :=
  NumberField.of_module_finite ℚ (finiteGaloisImage K)

/-- The original field is equivalent to its literal image. -/
def finiteGaloisImageEquiv : K ≃ₐ[ℚ] finiteGaloisImage K :=
  (rationalClosureEmbedding K).equivFieldRange

/-- The actual p-group property transports to the image Galois group. -/
theorem finiteGaloisImage_isPGroup {p : ℕ} (h : IsPGroup p (K ≃ₐ[ℚ] K)) :
    IsPGroup p (finiteGaloisImage K ≃ₐ[ℚ] finiteGaloisImage K) :=
  h.of_equiv (AlgEquiv.autCongr (finiteGaloisImageEquiv K))

/-- Actual ramification support transports to the image. -/
theorem finiteGaloisImage_unramifiedAway {N : ℤ} (h : UnramifiedAway K N) :
    UnramifiedAway (finiteGaloisImage K) N :=
  h.of_algEquiv (finiteGaloisImageEquiv K)

end UnitDistance.ArithmeticProP
