module

public import UnitDistance.MultiquadraticTower
public import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.RingTheory.Norm.Transitivity

@[expose] public section
set_option backward.privateInPublic true


/-! The actual quadratic field with square root of seven and its norm and trace. -/
noncomputable section
namespace UnitDistance.QuadraticSeven
open QuadraticAlgebra KummerInvariant Multiquadratic

instance seven_nonsquare : Fact (Nonsquare (7 : ℚ)) :=
  ⟨nonsquare_of_not_isSquare _ (by decide +kernel)⟩

abbrev SevenField := Extension (7 : ℚ)

instance sevenField : Field SevenField := inferInstanceAs (Field (Extension (7 : ℚ)))
instance sevenNumberField : NumberField SevenField := inferInstance

 theorem degree : Module.finrank ℚ SevenField = 2 := by
  exact finrank_eq_two _ _

 theorem norm_eq (z : SevenField) : Algebra.norm ℚ z = z.re^2-7*z.im^2 := by
  rw [Algebra.norm_apply]
  change (DistribSMul.toLinearMap ℚ SevenField z).det = _
  rw [QuadraticAlgebra.det_toLinearMap_eq_norm]
  simp [QuadraticAlgebra.norm]
  ring

 theorem trace_eq (z : SevenField) : Algebra.trace ℚ SevenField z = 2*z.re := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis (7 : ℚ) 0)]
  simp [Matrix.trace,Algebra.leftMulMatrix_apply,LinearMap.toMatrix_apply,QuadraticAlgebra.basis]
  ring

/-- Substitution into any actual field containing a displayed root. -/
def embedding {F : Type*} [Field F] [CharZero F] (r : F) (hr : r^2=7) :
    SevenField →ₐ[ℚ] F :=
  QuadraticAlgebra.lift ⟨r,by simpa [pow_two] using hr⟩

@[simp] theorem embedding_root {F : Type*} [Field F] [CharZero F] (r : F) (hr : r^2=7) :
    embedding r hr omega = r := by
  change (omega : SevenField).re • (1 : F) + (omega : SevenField).im • r = r
  simp

/-- Integrality gives the integer trace and norm coordinates used by the
rational parity argument. -/
theorem trace_norm_integers {z : SevenField} (hz : IsIntegral ℤ z) :
    ∃ a n : ℤ, 2*z.re=(a : ℚ) ∧ z.re^2-7*z.im^2=(n : ℚ) := by
  obtain ⟨a,ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (Algebra.isIntegral_trace (L := ℚ) hz)
  obtain ⟨n,hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (Algebra.isIntegral_norm ℚ hz)
  refine ⟨a,n,?_,?_⟩
  · rw [← trace_eq,← ha]
    rfl
  · rw [← norm_eq,← hn]
    rfl

end UnitDistance.QuadraticSeven
