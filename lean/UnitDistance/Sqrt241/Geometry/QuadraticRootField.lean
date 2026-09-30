module

public import UnitDistance.QuadraticSevenField
public import Mathlib.Data.Rat.Lemmas

@[expose] public section
set_option backward.privateInPublic true


/-!
# The quadratic field `ℚ(√d)` for an admissible radicand

Copy of `UnitDistance.QuadraticSevenField` with the radicand `7` replaced by a
natural number `d` that is a prime congruent to `3` modulo `4`
(`Admissible d`). The tower over `ℚ(√241)` uses `d = 3`
(`admissible_three`); the ℚ development used `d = 7`.
-/

noncomputable section
set_option autoImplicit false
namespace UnitDistance.Sqrt241.QuadraticRoot
open QuadraticAlgebra UnitDistance.KummerInvariant UnitDistance.Multiquadratic

/-- The radicands that replace seven: primes congruent to three modulo four. -/
structure Admissible (d : ℕ) : Prop where
  prime : d.Prime
  mod_four : d % 4 = 3

instance admissible_three : Fact (Admissible 3) := ⟨⟨Nat.prime_three, rfl⟩⟩

theorem admissible_seven : Admissible 7 := ⟨by norm_num, rfl⟩

/-- A natural number congruent to three modulo four is not a square. -/
theorem not_isSquare_of_mod_four {d : ℕ} (h : d % 4 = 3) : ¬IsSquare d := by
  rintro ⟨m, hm⟩
  have h4 : m * m % 4 = (m % 4) * (m % 4) % 4 := Nat.mul_mod _ _ _
  have hlt : m % 4 < 4 := Nat.mod_lt _ (by norm_num)
  rw [← hm, h] at h4
  interval_cases hmm : m % 4 <;> omega

variable (d : ℕ) [hd : Fact (Admissible d)]

instance root_nonsquare : Fact (Nonsquare (d : ℚ)) :=
  ⟨nonsquare_of_not_isSquare _ (by
    rw [Rat.isSquare_natCast_iff]
    exact not_isSquare_of_mod_four hd.out.mod_four)⟩

/-- The quadratic field obtained by adjoining a square root of `d` to `ℚ`. -/
abbrev RootField := Extension (d : ℚ)

instance rootField : Field (RootField d) := inferInstanceAs (Field (Extension (d : ℚ)))
instance rootNumberField : NumberField (RootField d) := inferInstance

omit hd in
theorem degree : Module.finrank ℚ (RootField d) = 2 := by
  exact finrank_eq_two _ _

theorem norm_eq (z : RootField d) : Algebra.norm ℚ z = z.re^2-d*z.im^2 := by
  rw [Algebra.norm_apply]
  change (DistribSMul.toLinearMap ℚ (RootField d) z).det = _
  rw [QuadraticAlgebra.det_toLinearMap_eq_norm]
  simp [QuadraticAlgebra.norm]
  ring

theorem trace_eq (z : RootField d) : Algebra.trace ℚ (RootField d) z = 2*z.re := by
  rw [Algebra.trace_eq_matrix_trace (QuadraticAlgebra.basis (d : ℚ) 0)]
  simp [Matrix.trace,Algebra.leftMulMatrix_apply,LinearMap.toMatrix_apply,QuadraticAlgebra.basis]
  ring

/-- Substitution into any actual field containing a displayed root. -/
def embedding {F : Type*} [Field F] [CharZero F] (r : F) (hr : r^2=(d : F)) :
    RootField d →ₐ[ℚ] F :=
  QuadraticAlgebra.lift ⟨r,by simpa [pow_two] using hr⟩

@[simp] theorem embedding_root {F : Type*} [Field F] [CharZero F] (r : F) (hr : r^2=(d : F)) :
    embedding d r hr omega = r := by
  change (omega : RootField d).re • (1 : F) + (omega : RootField d).im • r = r
  simp

/-- Integrality gives the integer trace and norm coordinates used by the
rational parity argument. -/
theorem trace_norm_integers {z : RootField d} (hz : IsIntegral ℤ z) :
    ∃ a n : ℤ, 2*z.re=(a : ℚ) ∧ z.re^2-d*z.im^2=(n : ℚ) := by
  obtain ⟨a,ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (Algebra.isIntegral_trace (L := ℚ) hz)
  obtain ⟨n,hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp
    (Algebra.isIntegral_norm ℚ hz)
  refine ⟨a,n,?_,?_⟩
  · rw [← trace_eq,← ha]
    rfl
  · rw [← norm_eq,← hn]
    rfl

end UnitDistance.Sqrt241.QuadraticRoot
