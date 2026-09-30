module

public import UnitDistance.QuadraticSevenField
public import UnitDistance.QuadraticSevenIntegrality
public import Mathlib.NumberTheory.NumberField.Norm

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual norm congruences above Q(sqrt7)

The rational coordinate lemma applies to the actual integral trace and norm.
Norm transitivity then gives the signed congruence for every actual number
field containing the displayed quadratic field.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.QuadraticSeven
open NumberField
open scoped NumberField

 theorem integral_coordinates {z : SevenField} (hz : IsIntegral ℤ z) :
    ∃ a b : ℤ, z.re=(a : ℚ) ∧ z.im=(b : ℚ) := by
  obtain ⟨a,n,ha,hn⟩ := trace_norm_integers hz
  exact rational_coordinates_of_trace_norm z.re z.im a n ha hn

variable {F : Type*} [Field F] [NumberField F] [Algebra SevenField F]
  [IsScalarTower ℚ SevenField F]

/-- The actual signed absolute norm of an integral element has the displayed
integer quadratic-form representation. -/
theorem integer_norm_representation (x : 𝓞 F) :
    ∃ a b : ℤ, Algebra.norm ℤ x = a^2-7*b^2 := by
  have hz : IsIntegral ℤ (Algebra.norm SevenField (x : F)) :=
    Algebra.isIntegral_norm SevenField x.2
  obtain ⟨a,b,ha,hb⟩ := integral_coordinates hz
  refine ⟨a,b,?_⟩
  have h : (Algebra.norm ℤ x : ℚ) = (a : ℚ)^2-7*(b : ℚ)^2 := by
    calc
      (Algebra.norm ℤ x : ℚ) = Algebra.norm ℚ (x : F) := Algebra.coe_norm_int x
      _ = Algebra.norm ℚ (Algebra.norm SevenField (x : F)) :=
        (Algebra.norm_norm (S := SevenField) (a := (x : F))).symm
      _ = _ := (norm_eq _).trans (congrArg₂ (fun s t : ℚ => s^2-7*t^2) ha hb)
  exact_mod_cast h

/-- Every odd signed norm in an actual extension of Q(sqrt7) is 1 modulo4. -/
theorem integer_norm_mod_four (x : 𝓞 F) (hx : Odd (Algebra.norm ℤ x)) :
    Algebra.norm ℤ x % 4 = 1 := by
  obtain ⟨a,b,h⟩ := integer_norm_representation x
  rw [h] at hx ⊢
  exact odd_norm_mod_four a b hx

/-- The actual principal norm's finite mod-four character equals its sign. -/
theorem integer_norm_chi4_eq_sign (x : 𝓞 F) (hx : Odd (Algebra.norm ℤ x)) :
    ZMod.χ₄ ((Algebra.norm ℤ x).natAbs : ZMod 4) = Int.sign (Algebra.norm ℤ x) :=
  chi4_natAbs_eq_sign_of_mod_four _ (integer_norm_mod_four x hx)

/-- Every integral unit in an actual extension of Q(sqrt7) has norm +1. -/
theorem integer_norm_eq_one_of_isUnit (x : 𝓞 F) (hx : IsUnit x) :
    Algebra.norm ℤ x = 1 := by
  obtain ⟨a,b,h⟩ := integer_norm_representation x
  have hu : IsUnit (Algebra.norm ℤ x) := hx.map (Algebra.norm ℤ)
  rw [h] at hu ⊢
  exact norm_eq_one_of_isUnit a b hu

end UnitDistance.QuadraticSeven

namespace UnitDistance.QuadraticSeven
open scoped NumberField
variable {F : Type*} [Field F] [NumberField F]

/-- A displayed actual square root suffices; the algebra inclusion is constructed. -/
theorem integer_norm_chi4_eq_sign_of_root (r : F) (hr : r^2=7)
    (x : 𝓞 F) (hx : Odd (Algebra.norm ℤ x)) :
    ZMod.χ₄ ((Algebra.norm ℤ x).natAbs : ZMod 4) = Int.sign (Algebra.norm ℤ x) := by
  let f := embedding r hr
  letI : Algebra SevenField F := f.toRingHom.toAlgebra
  letI : IsScalarTower ℚ SevenField F := IsScalarTower.of_algHom f
  exact integer_norm_chi4_eq_sign x hx

/-- Integral units have norm +1 whenever the actual field contains a root of seven. -/
theorem integer_norm_eq_one_of_isUnit_of_root (r : F) (hr : r^2=7)
    (x : 𝓞 F) (hx : IsUnit x) : Algebra.norm ℤ x = 1 := by
  let f := embedding r hr
  letI : Algebra SevenField F := f.toRingHom.toAlgebra
  letI : IsScalarTower ℚ SevenField F := IsScalarTower.of_algHom f
  exact integer_norm_eq_one_of_isUnit x hx

end UnitDistance.QuadraticSeven
