module

public import UnitDistance.Sqrt241.Geometry.QuadraticRootField
public import UnitDistance.Sqrt241.Geometry.QuadraticRootIntegrality
public import UnitDistance.QuadraticSevenNormCongruence

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual norm congruences above `ℚ(√d)`

Copy of `UnitDistance.QuadraticSevenNormCongruence` for an admissible radicand
`d` in place of `7`. The rational coordinate lemma applies to the actual
integral trace and norm; norm transitivity then gives the signed congruence
and the norm of units for every number field containing a square root of `d`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.Sqrt241.QuadraticRoot
open NumberField
open scoped NumberField

variable {d : ℕ} [hd : Fact (Admissible d)]

theorem integral_coordinates {z : RootField d} (hz : IsIntegral ℤ z) :
    ∃ a b : ℤ, z.re=(a : ℚ) ∧ z.im=(b : ℚ) := by
  obtain ⟨a,n,ha,hn⟩ := trace_norm_integers d hz
  exact rational_coordinates_of_trace_norm z.re z.im a n ha hn

variable {F : Type*} [Field F] [NumberField F] [Algebra (RootField d) F]
  [IsScalarTower ℚ (RootField d) F]
include hd

/-- The actual signed absolute norm of an integral element has the displayed
integer quadratic-form representation. -/
theorem integer_norm_representation (x : 𝓞 F) :
    ∃ a b : ℤ, Algebra.norm ℤ x = a^2-(d : ℤ)*b^2 := by
  have hz : IsIntegral ℤ (Algebra.norm (RootField d) (x : F)) :=
    Algebra.isIntegral_norm (RootField d) x.2
  obtain ⟨a,b,ha,hb⟩ := integral_coordinates hz
  refine ⟨a,b,?_⟩
  have h : (Algebra.norm ℤ x : ℚ) = (a : ℚ)^2-(d : ℚ)*(b : ℚ)^2 := by
    calc
      (Algebra.norm ℤ x : ℚ) = Algebra.norm ℚ (x : F) := Algebra.coe_norm_int x
      _ = Algebra.norm ℚ (Algebra.norm (RootField d) (x : F)) :=
        (Algebra.norm_norm (S := RootField d) (a := (x : F))).symm
      _ = _ := (norm_eq d _).trans (congrArg₂ (fun s t : ℚ => s^2-(d : ℚ)*t^2) ha hb)
  exact_mod_cast h

/-- Every odd signed norm in an actual extension of `ℚ(√d)` is `1` modulo `4`. -/
theorem integer_norm_mod_four (x : 𝓞 F) (hx : Odd (Algebra.norm ℤ x)) :
    Algebra.norm ℤ x % 4 = 1 := by
  obtain ⟨a,b,h⟩ := integer_norm_representation (d := d) x
  rw [h] at hx ⊢
  exact odd_norm_mod_four a b hx

/-- The actual principal norm's finite mod-four character equals its sign. -/
theorem integer_norm_chi4_eq_sign (x : 𝓞 F) (hx : Odd (Algebra.norm ℤ x)) :
    ZMod.χ₄ ((Algebra.norm ℤ x).natAbs : ZMod 4) = Int.sign (Algebra.norm ℤ x) :=
  UnitDistance.QuadraticSeven.chi4_natAbs_eq_sign_of_mod_four _
    (integer_norm_mod_four (d := d) x hx)

/-- Every integral unit in an actual extension of `ℚ(√d)` has norm `+1`. -/
theorem integer_norm_eq_one_of_isUnit (x : 𝓞 F) (hx : IsUnit x) :
    Algebra.norm ℤ x = 1 := by
  obtain ⟨a,b,h⟩ := integer_norm_representation (d := d) x
  have hu : IsUnit (Algebra.norm ℤ x) := hx.map (Algebra.norm ℤ)
  rw [h] at hu ⊢
  exact norm_eq_one_of_isUnit a b hu

end UnitDistance.Sqrt241.QuadraticRoot

namespace UnitDistance.Sqrt241.QuadraticRoot
open scoped NumberField
variable {d : ℕ} [hd : Fact (Admissible d)]
variable {F : Type*} [Field F] [NumberField F]

/-- A displayed actual square root suffices; the algebra inclusion is constructed. -/
theorem integer_norm_chi4_eq_sign_of_root (r : F) (hr : r^2=(d : F))
    (x : 𝓞 F) (hx : Odd (Algebra.norm ℤ x)) :
    ZMod.χ₄ ((Algebra.norm ℤ x).natAbs : ZMod 4) = Int.sign (Algebra.norm ℤ x) := by
  let f := embedding d r hr
  let : Algebra (RootField d) F := f.toRingHom.toAlgebra
  let : IsScalarTower ℚ (RootField d) F := IsScalarTower.of_algHom f
  exact integer_norm_chi4_eq_sign (d := d) x hx

/-- Integral units have norm `+1` whenever the actual field contains a root of `d`. -/
theorem integer_norm_eq_one_of_isUnit_of_root (r : F) (hr : r^2=(d : F))
    (x : 𝓞 F) (hx : IsUnit x) : Algebra.norm ℤ x = 1 := by
  let f := embedding d r hr
  let : Algebra (RootField d) F := f.toRingHom.toAlgebra
  let : IsScalarTower ℚ (RootField d) F := IsScalarTower.of_algHom f
  exact integer_norm_eq_one_of_isUnit (d := d) x hx

end UnitDistance.Sqrt241.QuadraticRoot
