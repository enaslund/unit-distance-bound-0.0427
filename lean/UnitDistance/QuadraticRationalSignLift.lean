module

public import UnitDistance.QuadraticSignLift
public import Mathlib.Algebra.Algebra.Hom.Rat

@[expose] public section
set_option backward.privateInPublic true


/-!
# Rational sign lifts with explicit algebra structures

The semilinear coordinate map is first regarded as a ring equivalence and
then as a rational algebra equivalence for the actual chosen rational
algebra structure. This avoids relying on expensive definitional equality
between inherited and canonical rational algebra instances in long towers.
-/

noncomputable section
namespace UnitDistance.Multiquadratic
open QuadraticAlgebra KummerInvariant
variable {E : Type*} [Field E] [CharZero E] [Algebra ℚ E]

@[simp] theorem rational_map_binarySign (σ : Gal(E/ℚ)) (ε : ZMod 2) :
    σ (binarySign (E := E) ε) = binarySign ε := by simp [binarySign]

/-- The actual sign lift for any specified rational algebra structure on
the quadratic algebra. -/
def rationalSignLift (σ : Gal(E/ℚ)) (a : ℚ) [Algebra ℚ (Extension (a : E))]
    (ε : ZMod 2) : Extension (a : E) ≃ₐ[ℚ] Extension (a : E) := by
  let e : Extension (a : E) ≃+* Extension (a : E) := by
    letI : Algebra ℚ (Extension (a : E)) := QuadraticAlgebra.instAlgebra
    exact (liftEquiv σ (a : E) (binarySign ε) (by simp) (binarySign_ne_zero ε)).toRingEquiv
  exact AlgEquiv.ofBijective e.toRingHom.toRatAlgHom e.bijective

@[simp] theorem rationalSignLift_re (σ : Gal(E/ℚ)) (a : ℚ)
    [Algebra ℚ (Extension (a : E))] (ε : ZMod 2) (z : Extension (a : E)) :
    (rationalSignLift σ a ε z).re = σ z.re := rfl

@[simp] theorem rationalSignLift_im (σ : Gal(E/ℚ)) (a : ℚ)
    [Algebra ℚ (Extension (a : E))] (ε : ZMod 2) (z : Extension (a : E)) :
    (rationalSignLift σ a ε z).im = σ z.im*binarySign ε := rfl

@[simp] theorem rationalSignLift_algebraMap (σ : Gal(E/ℚ)) (a : ℚ)
    [Algebra ℚ (Extension (a : E))] (ε : ZMod 2) (x : E) :
    rationalSignLift σ a ε (algebraMap E (Extension (a : E)) x) =
      algebraMap E (Extension (a : E)) (σ x) := by
  ext <;> simp

@[simp] theorem rationalSignLift_root (σ : Gal(E/ℚ)) (a : ℚ)
    [Algebra ℚ (Extension (a : E))] (ε : ZMod 2) :
    rationalSignLift σ a ε omega =
      binarySign (E := E) ε • (omega : Extension (a : E)) := by
  ext <;> simp

/-- An actual involution on the base has an actual involutive sign lift. -/
theorem rationalSignLift_involutive (σ : Gal(E/ℚ)) (hσ : Function.Involutive σ)
    (a : ℚ) [Algebra ℚ (Extension (a : E))] (ε : ZMod 2) :
    Function.Involutive (rationalSignLift σ a ε) := by
  intro z
  apply QuadraticAlgebra.ext
  · change σ (σ z.re) = z.re
    exact hσ z.re
  · change σ (σ z.im*binarySign ε)*binarySign ε = z.im
    rw [map_mul,hσ]
    simp only [binarySign,map_intCast]
    rw [mul_assoc,← pow_two]
    change z.im * (binarySign ε)^2 = z.im
    rw [binarySign_sq,mul_one]

end UnitDistance.Multiquadratic
