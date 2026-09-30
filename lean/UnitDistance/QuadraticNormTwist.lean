module

public import UnitDistance.QuadraticSignLift
public import UnitDistance.KummerInvariantRadicand

@[expose] public section
set_option backward.privateInPublic true


/-! The norm-pair lift calculation with an arbitrary fixed coefficient x,
including genuinely p-adic coefficients. -/
noncomputable section
namespace UnitDistance.QuadraticNormTwist
open Multiquadratic
variable {K E : Type*} [Field K] [Field E] [CharZero E] [Algebra K E]

private theorem binarySign_one : binarySign (E:=E) 1=(-1 : E) := by
  simp [binarySign,binarySignInteger]

/-- Lift multiplier for the actual norm pair x±a. -/
def multiplier (x a b z : E) (ε : ZMod 2) : E :=
  if ε=0 then 1 else z*b/(x+a)

private theorem bits (ε : ZMod 2) : ε=0 ∨ ε=1 := by
  have h : ∀ ε : ZMod 2,ε=0 ∨ ε=1 := by decide
  exact h ε

theorem alpha_ne_zero (x a b z : E) (hb : b≠0) (hz : z≠0)
    (hn : (x+a)*(x-a)=b^2*z^2) : x+a≠0 := by
  intro h
  rw [h,zero_mul] at hn
  exact (mul_ne_zero (pow_ne_zero 2 hb) (pow_ne_zero 2 hz)) hn.symm

theorem twist (σ : Gal(E/K)) (x a b z : E) (ε : ZMod 2)
    (hb : b≠0) (hz : z≠0) (hn : (x+a)*(x-a)=b^2*z^2)
    (hx : σ x=x) (ha : σ a=binarySign ε*a) :
    (x+a)*(multiplier x a b z ε)^2=σ (x+a) := by
  rcases bits ε with rfl | rfl
  · simp [multiplier,map_add,hx,ha,binarySign,binarySignInteger]
  · have hα := alpha_ne_zero x a b z hb hz hn
    simp only [multiplier,one_ne_zero,if_false,map_add,hx,ha,binarySign_one,neg_one_mul]
    calc
      (x+a)*(z*b/(x+a))^2 = (b^2*z^2)/(x+a) := by field_simp
      _ = x+ -a := (div_eq_iff hα).mpr (by linear_combination -hn)

theorem twisted_norm (σ : Gal(E/K)) (x a b z : E) (ε δ : ZMod 2)
    (hb : b≠0) (hz : z≠0) (hn : (x+a)*(x-a)=b^2*z^2)
    (hx : σ x=x) (ha : σ a=binarySign ε*a)
    (hσb : σ b=binarySign δ*b) (hσz : σ z=z) :
    multiplier x a b z ε*σ (multiplier x a b z ε)=binarySign (ε*δ) := by
  rcases bits ε with rfl | rfl
  · simp [multiplier,binarySign_zero]
  · have hα := alpha_ne_zero x a b z hb hz hn
    have hα' : x-a≠0 := by
      intro h
      rw [h,mul_zero] at hn
      exact (mul_ne_zero (pow_ne_zero 2 hb) (pow_ne_zero 2 hz)) hn.symm
    simp only [multiplier,one_ne_zero,if_false,map_div₀,map_mul,map_add,hx,ha,
      binarySign_one,neg_one_mul,hσb,hσz,one_mul]
    rw [show x+ -a=x-a from (sub_eq_add_neg x a).symm]
    field_simp
    linear_combination -hn

end UnitDistance.QuadraticNormTwist
