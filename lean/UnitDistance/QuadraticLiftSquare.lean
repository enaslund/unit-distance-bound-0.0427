module

public import UnitDistance.QuadraticSignLift

@[expose] public section
set_option backward.privateInPublic true


/-! The actual square of every lift on an actual quadratic radical.
The lift need not be the explicitly constructed lift: its possible sign
cancels on squaring, leaving precisely the twisted norm of the multiplier. -/
noncomputable section
namespace UnitDistance.Multiquadratic
universe u v
variable {E : Type u} [Field E] {L : Type v} [Field L] [Algebra E L]

/-- Every lift of a base automorphism has the same square action on a radical. -/
theorem square_on_root_of_twist (σ : E ≃+* E) (τ : L ≃+* L)
    (hres : ∀ a : E, τ (algebraMap E L a)=algebraMap E L (σ a))
    {a u : E} {x : L} (hx : x^2=algebraMap E L a)
    (hu : a*u^2=σ a) :
    τ (τ x)=algebraMap E L (u*σ u)*x := by
  have hs : (τ x)^2=(algebraMap E L u*x)^2 := by
    rw [← map_pow,hx,hres,← hu,map_mul,map_pow,mul_pow,hx]
    ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with h | h <;>
    simp only [h,map_mul,map_neg,hres] <;> ring

/-- The binary twisted norm is the actual sign of the squared lift. -/
theorem square_on_root_of_twisted_norm (σ : E ≃+* E) (τ : L ≃+* L)
    (hres : ∀ a : E, τ (algebraMap E L a)=algebraMap E L (σ a))
    {a u : E} {x : L} (hx : x^2=algebraMap E L a)
    (hu : a*u^2=σ a) (e : ZMod 2) (hn : u*σ u=binarySign e) :
    τ (τ x)=binarySign e*x := by
  rw [square_on_root_of_twist σ τ hres hx hu,hn]
  simp only [binarySign,map_intCast]

end UnitDistance.Multiquadratic
