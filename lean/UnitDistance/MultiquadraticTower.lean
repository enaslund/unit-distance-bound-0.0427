module

public import UnitDistance.KummerInvariantRadicand
public import Mathlib.Data.Rat.Sqrt

@[expose] public section
set_option backward.privateInPublic true


/-!
# Square classes in actual quadratic extensions

The coordinate identity for a square in `E(√a)` reduces rational
nonsquareness in an explicit multiquadratic tower to independently decidable
rational square tests. The extension and its basis are actual algebras.
-/

noncomputable section
namespace UnitDistance.Multiquadratic
open QuadraticAlgebra
variable {E : Type*} [Field E] [CharZero E]

/-- A base element is a square in the actual quadratic algebra exactly
when it or its quotient by the radicand is a square in the base field. -/
theorem isSquare_algebraMap_iff (a b : E) (ha : a ≠ 0) :
    IsSquare (algebraMap E (KummerInvariant.Extension a) b) ↔
      IsSquare b ∨ IsSquare (b/a) := by
  constructor
  · rintro ⟨z,hz⟩
    have hi := congrArg QuadraticAlgebra.im hz
    have hr := congrArg QuadraticAlgebra.re hz
    simp only [algebraMap_im,im_mul,zero_mul,add_zero] at hi
    simp only [algebraMap_re,re_mul] at hr
    have hxy : z.re*z.im = 0 := by
      have hh : z.re*z.im + z.re*z.im = 0 := by linear_combination -hi
      exact add_self_eq_zero.mp hh
    rcases mul_eq_zero.mp hxy with hx | hy
    · right
      refine ⟨z.im,?_⟩
      apply (div_eq_iff ha).mpr
      simpa [hx,mul_assoc,mul_comm,mul_left_comm] using hr
    · left
      exact ⟨z.re,by simpa [hy] using hr⟩
  · rintro (⟨x,hx⟩ | ⟨y,hy⟩)
    · refine ⟨⟨x,0⟩,?_⟩
      ext <;> simp [hx]
    · refine ⟨⟨0,y⟩,?_⟩
      ext
      · have hh := (div_eq_iff ha).mp hy
        simpa [mul_assoc,mul_comm,mul_left_comm] using hh
      · simp

/-- The rational-cast form keeps every recursive square test over `ℚ`. -/
theorem isSquare_ratCast_iff (a b : ℚ) (ha : a ≠ 0) :
    IsSquare (b : KummerInvariant.Extension (a : E)) ↔
      IsSquare (b : E) ∨ IsSquare ((b/a : ℚ) : E) := by
  have ha' : (a : E) ≠ 0 := by exact_mod_cast ha
  change IsSquare (algebraMap E (KummerInvariant.Extension (a : E)) (b : E)) ↔ _
  simpa using isSquare_algebraMap_iff (a : E) (b : E) ha'

/-- Adjoining a nonsquare rational radicand preserves Galoisness over `ℚ`;
every actual base automorphism lifts with multiplier one. -/
theorem isGalois_ratCast [NumberField E] [IsGalois ℚ E]
    (a : ℚ) [Fact (KummerInvariant.Nonsquare (a : E))] :
    IsGalois ℚ (KummerInvariant.Extension (a : E)) := by
  apply KummerInvariant.isGalois_of_invariant
  intro σ
  exact ⟨1,by simp⟩

end UnitDistance.Multiquadratic

namespace UnitDistance.Multiquadratic
variable {E : Type*} [Field E]

/-- The square predicate and the explicit nonsquare field condition agree. -/
theorem nonsquare_of_not_isSquare (a : E) (ha : ¬IsSquare a) :
    KummerInvariant.Nonsquare a := by
  intro x hx
  exact ha ⟨x,by simpa [pow_two] using hx.symm⟩

end UnitDistance.Multiquadratic
