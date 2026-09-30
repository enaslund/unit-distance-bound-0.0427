module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.Tactic

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual quadratic fields from invariant radicands

A norm identity supplies an explicit semilinear lift of a base automorphism
to the actual quadratic algebra. A nontrivial twisted norm obstructs the
radicand being a square. These are field identities, independent of assigned
quadratic forms or desired Galois-group orders.
-/

noncomputable section
namespace UnitDistance.KummerInvariant
open QuadraticAlgebra
variable {k E : Type*} [Field k] [Field E] [Algebra k E]

/-- The actual algebra obtained by adjoining a square root of `β`. -/
abbrev Extension (β : E) := QuadraticAlgebra E β 0

/-- A square radicand invariant up to `u²` has trivial twisted norm under
an involution. This is the elementary obstruction behind nonzero forms. -/
theorem twisted_norm_eq_one_of_square
    (σ : E ≃ₐ[k] E) (hσ : Function.Involutive σ)
    (β u s : E) (hs : s^2 = β) (hβ : β ≠ 0)
    (htwist : β*u^2 = σ β) : u*σ u = 1 := by
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs; exact hβ hs.symm
  have hsquare : (σ s)^2 = (s*u)^2 := by
    rw [← map_pow,hs,← htwist,mul_pow,hs]
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsquare with h | h
  · have hh := congrArg σ h
    rw [hσ s,map_mul,h] at hh
    apply (mul_left_cancel₀ hs0)
    simpa [mul_assoc] using hh.symm
  · have hh := congrArg σ h
    rw [hσ s,map_neg,map_mul,h,neg_mul,neg_neg] at hh
    apply (mul_left_cancel₀ hs0)
    simpa [mul_assoc] using hh.symm

/-- A nontrivial actual twisted norm proves that the actual radicand is
not a square, without a cohomological injectivity assumption. -/
theorem nonsquare_of_twisted_norm
    (σ : E ≃ₐ[k] E) (hσ : Function.Involutive σ)
    (β u : E) (hβ : β ≠ 0) (htwist : β*u^2 = σ β)
    (hnorm : u*σ u ≠ 1) : ∀ s : E, s^2 ≠ β := by
  intro s hs
  exact hnorm (twisted_norm_eq_one_of_square σ hσ β u s hs hβ htwist)

/-- The explicit semilinear ring map sends the new square root to `u√β`. -/
def liftHom (σ : E ≃ₐ[k] E) (β u : E) (htwist : β*u^2 = σ β) :
    Extension β →ₐ[k] Extension β where
  toFun z := ⟨σ z.re, σ z.im*u⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp
  map_add' z w := by ext <;> simp [add_mul]
  map_mul' z w := by
    ext <;> simp only [re_mul,im_mul,map_add,map_mul,map_zero,zero_mul,add_zero]
    · rw [← htwist]
      ring
    · ring
  commutes' r := by
    ext <;> simp [Algebra.algebraMap_eq_smul_one,AlgEquiv.commutes]

@[simp] theorem liftHom_re (σ : E ≃ₐ[k] E) (β u : E) (htwist : β*u^2 = σ β)
    (z : Extension β) : (liftHom σ β u htwist z).re = σ z.re := rfl

@[simp] theorem liftHom_im (σ : E ≃ₐ[k] E) (β u : E) (htwist : β*u^2 = σ β)
    (z : Extension β) : (liftHom σ β u htwist z).im = σ z.im*u := rfl

/-- The displayed semilinear map is an actual automorphism when `u ≠ 0`. -/
def liftEquiv (σ : E ≃ₐ[k] E) (β u : E) (htwist : β*u^2 = σ β) (hu : u ≠ 0) :
    Extension β ≃ₐ[k] Extension β :=
  AlgEquiv.ofBijective (liftHom σ β u htwist) ⟨by
    intro z w h
    apply QuadraticAlgebra.ext
    · exact σ.injective (congrArg QuadraticAlgebra.re h)
    · apply σ.injective
      exact mul_right_cancel₀ hu (congrArg QuadraticAlgebra.im h),by
    intro z
    refine ⟨⟨σ.symm z.re,σ.symm (z.im/u)⟩,?_⟩
    ext <;> simp [div_mul_cancel₀ _ hu]⟩

@[simp] theorem liftEquiv_re (σ : E ≃ₐ[k] E) (β u : E) (htwist : β*u^2 = σ β)
    (hu : u ≠ 0) (z : Extension β) : (liftEquiv σ β u htwist hu z).re = σ z.re := rfl

@[simp] theorem liftEquiv_im (σ : E ≃ₐ[k] E) (β u : E) (htwist : β*u^2 = σ β)
    (hu : u ≠ 0) (z : Extension β) : (liftEquiv σ β u htwist hu z).im = σ z.im*u := rfl

/-- Nonzero radicands force nonzero multipliers in the invariant identity. -/
theorem multiplier_ne_zero (σ : E ≃ₐ[k] E) (β u : E) (hβ : β ≠ 0)
    (htwist : β*u^2 = σ β) : u ≠ 0 := by
  intro hu
  apply hβ
  apply σ.injective
  simpa [hu] using htwist.symm

end UnitDistance.KummerInvariant

namespace UnitDistance.KummerInvariant
open QuadraticAlgebra
variable {k E : Type*} [Field k] [Field E] [Algebra k E]

/-- An independently stated nonsquareness predicate on the actual radicand. -/
def Nonsquare (β : E) : Prop := ∀ s : E, s^2 ≠ β

instance quadraticFieldCondition (β : E) [Fact (Nonsquare β)] :
    Fact (∀ r : E, r^2 ≠ β + 0*r) := ⟨by simpa [Nonsquare] using (Fact.out : Nonsquare β)⟩

/-- The actual quadratic field has its actual two-dimensional basis. -/
theorem relative_finrank (β : E) [Fact (Nonsquare β)] :
    Module.finrank E (Extension β) = 2 := QuadraticAlgebra.finrank_eq_two _ _

/-- A quadratic extension of an actual number field is an actual number field. -/
instance extensionNumberField [NumberField E] (β : E) [Fact (Nonsquare β)] :
    NumberField (Extension β) where
  to_finiteDimensional := Module.Finite.trans E (Extension β)

/-- The square-root sign change is an actual automorphism over the base. -/
def signChange (β : E) : Extension β ≃ₐ[k] Extension β :=
  liftEquiv (1 : Gal(E/k)) β (-1) (by simp) (by simp)

@[simp] theorem signChange_re (β : E) (z : Extension β) :
    (signChange (k := k) β z).re = z.re := rfl

@[simp] theorem signChange_im (β : E) (z : Extension β) :
    (signChange (k := k) β z).im = -z.im := by
  change z.im * (-1 : E) = -z.im
  ring

/-- Invariance of a nonsquare's actual squareclass constructs an actual
Galois quadratic extension over the given Galois base. -/
theorem isGalois_of_invariant [CharZero E] [Module.Finite k E] [IsGalois k E]
    (β : E) [Fact (Nonsquare β)]
    (hinvariant : ∀ σ : Gal(E/k), ∃ u : E, β*u^2 = σ β) :
    IsGalois k (Extension β) := by
  letI : Module.Finite k (Extension β) := Module.Finite.trans E (Extension β)
  have hβ : β ≠ 0 := by
    intro h
    exact (Fact.out : Nonsquare β) 0 (by simp [h])
  apply IsGalois.of_fixedField_eq_bot k (Extension β)
  apply le_antisymm
  · intro z hz
    have hfix := (IntermediateField.mem_fixedField_iff _ z).mp hz
    have hi := congrArg QuadraticAlgebra.im (hfix (signChange (k := k) β) (by trivial))
    have him : z.im = 0 := CharZero.neg_eq_self_iff.mp (by simpa using hi)
    have hr : z.re ∈ (⊥ : IntermediateField k E) := by
      apply (IsGalois.mem_bot_iff_fixed (F := k) z.re).mpr
      intro σ
      obtain ⟨u,hu⟩ := hinvariant σ
      have he := congrArg QuadraticAlgebra.re
        (hfix (liftEquiv σ β u hu (multiplier_ne_zero σ β u hβ hu)) (by trivial))
      exact he
    obtain ⟨r,hr⟩ := IntermediateField.mem_bot.mp hr
    apply IntermediateField.mem_bot.mpr
    refine ⟨r,?_⟩
    apply QuadraticAlgebra.ext
    · simpa [Algebra.algebraMap_eq_smul_one] using hr
    · simpa [Algebra.algebraMap_eq_smul_one] using him.symm
  · exact bot_le

/-- The actual absolute degree of the invariant quadratic extension doubles. -/
theorem absolute_finrank [Module.Finite k E] (β : E) [Fact (Nonsquare β)] :
    Module.finrank k (Extension β) = 2 * Module.finrank k E := by
  rw [← Module.finrank_mul_finrank k E (Extension β),relative_finrank,mul_comm]

/-- Its actual Galois group has the proved, rather than assigned, doubled order. -/
theorem card_galoisGroup [CharZero E] [Module.Finite k E] [IsGalois k E]
    (β : E) [Fact (Nonsquare β)]
    (hinvariant : ∀ σ : Gal(E/k), ∃ u : E, β*u^2 = σ β) :
    Nat.card (Gal(Extension β/k)) = 2 * Module.finrank k E := by
  letI : Module.Finite k (Extension β) := Module.Finite.trans E (Extension β)
  letI := isGalois_of_invariant (k := k) β hinvariant
  rw [IsGalois.card_aut_eq_finrank,absolute_finrank]

end UnitDistance.KummerInvariant

namespace UnitDistance.KummerInvariant
open QuadraticAlgebra
variable {k E : Type*} [Field k] [Field E] [Algebra k E]

/-- The square of an actual lifted involution is given by the actual twisted
norm, which is the quadratic extension-class computation. -/
theorem liftEquiv_square_coefficients
    (σ : E ≃ₐ[k] E) (hσ : Function.Involutive σ)
    (β u : E) (htwist : β*u^2 = σ β) (hu : u ≠ 0) (z : Extension β) :
    (((liftEquiv σ β u htwist hu)^2) z).re = z.re ∧
    (((liftEquiv σ β u htwist hu)^2) z).im = z.im*(u*σ u) := by
  constructor
  · change σ (σ z.re) = z.re
    exact hσ z.re
  · change σ (σ z.im*u)*u = z.im*(u*σ u)
    rw [map_mul,hσ]
    ring

/-- A twisted norm of minus one makes the lifted involution square to the
nontrivial square-root sign change. -/
theorem liftEquiv_sq_eq_signChange
    (σ : E ≃ₐ[k] E) (hσ : Function.Involutive σ)
    (β u : E) (htwist : β*u^2 = σ β) (hu : u ≠ 0) (hnorm : u*σ u = -1) :
    (liftEquiv σ β u htwist hu)^2 = signChange (k := k) β := by
  ext z : 1
  apply QuadraticAlgebra.ext
  · exact (liftEquiv_square_coefficients σ hσ β u htwist hu z).1
  · simpa [hnorm] using (liftEquiv_square_coefficients σ hσ β u htwist hu z).2

/-- A trivial twisted norm makes the lifted automorphism an involution. -/
theorem liftEquiv_sq_eq_one
    (σ : E ≃ₐ[k] E) (hσ : Function.Involutive σ)
    (β u : E) (htwist : β*u^2 = σ β) (hu : u ≠ 0) (hnorm : u*σ u = 1) :
    (liftEquiv σ β u htwist hu)^2 = 1 := by
  ext z : 1
  apply QuadraticAlgebra.ext
  · exact (liftEquiv_square_coefficients σ hσ β u htwist hu z).1
  · simpa [hnorm] using (liftEquiv_square_coefficients σ hσ β u htwist hu z).2

end UnitDistance.KummerInvariant
