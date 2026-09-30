module

public import UnitDistance.MultiquadraticTower

@[expose] public section
set_option backward.privateInPublic true


/-!
# Explicit sign lifts in rational quadratic towers

Every automorphism of the preceding field has two explicit lifts, according
to the sign of the newly adjoined rational square root. The direct-product
law is proved on actual quadratic-algebra coordinates.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.Multiquadratic
open QuadraticAlgebra KummerInvariant
variable {E : Type*} [Field E] [CharZero E]

/-- The independent integer sign attached to a binary exponent. -/
def binarySignInteger (ε : ZMod 2) : ℤ := if ε = 0 then 1 else -1

/-- The actual scalar sign attached to a binary exponent. -/
def binarySign (ε : ZMod 2) : E := (binarySignInteger ε : E)

@[simp] theorem binarySign_zero : binarySign (E := E) 0 = 1 := by
  simp [binarySign,binarySignInteger]

@[simp] theorem binarySign_sq (ε : ZMod 2) : (binarySign (E := E) ε)^2 = 1 := by
  have h : ∀ ε : ZMod 2, (binarySignInteger ε)^2 = 1 := by decide +kernel
  unfold binarySign
  exact_mod_cast h ε

@[simp] theorem binarySign_ne_zero (ε : ZMod 2) : binarySign (E := E) ε ≠ 0 := by
  have h : ∀ ε : ZMod 2, binarySignInteger ε ≠ 0 := by decide +kernel
  unfold binarySign
  exact_mod_cast h ε

@[simp] theorem map_binarySign (σ : Gal(E/ℚ)) (ε : ZMod 2) :
    σ (binarySign (E := E) ε) = binarySign ε := by simp [binarySign]

theorem binarySign_add (ε δ : ZMod 2) :
    binarySign (E := E) (ε+δ) = binarySign ε * binarySign δ := by
  have h : ∀ ε δ : ZMod 2,
      binarySignInteger (ε+δ) = binarySignInteger ε * binarySignInteger δ := by decide +kernel
  unfold binarySign
  exact_mod_cast h ε δ

theorem binarySign_injective : Function.Injective (binarySign (E := E)) := by
  have h : Function.Injective binarySignInteger := by decide +kernel
  intro ε δ he
  apply h
  unfold binarySign at he
  exact_mod_cast he

/-- The displayed square root has its defining square, in the actual algebra. -/
theorem root_sq (a : ℚ) :
    (omega : Extension (a : E))^2 = (a : Extension (a : E)) := by
  ext <;> simp [pow_two]

/-- Extend a base automorphism, specifying the actual sign of the new root. -/
def signLift (σ : Gal(E/ℚ)) (a : ℚ) (ε : ZMod 2) :
    Extension (a : E) ≃ₐ[ℚ] Extension (a : E) :=
  liftEquiv σ (a : E) (binarySign ε) (by simp) (binarySign_ne_zero ε)

@[simp] theorem signLift_re (σ : Gal(E/ℚ)) (a : ℚ) (ε : ZMod 2)
    (z : Extension (a : E)) : (signLift σ a ε z).re = σ z.re := rfl

@[simp] theorem signLift_im (σ : Gal(E/ℚ)) (a : ℚ) (ε : ZMod 2)
    (z : Extension (a : E)) : (signLift σ a ε z).im = σ z.im*binarySign ε := rfl

/-- The lift restricts to the actual base automorphism. -/
@[simp] theorem signLift_algebraMap (σ : Gal(E/ℚ)) (a : ℚ) (ε : ZMod 2) (x : E) :
    signLift σ a ε (algebraMap E (Extension (a : E)) x) =
      algebraMap E (Extension (a : E)) (σ x) := by
  ext <;> simp

/-- The lift has the specified actual sign on the new square root. -/
@[simp] theorem signLift_root (σ : Gal(E/ℚ)) (a : ℚ) (ε : ZMod 2) :
    signLift σ a ε omega = (binarySign (E := E) ε) • (omega : Extension (a : E)) := by
  ext <;> simp

/-- The explicit lifts obey the direct-product group law. -/
def signLiftHom (a : ℚ) :
    (Gal(E/ℚ) × Multiplicative (ZMod 2)) →* (Extension (a : E) ≃ₐ[ℚ] Extension (a : E)) where
  toFun g := signLift g.1 a g.2.toAdd
  map_one' := by
    ext z : 1
    apply QuadraticAlgebra.ext <;> simp
  map_mul' g h := by
    ext z : 1
    apply QuadraticAlgebra.ext
    · rfl
    · change (g.1*h.1) z.im * binarySign (g.2.toAdd+h.2.toAdd) =
        g.1 (h.1 z.im*binarySign h.2.toAdd)*binarySign g.2.toAdd
      rw [AlgEquiv.mul_apply,map_mul,map_binarySign,binarySign_add]
      ring

/-- Different base automorphisms or signs give different actual lifts. -/
theorem signLiftHom_injective (a : ℚ) : Function.Injective (signLiftHom (E := E) a) := by
  intro g h he
  have hbase : g.1 = h.1 := by
    ext x
    exact congrArg QuadraticAlgebra.re
      (AlgEquiv.congr_fun he (algebraMap E (Extension (a : E)) x))
  have hsign : binarySign (E := E) g.2.toAdd = binarySign h.2.toAdd := by
    simpa only [signLiftHom,MonoidHom.coe_mk,OneHom.coe_mk,signLift_im,omega_im,map_one,one_mul]
      using congrArg QuadraticAlgebra.im (AlgEquiv.congr_fun he omega)
  apply Prod.ext hbase
  exact Multiplicative.toAdd.injective (binarySign_injective hsign)

/-- For an actual Galois number field and nonsquare rational radicand,
these explicit lifts give the entire actual Galois group. -/
def signLiftEquiv [NumberField E] [IsGalois ℚ E]
    (a : ℚ) [Fact (Nonsquare (a : E))] :
    (Gal(E/ℚ) × Multiplicative (ZMod 2)) ≃* Gal(Extension (a : E)/ℚ) := by
  letI := isGalois_ratCast (E := E) a
  apply MulEquiv.ofBijective (signLiftHom a)
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨signLiftHom_injective a,?_⟩
  rw [Nat.card_prod,IsGalois.card_aut_eq_finrank ℚ E,
    IsGalois.card_aut_eq_finrank ℚ (Extension (a : E)),KummerInvariant.absolute_finrank]
  simp [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card, mul_comm]

end UnitDistance.Multiquadratic

namespace UnitDistance.Multiquadratic
open QuadraticAlgebra KummerInvariant
variable {E : Type*} [Field E] [CharZero E]

/-- An involutive base automorphism has involutive rational sign lifts. -/
theorem signLift_involutive (σ : Gal(E/ℚ)) (hσ : Function.Involutive σ)
    (a : ℚ) (ε : ZMod 2) : Function.Involutive (signLift σ a ε) := by
  intro z
  apply QuadraticAlgebra.ext
  · change σ (σ z.re) = z.re
    exact hσ z.re
  · change σ (σ z.im*binarySign ε)*binarySign ε = z.im
    rw [map_mul,hσ,map_binarySign,mul_assoc,← pow_two,binarySign_sq,mul_one]

end UnitDistance.Multiquadratic

namespace UnitDistance.Multiquadratic
open scoped BigOperators
variable {E : Type*} [Field E] [CharZero E]

/-- The scalar sign of a finite sum is the product of its scalar signs. -/
theorem binarySign_sum {ι : Type*} (s : Finset ι) (v : ι → ZMod 2) :
    binarySign (E := E) (∑ i ∈ s, v i) = ∏ i ∈ s, binarySign (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi,ih,binarySign_add]

end UnitDistance.Multiquadratic
