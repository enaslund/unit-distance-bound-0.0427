module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.Algebra.QuadraticAlgebra.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.GCongr

@[expose] public section
set_option backward.privateInPublic true


/-!
# Integer polynomials as coefficient lists

`horner L z` evaluates the integer polynomial with coefficient list `L` (constant
term first) at `z` in any commutative ring, by Horner's rule; `hornerD L z`
evaluates its formal derivative. Both commute with ring homomorphisms, and a
list ending in `1` gives a monic polynomial. These are used to transport
kernel-checked identities from an explicit model ring to a number field, and
to feed explicit monic relations to `aeval_derivative_mem_differentIdeal`.

`quadLift ψ a u hu` extends a ring homomorphism `ψ : R → A` to
`QuadraticAlgebra R a 0` by sending the generator to `u`, when `u² = ψ a`.
-/

noncomputable section
open Polynomial

namespace UnitDistance.Sqrt241.Discriminant

/-- Horner evaluation of an integer coefficient list (constant term first). -/
def horner {R : Type*} [CommRing R] : List ℤ → R → R
  | [], _ => 0
  | c :: cs, z => (c : R) + z * horner cs z

/-- Horner evaluation of the formal derivative of the coefficient list. -/
def hornerD {R : Type*} [CommRing R] : List ℤ → R → R
  | [], _ => 0
  | _ :: cs, z => horner cs z + z * hornerD cs z

@[simp] theorem horner_nil {R : Type*} [CommRing R] (z : R) : horner [] z = 0 := rfl

@[simp] theorem horner_cons {R : Type*} [CommRing R] (c : ℤ) (cs : List ℤ) (z : R) :
    horner (c :: cs) z = (c : R) + z * horner cs z := rfl

@[simp] theorem hornerD_nil {R : Type*} [CommRing R] (z : R) : hornerD [] z = 0 := rfl

@[simp] theorem hornerD_cons {R : Type*} [CommRing R] (c : ℤ) (cs : List ℤ) (z : R) :
    hornerD (c :: cs) z = horner cs z + z * hornerD cs z := rfl

theorem map_horner {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (L : List ℤ) (z : R) :
    φ (horner L z) = horner L (φ z) := by
  induction L with
  | nil => simp
  | cons c cs ih => simp [ih]

theorem map_hornerD {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (L : List ℤ)
    (z : R) : φ (hornerD L z) = hornerD L (φ z) := by
  induction L with
  | nil => simp
  | cons c cs ih => simp [ih, map_horner]

/-- The integer polynomial with coefficient list `L`. -/
def hornerPoly (L : List ℤ) : ℤ[X] := horner L X

theorem hornerPoly_cons (c : ℤ) (cs : List ℤ) :
    hornerPoly (c :: cs) = C c + X * hornerPoly cs := by
  simp [hornerPoly]

theorem aeval_hornerPoly {A : Type*} [CommRing A] (L : List ℤ) (z : A) :
    aeval z (hornerPoly L) = horner L z := by
  have h := map_horner (aeval z : ℤ[X] →ₐ[ℤ] A).toRingHom L X
  simpa [hornerPoly] using h

theorem aeval_derivative_hornerPoly {A : Type*} [CommRing A] (L : List ℤ) (z : A) :
    aeval z (derivative (hornerPoly L)) = hornerD L z := by
  induction L with
  | nil => simp [hornerPoly]
  | cons c cs ih =>
    rw [hornerPoly_cons, derivative_add, derivative_C, zero_add, derivative_mul,
      derivative_X, one_mul, map_add, map_mul, aeval_X, ih, aeval_hornerPoly, hornerD_cons]

theorem hornerPoly_monic (L : List ℤ) : (hornerPoly (L ++ [1])).Monic := by
  induction L with
  | nil => simp [hornerPoly]
  | cons c cs ih =>
    rw [List.cons_append, hornerPoly_cons]
    have hXq : (X * hornerPoly (cs ++ [1])).Monic := monic_X.mul ih
    apply hXq.add_of_right
    calc degree (C c) ≤ 0 := degree_C_le
      _ < 1 := by norm_num
      _ ≤ degree (X * hornerPoly (cs ++ [1])) := by
        rw [degree_mul, degree_X]
        have : 0 ≤ degree (hornerPoly (cs ++ [1])) := zero_le_degree_iff.mpr ih.ne_zero
        calc (1 : WithBot ℕ) = 1 + 0 := by norm_num
          _ ≤ 1 + degree (hornerPoly (cs ++ [1])) := by gcongr

/-- A root of a monic integer coefficient list is integral over `ℤ`. -/
theorem isIntegral_of_horner {A : Type*} [CommRing A] (L : List ℤ) (z : A)
    (h : horner (L ++ [1]) z = 0) : IsIntegral ℤ z :=
  ⟨hornerPoly (L ++ [1]), hornerPoly_monic L, by
    rw [← aeval_def, aeval_hornerPoly, h]⟩

/-- Adjoining a square root: `x + y ω ↦ ψ x + ψ y u` when `u² = ψ a`. -/
def quadLift {R A : Type*} [CommRing R] [CommRing A] (ψ : R →+* A) (a : R) (u : A)
    (hu : u * u = ψ a) : QuadraticAlgebra R a 0 →+* A where
  toFun z := ψ z.re + ψ z.im * u
  map_one' := by simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  map_mul' z w := by
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, map_add, map_mul,
      zero_mul, add_zero]
    linear_combination (-(ψ z.im * ψ w.im)) * hu
  map_zero' := by simp
  map_add' z w := by
    simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add, map_add]
    ring

theorem quadLift_apply {R A : Type*} [CommRing R] [CommRing A] (ψ : R →+* A) (a : R) (u : A)
    (hu : u * u = ψ a) (z : QuadraticAlgebra R a 0) :
    quadLift ψ a u hu z = ψ z.re + ψ z.im * u := rfl

theorem quadLift_mk {R A : Type*} [CommRing R] [CommRing A] (ψ : R →+* A) (a : R) (u : A)
    (hu : u * u = ψ a) (x y : R) :
    quadLift ψ a u hu ⟨x, y⟩ = ψ x + ψ y * u := rfl

end UnitDistance.Sqrt241.Discriminant
