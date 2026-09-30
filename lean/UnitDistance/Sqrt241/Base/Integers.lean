module

public import UnitDistance.Sqrt241.Base.Field
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section
set_option backward.privateInPublic true

/-!
# The ring of integers of `B = ℚ(√241)`

`𝓞 B = ℤ[ω]` with `ω = (1 + √241)/2`, `ω² = ω + 60`, and `disc B = 241`.
Elements are written `mk m n = m + n ω`; the norm is `m² + mn - 60 n²`.
This module names the eight Kummer radicands of `CanonicalGenus` as algebraic
integers (`alpha i`), the fundamental unit `ε` (`eps`, `epsUnit`, norm `-1`),
generators `pi2, pi2', pi3, pi3', pi5, pi5'` of the primes above `2, 3, 5`
(PARI's `idealprimedec` order) and `pi29, pi29'` for the primes above `29`,
and proves their norms and product relations.
-/

noncomputable section

namespace UnitDistance.Sqrt241.Base

open CanonicalGenus IntermediateField NumberField

theorem prime_241 : Nat.Prime 241 := by norm_num

theorem squarefree_241 : Squarefree (241 : ℤ).natAbs :=
  prime_241.prime.squarefree

theorem sqrt241_sq_int : sqrt241 ^ 2 = algebraMap ℚ B ((241 : ℤ) : ℚ) := by
  rw [sqrt241_sq]
  simp

/-- `ω = (1 + √241)/2`, the generator of `𝓞 B` over `ℤ`. -/
def omega : 𝓞 B :=
  ClassFieldTower.Sawin.quadraticHalfIntegerGenerator B 241 sqrt241 sqrt241_sq_int (by norm_num)

@[simp] theorem coe_omega : ((omega : 𝓞 B) : B) = (1 + sqrt241) / 2 :=
  ClassFieldTower.Sawin.coe_quadraticHalfIntegerGenerator B 241 sqrt241 sqrt241_sq_int _

/-- The integral basis `1, ω` of `𝓞 B`. -/
def integralBasis : Module.Basis (Fin 2) ℤ (𝓞 B) :=
  ClassFieldTower.Sawin.quadraticIntegerBasisOfModFourEqOne B 241 squarefree_241 sqrt241
    sqrt241_sq_int adjoin_sqrt241_eq_top (by norm_num)

@[simp] theorem integralBasis_zero : integralBasis 0 = 1 :=
  ClassFieldTower.Sawin.quadraticIntegerBasisOfModFourEqOne_apply_zero _ _ _ _ _ _ _

@[simp] theorem integralBasis_one : integralBasis 1 = omega :=
  ClassFieldTower.Sawin.quadraticIntegerBasisOfModFourEqOne_apply_one _ _ _ _ _ _ _

/-- The discriminant of `B` is `241`. -/
theorem discr_eq : NumberField.discr B = 241 :=
  ClassFieldTower.Sawin.numberField_discr_of_mod_four_eq_one B 241 squarefree_241 sqrt241
    sqrt241_sq_int adjoin_sqrt241_eq_top (by norm_num)

/-! ## Coercion `𝓞 B → B` -/

theorem coe_mul (x y : 𝓞 B) : ((x * y : 𝓞 B) : B) = (x : B) * (y : B) := map_mul _ x y

theorem coe_pow (x : 𝓞 B) (n : ℕ) : ((x ^ n : 𝓞 B) : B) = (x : B) ^ n := map_pow _ x n

theorem coe_ne_zero {x : 𝓞 B} (hx : x ≠ 0) : (x : B) ≠ 0 := by
  rwa [Ne, RingOfIntegers.coe_eq_zero_iff]

/-! ## Coordinates in the basis `1, ω` -/

/-- The algebraic integer `m + n ω`. -/
def mk (m n : ℤ) : 𝓞 B := m + n * omega

theorem coe_mk (m n : ℤ) :
    ((mk m n : 𝓞 B) : B) =
      algebraMap ℚ B ((m : ℚ) + (n : ℚ) / 2) + algebraMap ℚ B ((n : ℚ) / 2) * sqrt241 := by
  simp only [mk, map_add, map_mul, map_intCast, coe_omega, map_div₀, map_ofNat]
  ring

theorem omega_mul_omega : omega * omega = omega + 60 := by
  apply RingOfIntegers.ext
  simp only [map_mul, map_add, coe_omega, map_ofNat]
  linear_combination (1 / 4 : B) * sqrt241_sq

theorem exists_mk (x : 𝓞 B) : ∃ m n : ℤ, x = mk m n := by
  obtain ⟨m, n, h⟩ := ClassFieldTower.Sawin.exists_int_linear_combination_of_half_quadraticGenerator
    B 241 squarefree_241 sqrt241 sqrt241_sq_int adjoin_sqrt241_eq_top x
  refine ⟨m, n, RingOfIntegers.ext ?_⟩
  rw [h]
  simp [mk]

theorem mk_inj {m n m' n' : ℤ} : mk m n = mk m' n' ↔ m = m' ∧ n = n' := by
  constructor
  · intro h
    have h' := congrArg (fun x : 𝓞 B ↦ (x : B)) h
    simp only [coe_mk] at h'
    obtain ⟨h1, h2⟩ := coords_injective h'
    have hn : n = n' := by exact_mod_cast (by linarith : (n : ℚ) = n')
    subst hn
    exact ⟨by exact_mod_cast (by linarith : (m : ℚ) = m'), rfl⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem mk_add (a b c d : ℤ) : mk a b + mk c d = mk (a + c) (b + d) := by
  simp only [mk]
  push_cast
  ring

theorem mk_neg (a b : ℤ) : -mk a b = mk (-a) (-b) := by
  simp only [mk]
  push_cast
  ring

theorem mk_sub (a b c d : ℤ) : mk a b - mk c d = mk (a - c) (b - d) := by
  simp only [mk]
  push_cast
  ring

theorem mk_mul (a b c d : ℤ) :
    mk a b * mk c d = mk (a * c + 60 * b * d) (a * d + b * c + b * d) := by
  simp only [mk]
  push_cast
  linear_combination ((b : 𝓞 B) * d) * omega_mul_omega

theorem mk_zero_zero : mk 0 0 = 0 := by simp [mk]

theorem mk_intCast (m : ℤ) : mk m 0 = (m : 𝓞 B) := by simp [mk]

theorem mk_one_zero : mk 1 0 = 1 := by simp [mk]

theorem mk_zero_one : mk 0 1 = omega := by simp [mk]

theorem mk_ofNat (m : ℕ) [m.AtLeastTwo] : mk (OfNat.ofNat m) 0 = (OfNat.ofNat m : 𝓞 B) := by
  simp [mk]

/-- The norm of `m + n ω` is `m² + mn - 60 n²`. -/
theorem norm_mk (m n : ℤ) : Algebra.norm ℤ (mk m n) = m ^ 2 + m * n - 60 * n ^ 2 := by
  apply Int.cast_injective (α := ℚ)
  rw [Algebra.coe_norm_int, coe_mk, norm_coords]
  push_cast
  ring

/-! ## The Galois conjugation on `𝓞 B` -/

/-- The conjugation `σ` restricted to `𝓞 B`. -/
def sigmaInt : 𝓞 B ≃+* 𝓞 B := RingOfIntegers.mapRingEquiv (sigma : B ≃+* B)

@[simp] theorem coe_sigmaInt (x : 𝓞 B) : ((sigmaInt x : 𝓞 B) : B) = sigma (x : B) := rfl

theorem sigmaInt_mk (m n : ℤ) : sigmaInt (mk m n) = mk (m + n) (-n) := by
  apply RingOfIntegers.ext
  rw [coe_sigmaInt, coe_mk, coe_mk, sigma_coords]
  simp only [map_add, map_div₀, map_intCast, map_ofNat]
  push_cast
  ring

theorem mul_sigmaInt (x : 𝓞 B) : x * sigmaInt x = (Algebra.norm ℤ x : 𝓞 B) := by
  apply RingOfIntegers.ext
  simp only [map_mul, coe_sigmaInt, mul_sigma_eq_norm, map_intCast]
  rw [← Algebra.coe_norm_int]
  simp

/-! ## Named elements -/

/-- `√241 = 2ω - 1` as an algebraic integer. -/
def sqrt241Int : 𝓞 B := mk (-1) 2

@[simp] theorem coe_sqrt241Int : ((sqrt241Int : 𝓞 B) : B) = sqrt241 := by
  rw [sqrt241Int, coe_mk]
  norm_num

/-- The fundamental unit `ε = -71011068 + 4574225√241` (norm `-1`). -/
def eps : 𝓞 B := mk (-75585293) 9148450

/-- `ε⁻¹ = -σ(ε) = 71011068 + 4574225√241`. -/
def epsInv : 𝓞 B := mk 66436843 9148450

/-- The generator `(-6101 - 393√241)/2` of the first prime above `2` (norm `-2`). -/
def pi2 : 𝓞 B := mk (-2854) (-393)

/-- The generator `(6101 - 393√241)/2` of the second prime above `2` (norm `-2`). -/
def pi2' : 𝓞 B := mk 3247 (-393)

/-- The generator `31 - 2√241` of the first prime above `3` (norm `-3`). -/
def pi3 : 𝓞 B := mk 33 (-4)

/-- The generator `31 + 2√241` of the second prime above `3` (norm `-3`). -/
def pi3' : 𝓞 B := mk 29 4

/-- The generator `326 - 21√241` of the first prime above `5` (norm `-5`). -/
def pi5 : 𝓞 B := mk 347 (-42)

/-- The generator `326 + 21√241` of the second prime above `5` (norm `-5`). -/
def pi5' : 𝓞 B := mk 305 42

/-- The generator `-14127 + 910√241` of the first prime above `29` (norm `29`). -/
def pi29 : 𝓞 B := mk (-15037) 1820

/-- The generator `-14127 - 910√241` of the second prime above `29` (norm `29`). -/
def pi29' : 𝓞 B := mk (-13217) (-1820)

theorem coe_eps : ((eps : 𝓞 B) : B) =
    algebraMap ℚ B (-71011068) + algebraMap ℚ B 4574225 * sqrt241 := by
  rw [eps, coe_mk]; norm_num

theorem coe_epsInv : ((epsInv : 𝓞 B) : B) =
    algebraMap ℚ B 71011068 + algebraMap ℚ B 4574225 * sqrt241 := by
  rw [epsInv, coe_mk]; norm_num

theorem coe_pi2 : ((pi2 : 𝓞 B) : B) =
    algebraMap ℚ B (-6101 / 2) + algebraMap ℚ B (-393 / 2) * sqrt241 := by
  rw [pi2, coe_mk]; norm_num

theorem coe_pi2' : ((pi2' : 𝓞 B) : B) =
    algebraMap ℚ B (6101 / 2) + algebraMap ℚ B (-393 / 2) * sqrt241 := by
  rw [pi2', coe_mk]; norm_num

theorem coe_pi3 : ((pi3 : 𝓞 B) : B) =
    algebraMap ℚ B 31 + algebraMap ℚ B (-2) * sqrt241 := by
  rw [pi3, coe_mk]; norm_num

theorem coe_pi3' : ((pi3' : 𝓞 B) : B) =
    algebraMap ℚ B 31 + algebraMap ℚ B 2 * sqrt241 := by
  rw [pi3', coe_mk]; norm_num

theorem coe_pi5 : ((pi5 : 𝓞 B) : B) =
    algebraMap ℚ B 326 + algebraMap ℚ B (-21) * sqrt241 := by
  rw [pi5, coe_mk]; norm_num

theorem coe_pi5' : ((pi5' : 𝓞 B) : B) =
    algebraMap ℚ B 326 + algebraMap ℚ B 21 * sqrt241 := by
  rw [pi5', coe_mk]; norm_num

theorem coe_pi29 : ((pi29 : 𝓞 B) : B) =
    algebraMap ℚ B (-14127) + algebraMap ℚ B 910 * sqrt241 := by
  rw [pi29, coe_mk]; norm_num

theorem coe_pi29' : ((pi29' : 𝓞 B) : B) =
    algebraMap ℚ B (-14127) + algebraMap ℚ B (-910) * sqrt241 := by
  rw [pi29', coe_mk]; norm_num

theorem norm_eps : Algebra.norm ℤ eps = -1 := by rw [eps, norm_mk]; norm_num
theorem norm_pi2 : Algebra.norm ℤ pi2 = -2 := by rw [pi2, norm_mk]; norm_num
theorem norm_pi2' : Algebra.norm ℤ pi2' = -2 := by rw [pi2', norm_mk]; norm_num
theorem norm_pi3 : Algebra.norm ℤ pi3 = -3 := by rw [pi3, norm_mk]; norm_num
theorem norm_pi3' : Algebra.norm ℤ pi3' = -3 := by rw [pi3', norm_mk]; norm_num
theorem norm_pi5 : Algebra.norm ℤ pi5 = -5 := by rw [pi5, norm_mk]; norm_num
theorem norm_pi5' : Algebra.norm ℤ pi5' = -5 := by rw [pi5', norm_mk]; norm_num
theorem norm_pi29 : Algebra.norm ℤ pi29 = 29 := by rw [pi29, norm_mk]; norm_num
theorem norm_pi29' : Algebra.norm ℤ pi29' = 29 := by rw [pi29', norm_mk]; norm_num
theorem norm_sqrt241Int : Algebra.norm ℤ sqrt241Int = -241 := by
  rw [sqrt241Int, norm_mk]; norm_num

theorem eps_mul_epsInv : eps * epsInv = 1 := by
  rw [eps, epsInv, mk_mul, ← mk_one_zero, mk_inj]; norm_num

theorem pi2_mul_pi2' : pi2 * pi2' = 2 := by
  rw [pi2, pi2', mk_mul, ← mk_ofNat, mk_inj]; norm_num

theorem pi3_mul_pi3' : pi3 * pi3' = -3 := by
  rw [pi3, pi3', mk_mul, show (-3 : 𝓞 B) = mk (-3) 0 by simp [mk], mk_inj]; norm_num

theorem pi5_mul_pi5' : pi5 * pi5' = -5 := by
  rw [pi5, pi5', mk_mul, show (-5 : 𝓞 B) = mk (-5) 0 by simp [mk], mk_inj]; norm_num

theorem pi29_mul_pi29' : pi29 * pi29' = 29 := by
  rw [pi29, pi29', mk_mul, ← mk_ofNat, mk_inj]; norm_num

theorem sqrt241Int_mul_self : sqrt241Int * sqrt241Int = 241 := by
  rw [sqrt241Int, mk_mul, ← mk_ofNat, mk_inj]; norm_num

theorem sigmaInt_eps : sigmaInt eps = -epsInv := by
  rw [eps, epsInv, sigmaInt_mk, mk_neg, mk_inj]; norm_num

theorem sigmaInt_pi2 : sigmaInt pi2 = -pi2' := by
  rw [pi2, pi2', sigmaInt_mk, mk_neg, mk_inj]; norm_num

theorem sigmaInt_pi3 : sigmaInt pi3 = pi3' := by
  rw [pi3, pi3', sigmaInt_mk, mk_inj]; norm_num

theorem sigmaInt_pi5 : sigmaInt pi5 = pi5' := by
  rw [pi5, pi5', sigmaInt_mk, mk_inj]; norm_num

theorem sigmaInt_pi2' : sigmaInt pi2' = -pi2 := by
  rw [pi2, pi2', sigmaInt_mk, mk_neg, mk_inj]; norm_num

theorem sigmaInt_pi3' : sigmaInt pi3' = pi3 := by
  rw [pi3, pi3', sigmaInt_mk, mk_inj]; norm_num

theorem sigmaInt_pi5' : sigmaInt pi5' = pi5 := by
  rw [pi5, pi5', sigmaInt_mk, mk_inj]; norm_num

theorem sigmaInt_pi29' : sigmaInt pi29' = pi29 := by
  rw [pi29, pi29', sigmaInt_mk, mk_inj]; norm_num

theorem sigmaInt_pi29 : sigmaInt pi29 = pi29' := by
  rw [pi29, pi29', sigmaInt_mk, mk_inj]; norm_num

/-- `ε` as a unit of `𝓞 B`. -/
def epsUnit : (𝓞 B)ˣ where
  val := eps
  inv := epsInv
  val_inv := eps_mul_epsInv
  inv_val := by rw [mul_comm, eps_mul_epsInv]

@[simp] theorem coe_epsUnit : ((epsUnit : (𝓞 B)ˣ) : 𝓞 B) = eps := rfl

/-- `ε · σ(ε) = -1`. -/
theorem eps_mul_sigmaInt_eps : eps * sigmaInt eps = -1 := by
  rw [sigmaInt_eps, mul_neg, eps_mul_epsInv]

/-! ## The eight Kummer radicands -/

/-- The eight Kummer radicands `-1, ε, π₂, π₂', π₃, π₃', π₅, π₅'` as algebraic integers,
in the order of `CanonicalGenus.radicand`. -/
def alpha : Fin 8 → 𝓞 B := ![-1, eps, pi2, pi2', pi3, pi3', pi5, pi5']

theorem alpha_coords (i : Fin 8) : ((alpha i : 𝓞 B) : B) =
    algebraMap ℚ B (radicandA i) + algebraMap ℚ B (radicandB i) * sqrt241 := by
  fin_cases i
  · simp [alpha, radicandA, radicandB]
  · simpa [alpha, radicandA, radicandB] using coe_eps
  · simpa [alpha, radicandA, radicandB] using coe_pi2
  · simpa [alpha, radicandA, radicandB] using coe_pi2'
  · simpa [alpha, radicandA, radicandB] using coe_pi3
  · simpa [alpha, radicandA, radicandB] using coe_pi3'
  · simpa [alpha, radicandA, radicandB] using coe_pi5
  · simpa [alpha, radicandA, radicandB] using coe_pi5'

/-- The integral radicands map to the radicands of `CanonicalGenus` in the closure. -/
theorem coe_alpha (i : Fin 8) : (((alpha i : 𝓞 B) : B) : Closure) = radicand i := by
  rw [alpha_coords, radicand]
  simp

/-- The radicands of `CanonicalGenus` lie in `B`. -/
theorem radicand_mem_B (i : Fin 8) : radicand i ∈ B := by
  rw [← coe_alpha i]
  exact SetLike.coe_mem _

/-- Norms of the eight radicands: `1, -1, -2, -2, -3, -3, -5, -5`. -/
theorem norm_alpha : ∀ i : Fin 8, Algebra.norm ℤ (alpha i) = ![1, -1, -2, -2, -3, -3, -5, -5] i := by
  intro i
  fin_cases i
  · simp only [alpha, Fin.zero_eta, Matrix.cons_val_zero]
    rw [show (-1 : 𝓞 B) = mk (-1) 0 by simp [mk], norm_mk]
    norm_num
  · simpa [alpha] using norm_eps
  · simpa [alpha] using norm_pi2
  · simpa [alpha] using norm_pi2'
  · simpa [alpha] using norm_pi3
  · simpa [alpha] using norm_pi3'
  · simpa [alpha] using norm_pi5
  · simpa [alpha] using norm_pi5'

theorem alpha_ne_zero (i : Fin 8) : alpha i ≠ 0 := by
  intro h
  have := norm_alpha i
  rw [h, Algebra.norm_zero] at this
  fin_cases i <;> simp at this

end UnitDistance.Sqrt241.Base
