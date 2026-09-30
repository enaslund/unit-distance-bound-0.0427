module

public import UnitDistance.Sqrt241.CanonicalGenus
public import UnitDistance.Sqrt241.Genus.Kummer
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Data.Rat.Sqrt

@[expose] public section
set_option backward.privateInPublic true


/-!
# The base field `B = ℚ(√241)` inside the fixed closure

Elements `x + y√241` of `B` are handled through Mathlib's
`QuadraticAlgebra ℚ 241 0` and its evaluation `ev` at the chosen root
`CanonicalGenus.baseRoot`.  `ev` is injective and its image is `ℚ⟮√241⟯`,
so identities in `B` are checked coordinatewise in `ℚ × ℚ`.

The eight Kummer radicands `radicand i = ev (radQ i)` have norms
`1, -1, -2, -2, -3, -3, -5, -5`, and their conjugates are, up to the factor
`-1` and inversion of `ε`, again radicands.
-/

noncomputable section
open IntermediateField

namespace UnitDistance.Sqrt241.Genus

open CanonicalGenus

/-- Rational quadratic numbers `x + y√241`. -/
abbrev Q241 := QuadraticAlgebra ℚ 241 0

theorem not_isSquare_241 : ¬ IsSquare (241 : ℚ) := by decide +kernel

instance fact_not_sq : Fact (∀ r : ℚ, r ^ 2 ≠ 241 + 0 * r) :=
  ⟨fun r h => not_isSquare_241 ⟨r, by rw [← sq, h]; ring⟩⟩

theorem baseRoot_mul_self :
    baseRoot * baseRoot = (241 : ℚ) • (1 : Closure) + (0 : ℚ) • baseRoot := by
  rw [← sq, baseRoot_sq]
  simp [Algebra.smul_def]

/-- Evaluation of `x + y√241` at the chosen square root. -/
def ev : Q241 →ₐ[ℚ] Closure := QuadraticAlgebra.lift ⟨baseRoot, baseRoot_mul_self⟩

theorem ev_apply (z : Q241) : ev z = (z.re : Closure) + (z.im : Closure) * baseRoot := by
  simp [ev, QuadraticAlgebra.lift_apply_apply, Algebra.smul_def]

theorem ev_mk (x y : ℚ) : ev ⟨x, y⟩ = (x : Closure) + (y : Closure) * baseRoot :=
  ev_apply _

theorem ev_injective : Function.Injective ev :=
  ev.toRingHom.injective

theorem ev_mem (z : Q241) : ev z ∈ ℚ⟮baseRoot⟯ := by
  rw [ev_apply]
  have hb : baseRoot ∈ ℚ⟮baseRoot⟯ := mem_adjoin_simple_self ℚ baseRoot
  exact add_mem (IntermediateField.algebraMap_mem _ _)
    (mul_mem (IntermediateField.algebraMap_mem _ _) hb)

theorem exists_ev_eq {w : Closure} (hw : w ∈ ℚ⟮baseRoot⟯) : ∃ z : Q241, ev z = w := by
  have halg : IsAlgebraic ℚ baseRoot := Algebra.IsAlgebraic.isAlgebraic baseRoot
  have hw' : w ∈ (ℚ⟮baseRoot⟯).toSubalgebra := hw
  rw [adjoin_simple_toSubalgebra_of_isAlgebraic halg,
    ← QuadraticAlgebra.range_lift baseRoot_mul_self] at hw'
  obtain ⟨z, hz⟩ := hw'
  exact ⟨z, hz⟩

/-- The eight radicands as rational quadratic numbers. -/
def radQ (i : Fin 8) : Q241 := ⟨radicandA i, radicandB i⟩

theorem radicand_eq_ev (i : Fin 8) : radicand i = ev (radQ i) := by
  rw [radicand, ev_mk]
  rfl

theorem radicand_mem (i : Fin 8) : radicand i ∈ ℚ⟮baseRoot⟯ := by
  rw [radicand_eq_ev]
  exact ev_mem _

/-- Norms of the radicands. -/
def normValue : Fin 8 → ℤ := ![1, -1, -2, -2, -3, -3, -5, -5]

theorem norm_radQ (i : Fin 8) : (radQ i).norm = (normValue i : ℚ) := by
  fin_cases i <;> simp [radQ, QuadraticAlgebra.norm_def, radicandA, radicandB, normValue] <;>
    norm_num

/-- The conjugate radicand `a - b√241`. -/
def conjRadicand (i : Fin 8) : Closure := ev (star (radQ i))

theorem conjRadicand_eq (i : Fin 8) :
    conjRadicand i = (radicandA i : Closure) - (radicandB i : Closure) * baseRoot := by
  rw [conjRadicand, radQ, QuadraticAlgebra.star_mk, ev_mk]
  push_cast
  ring

theorem radicand_mul_conj (i : Fin 8) : radicand i * conjRadicand i = (normValue i : Closure) := by
  rw [radicand_eq_ev, conjRadicand, ← map_mul, ← QuadraticAlgebra.algebraMap_norm_eq_mul_star,
    norm_radQ, AlgHom.commutes]
  simp

theorem radicand_ne_zero (i : Fin 8) : radicand i ≠ 0 := by
  intro h
  have := radicand_mul_conj i
  rw [h, zero_mul] at this
  fin_cases i <;> norm_num [normValue] at this

theorem genusRoot_ne_zero (i : Fin 8) : genusRoot i ≠ 0 := by
  intro h
  apply radicand_ne_zero i
  rw [← genusRoot_sq, h]
  ring

theorem baseRoot_ne_zero : baseRoot ≠ 0 := by
  intro h
  have := baseRoot_sq
  rw [h] at this
  norm_num at this

/-! ### Conjugation of the radicands -/

theorem conjRadicand_zero : conjRadicand 0 = radicand 0 := by
  rw [conjRadicand_eq, radicand]
  simp [radicandA, radicandB]

theorem conjRadicand_one : conjRadicand 1 * radicand 1 = -1 := by
  rw [mul_comm, radicand_mul_conj]
  simp [normValue]

theorem conjRadicand_two : conjRadicand 2 = -radicand 3 := by
  rw [conjRadicand_eq, radicand]
  simp [radicandA, radicandB]
  ring

theorem conjRadicand_three : conjRadicand 3 = -radicand 2 := by
  rw [conjRadicand_eq, radicand]
  simp [radicandA, radicandB]
  ring

theorem conjRadicand_four : conjRadicand 4 = radicand 5 := by
  rw [conjRadicand_eq, radicand]
  simp [radicandA, radicandB]

theorem conjRadicand_five : conjRadicand 5 = radicand 4 := by
  rw [conjRadicand_eq, radicand]
  simp [radicandA, radicandB]
  ring

theorem conjRadicand_six : conjRadicand 6 = radicand 7 := by
  rw [conjRadicand_eq, radicand]
  simp [radicandA, radicandB]

theorem conjRadicand_seven : conjRadicand 7 = radicand 6 := by
  rw [conjRadicand_eq, radicand]
  simp [radicandA, radicandB]
  ring

/-! ### Non-squares in `B` -/

/-- Kernel-checkable certificate that `∏_{i∈m} radicand i` is not a square in
`B`: its norm is not a rational square, or it is a rational number `r` with
neither `r` nor `r/241` a rational square. -/
def NonsquareCert (m : Finset (Fin 8)) : Prop :=
  ¬ IsSquare (∏ i ∈ m, radQ i).norm ∨
    ((∏ i ∈ m, radQ i).im = 0 ∧ ¬ IsSquare (∏ i ∈ m, radQ i).re ∧
      ¬ IsSquare ((∏ i ∈ m, radQ i).re / 241))

instance (m : Finset (Fin 8)) : Decidable (NonsquareCert m) := by
  unfold NonsquareCert
  infer_instance

theorem nonsquareCert_all : ∀ m : Finset (Fin 8), m.Nonempty → NonsquareCert m := by
  decide +kernel

theorem not_sq_of_cert {z : Q241} (h : ¬ IsSquare z.norm ∨
    (z.im = 0 ∧ ¬ IsSquare z.re ∧ ¬ IsSquare (z.re / 241))) (w : Q241) : w ^ 2 ≠ z := by
  intro hw
  rcases h with h | ⟨him, hre, hre'⟩
  · apply h
    refine ⟨w.norm, ?_⟩
    rw [← hw, map_pow, sq]
  · have hre2 : z.re = w.re * w.re + 241 * w.im * w.im := by
      rw [← hw, sq, QuadraticAlgebra.re_mul]
    have him2 : z.im = w.re * w.im + w.im * w.re := by
      rw [← hw, sq, QuadraticAlgebra.im_mul]
      ring
    rw [him] at him2
    have : w.re * w.im = 0 := by linarith
    rcases mul_eq_zero.1 this with h0 | h0
    · apply hre'
      refine ⟨w.im, ?_⟩
      rw [hre2, h0]
      ring
    · apply hre
      refine ⟨w.re, ?_⟩
      rw [hre2, h0]
      ring

/-- No nonempty product of radicands is a square in `B`. -/
theorem prod_radicand_not_sq (m : Finset (Fin 8)) (hm : m.Nonempty) :
    ∀ w ∈ ℚ⟮baseRoot⟯, w ^ 2 ≠ ∏ i ∈ m, radicand i := by
  intro w hw hsq
  obtain ⟨z, rfl⟩ := exists_ev_eq hw
  have hprod : ∏ i ∈ m, radicand i = ev (∏ i ∈ m, radQ i) := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun i _ => radicand_eq_ev i
  rw [hprod, ← map_pow] at hsq
  exact not_sq_of_cert (nonsquareCert_all m hm) z (ev_injective hsq)

end UnitDistance.Sqrt241.Genus
