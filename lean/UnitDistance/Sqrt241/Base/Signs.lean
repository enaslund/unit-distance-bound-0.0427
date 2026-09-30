module

public import UnitDistance.Sqrt241.Base.Integers

@[expose] public section
set_option backward.privateInPublic true

/-!
# Signs of the Kummer radicands at the two real places

`v₁ = embPlus` (`√241 ↦ +√241`) and `v₂ = embMinus`. With `1` for negative,
the sign vectors of `(-1, ε, π₂, π₂', π₃, π₃', π₅, π₅')` are

* `v₁`: `1 0 1 1 1 0 1 0`,
* `v₂`: `1 1 0 0 0 1 0 1`,

matching the lines `c1`, `c2` of `kummer241.gp`. Several radicands are within
`10⁻⁸` of zero at one place; their signs follow from the norm
`embPlus x · embMinus x = N(x)` and the obvious sign at the other place.
-/

noncomputable section

namespace UnitDistance.Sqrt241.Base

open CanonicalGenus NumberField

theorem embPlus_mul_embMinus (x : B) :
    embPlus x * embMinus x = (Algebra.norm ℚ x : ℝ) := by
  rw [embMinus_apply, ← map_mul, mul_sigma_eq_norm, AlgHom.commutes]
  simp

theorem embPlus_mul_embMinus_int (x : 𝓞 B) :
    embPlus (x : B) * embMinus (x : B) = (Algebra.norm ℤ x : ℝ) := by
  rw [embPlus_mul_embMinus, ← Algebra.coe_norm_int]
  simp

theorem embPlus_alpha (i : Fin 8) :
    embPlus ((alpha i : 𝓞 B) : B) = radicandA i + radicandB i * Real.sqrt 241 := by
  rw [alpha_coords, embPlus_coords]

theorem embMinus_alpha (i : Fin 8) :
    embMinus ((alpha i : 𝓞 B) : B) = radicandA i - radicandB i * Real.sqrt 241 := by
  rw [alpha_coords, embMinus_coords]

/-- A real number whose product with a number of known sign is negative. -/
private theorem neg_of_mul_neg_of_pos {x y : ℝ} (h : x * y < 0) (hy : 0 < y) : x < 0 := by
  by_contra hx
  have hx' : 0 ≤ x := not_lt.mp hx
  nlinarith

private theorem pos_of_mul_neg_of_neg {x y : ℝ} (h : x * y < 0) (hy : y < 0) : 0 < x := by
  by_contra hx
  have hx' : x ≤ 0 := not_lt.mp hx
  nlinarith

private theorem norm_neg_of_alpha {i : Fin 8} (h : Algebra.norm ℤ (alpha i) < 0) :
    embPlus ((alpha i : 𝓞 B) : B) * embMinus ((alpha i : 𝓞 B) : B) < 0 := by
  rw [embPlus_mul_embMinus_int]
  exact_mod_cast h

private theorem norm_alpha_neg (i : Fin 8) (hi : i ≠ 0) : Algebra.norm ℤ (alpha i) < 0 := by
  rw [norm_alpha]
  fin_cases i <;> simp_all

/-- Sign vector of the radicands at `v₁ = embPlus` (`1` = negative). -/
def signPlus : Fin 8 → ZMod 2 := ![1, 0, 1, 1, 1, 0, 1, 0]

/-- Sign vector of the radicands at `v₂ = embMinus` (`1` = negative). -/
def signMinus : Fin 8 → ZMod 2 := ![1, 1, 0, 0, 0, 1, 0, 1]

/-- The radicands at `v₂` whose sign is obvious: `-1, ε` negative, `π₂, π₂', π₃, π₅` positive,
`π₃', π₅'` handled through the norm. -/
theorem embMinus_alpha_sign : ∀ i : Fin 8,
    (signMinus i = 1 → embMinus ((alpha i : 𝓞 B) : B) < 0) ∧
    (signMinus i = 0 → 0 < embMinus ((alpha i : 𝓞 B) : B)) := by
  have hs := sqrt_241_pos
  intro i
  fin_cases i
  · refine ⟨fun _ ↦ ?_, fun h ↦ absurd h (by decide)⟩
    rw [embMinus_alpha]; simp [radicandA, radicandB]
  · refine ⟨fun _ ↦ ?_, fun h ↦ absurd h (by decide)⟩
    rw [embMinus_alpha]; simp [radicandA, radicandB]; nlinarith
  · -- π₂: positive at `v₂`, via `π₂'` and the norm `2 > 0`
    refine ⟨fun h ↦ absurd h (by decide), fun _ ↦ ?_⟩
    have h2 : embPlus ((alpha 2 : 𝓞 B) : B) < 0 := by
      rw [embPlus_alpha]; simp [radicandA, radicandB]; nlinarith
    exact pos_of_mul_neg_of_neg (by
      rw [mul_comm]; exact norm_neg_of_alpha (norm_alpha_neg 2 (by decide))) h2
  · refine ⟨fun h ↦ absurd h (by decide), fun _ ↦ ?_⟩
    rw [embMinus_alpha]; simp [radicandA, radicandB]; nlinarith
  · refine ⟨fun h ↦ absurd h (by decide), fun _ ↦ ?_⟩
    rw [embMinus_alpha]; simp [radicandA, radicandB]; nlinarith
  · refine ⟨fun _ ↦ ?_, fun h ↦ absurd h (by decide)⟩
    have h2 : 0 < embPlus ((alpha 5 : 𝓞 B) : B) := by
      rw [embPlus_alpha]; simp [radicandA, radicandB]; nlinarith
    exact neg_of_mul_neg_of_pos (by
      rw [mul_comm]; exact norm_neg_of_alpha (norm_alpha_neg 5 (by decide))) h2
  · refine ⟨fun h ↦ absurd h (by decide), fun _ ↦ ?_⟩
    rw [embMinus_alpha]; simp [radicandA, radicandB]; nlinarith
  · refine ⟨fun _ ↦ ?_, fun h ↦ absurd h (by decide)⟩
    have h2 : 0 < embPlus ((alpha 7 : 𝓞 B) : B) := by
      rw [embPlus_alpha]; simp [radicandA, radicandB]; nlinarith
    exact neg_of_mul_neg_of_pos (by
      rw [mul_comm]; exact norm_neg_of_alpha (norm_alpha_neg 7 (by decide))) h2

/-- Signs at `v₁ = embPlus`: the radicand is negative iff `signPlus i = 1`. -/
theorem embPlus_alpha_sign : ∀ i : Fin 8,
    (signPlus i = 1 → embPlus ((alpha i : 𝓞 B) : B) < 0) ∧
    (signPlus i = 0 → 0 < embPlus ((alpha i : 𝓞 B) : B)) := by
  intro i
  by_cases h0 : i = 0
  · subst h0
    refine ⟨fun _ ↦ ?_, fun h ↦ absurd h (by decide)⟩
    rw [embPlus_alpha]; simp [radicandA, radicandB]
  · have hprod := norm_neg_of_alpha (norm_alpha_neg i h0)
    have hm := embMinus_alpha_sign i
    have hsum : signPlus i + signMinus i = 1 := by
      fin_cases i <;> simp_all [signPlus, signMinus]
    constructor
    · intro hp
      have hm0 : signMinus i = 0 := by rw [hp] at hsum; linear_combination hsum
      exact neg_of_mul_neg_of_pos hprod (hm.2 hm0)
    · intro hp
      have hm1 : signMinus i = 1 := by rw [hp, zero_add] at hsum; exact hsum
      exact pos_of_mul_neg_of_neg hprod (hm.1 hm1)

theorem embPlus_eps_pos : 0 < embPlus ((eps : 𝓞 B) : B) :=
  (embPlus_alpha_sign 1).2 (by decide)

theorem embMinus_eps_neg : embMinus ((eps : 𝓞 B) : B) < 0 :=
  (embMinus_alpha_sign 1).1 (by decide)

end UnitDistance.Sqrt241.Base
