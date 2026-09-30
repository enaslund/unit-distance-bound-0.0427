module

public import UnitDistance.Sqrt241.Base.SUnits

@[expose] public section
set_option backward.privateInPublic true

/-!
# Residue symbols of the radicands at the unramified primes `7` and `29`

At an unramified prime `𝔮` of `B` the Frobenius acts on `√α` according to
whether `α` is a square in the residue field. For the Kummer radicands:

* at the two primes above `29` (residue field `ZMod 29`): `frob29`, `frob29'`;
* at the inert prime `7` (residue field of order `49`): `frob7`;

with `1` meaning "not a square", matching the lines `cap29 1`, `cap29 2` and
`inert7` of `kummer241.gp`. At `7` squares are exhibited explicitly and
non-squares are detected through the norm: `N(α) ≡ N(y)² (mod 7)` if
`α ≡ y² (mod 7)`.
-/

noncomputable section

namespace UnitDistance.Sqrt241.Base

open NumberField Ideal

/-! ## The primes above `29` -/

/-- Non-square pattern of the radicands modulo `𝔭₂₉ = (π₂₉)`. -/
def frob29 : Fin 8 → ZMod 2 := ![0, 0, 1, 0, 0, 1, 1, 1]

/-- Non-square pattern of the radicands modulo `𝔭₂₉' = (π₂₉')`. -/
def frob29' : Fin 8 → ZMod 2 := ![0, 0, 0, 1, 1, 0, 1, 1]

theorem isSquare_res29_alpha (i : Fin 8) :
    (∃ t : ZMod 29, res29 (alpha i) = t * t) ↔ frob29 i = 0 := by
  rw [res29, evalHom_alpha]
  fin_cases i <;> decide

theorem isSquare_res29'_alpha (i : Fin 8) :
    (∃ t : ZMod 29, res29' (alpha i) = t * t) ↔ frob29' i = 0 := by
  rw [res29', evalHom_alpha]
  fin_cases i <;> decide

/-! ## The inert prime `7` -/

theorem isSquare_quotient_P7_iff (x : 𝓞 B) :
    IsSquare (Ideal.Quotient.mk P7 x) ↔ ∃ y : 𝓞 B, (7 : 𝓞 B) ∣ x - y * y := by
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨y, ?_⟩
    rw [← map_mul, Ideal.Quotient.eq] at hq
    rwa [P7, mem_span_singleton] at hq
  · rintro ⟨y, hy⟩
    refine ⟨Ideal.Quotient.mk P7 y, ?_⟩
    rw [← map_mul, Ideal.Quotient.eq, P7, mem_span_singleton]
    exact hy

/-- The norm modulo `7` only depends on the class modulo `7`. -/
theorem norm_mod_seven_congr {x x' : 𝓞 B} (h : (7 : 𝓞 B) ∣ x - x') :
    ((Algebra.norm ℤ x : ℤ) : ZMod 7) = ((Algebra.norm ℤ x' : ℤ) : ZMod 7) := by
  obtain ⟨a, b, rfl⟩ := exists_mk x
  obtain ⟨a', b', rfl⟩ := exists_mk x'
  rw [mk_sub, show (7 : 𝓞 B) = ((7 : ℤ) : 𝓞 B) by norm_cast, intCast_dvd_mk_iff] at h
  obtain ⟨⟨k, hk⟩, ⟨l, hl⟩⟩ := h
  rw [norm_mk, norm_mk, ZMod.intCast_eq_intCast_iff_dvd_sub]
  refine ⟨-(2 * a' * k + 7 * k ^ 2 + a' * l + b' * k + 7 * k * l - 120 * b' * l
    - 420 * l ^ 2), ?_⟩
  have ha : a = a' + 7 * k := by linarith
  have hb : b = b' + 7 * l := by linarith
  subst ha hb
  push_cast
  ring

theorem not_isSquare_mod_seven_of_norm {x : 𝓞 B}
    (h : ¬ ∃ t : ZMod 7, ((Algebra.norm ℤ x : ℤ) : ZMod 7) = t * t) :
    ¬ ∃ y : 𝓞 B, (7 : 𝓞 B) ∣ x - y * y := by
  rintro ⟨y, hy⟩
  apply h
  refine ⟨((Algebra.norm ℤ y : ℤ) : ZMod 7), ?_⟩
  rw [norm_mod_seven_congr hy, map_mul]
  push_cast
  ring

/-- Non-square pattern of the radicands modulo the inert prime `7`. -/
def frob7 : Fin 8 → ZMod 2 := ![0, 1, 1, 1, 0, 0, 0, 0]

private theorem seven_dvd_alpha_sub (i : Fin 8) (c d : ℤ)
    (h : (7 : ℤ) ∣ (alphaCoords i).1 - (c * c + 60 * d * d) ∧
      (7 : ℤ) ∣ (alphaCoords i).2 - (c * d + d * c + d * d)) :
    (7 : 𝓞 B) ∣ alpha i - mk c d * mk c d := by
  rw [alpha_eq_mk, mk_mul, mk_sub, show (7 : 𝓞 B) = ((7 : ℤ) : 𝓞 B) by norm_cast,
    intCast_dvd_mk_iff]
  convert h using 3

/-- Frobenius at `7`: `alpha i` is a square modulo `7` iff `frob7 i = 0`. -/
theorem isSquare_mod_seven_alpha (i : Fin 8) :
    (∃ y : 𝓞 B, (7 : 𝓞 B) ∣ alpha i - y * y) ↔ frob7 i = 0 := by
  have hns : ∀ i : Fin 8, ¬ (∃ t : ZMod 7,
      ((![1, -1, -2, -2, -3, -3, -5, -5] i : ℤ) : ZMod 7) = t * t) → frob7 i = 1 →
      ¬ ∃ y : 𝓞 B, (7 : 𝓞 B) ∣ alpha i - y * y := by
    intro i hi _
    apply not_isSquare_mod_seven_of_norm
    rw [norm_alpha]
    exact hi
  fin_cases i
  · exact ⟨fun _ ↦ rfl, fun _ ↦ ⟨mk 3 1, seven_dvd_alpha_sub 0 3 1 (by decide)⟩⟩
  · exact ⟨fun h ↦ absurd h (hns 1 (by decide) rfl), fun h ↦ absurd h (by decide)⟩
  · exact ⟨fun h ↦ absurd h (hns 2 (by decide) rfl), fun h ↦ absurd h (by decide)⟩
  · exact ⟨fun h ↦ absurd h (hns 3 (by decide) rfl), fun h ↦ absurd h (by decide)⟩
  · exact ⟨fun _ ↦ rfl, fun _ ↦ ⟨mk 1 1, seven_dvd_alpha_sub 4 1 1 (by decide)⟩⟩
  · exact ⟨fun _ ↦ rfl, fun _ ↦ ⟨mk 2 6, seven_dvd_alpha_sub 5 2 6 (by decide)⟩⟩
  · exact ⟨fun _ ↦ rfl, fun _ ↦ ⟨mk 2 0, seven_dvd_alpha_sub 6 2 0 (by decide)⟩⟩
  · exact ⟨fun _ ↦ rfl, fun _ ↦ ⟨mk 2 0, seven_dvd_alpha_sub 7 2 0 (by decide)⟩⟩

theorem isSquare_quotient_P7_alpha (i : Fin 8) :
    IsSquare (Ideal.Quotient.mk P7 (alpha i)) ↔ frob7 i = 0 := by
  rw [isSquare_quotient_P7_iff, isSquare_mod_seven_alpha]

end UnitDistance.Sqrt241.Base
