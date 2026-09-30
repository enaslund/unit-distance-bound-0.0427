module

public import UnitDistance.Sqrt241.Genus.LocalTypes

@[expose] public section
set_option backward.privateInPublic true


/-!
# Exact local types of the canonical genus field at 2, 29 and 7

The analytic bridge only needs the upper bounds of `Genus.LocalTypes`.  Here
they are completed to the exact absolute types of the design:

* at 2, `(e, f) = (4, 2)`: `ζ₈ = (1 + √-1)/√2 ∈ E` and `2 = (1 - ζ₈)⁴ u` with
  `u` integral, so `2 ∈ P⁴` and `e ≥ 4`; the golden ratio `(1 + √5)/2 ∈ 𝓞 E`
  has no residue in `𝔽₂`, so `f ≥ 2`; with `f ∣ 2` and `e f ≤ 8` the type is
  `(4, 2)`;
* at 29, `(1, 2)`: `2` is not a square mod 29, so `√2` has no residue in `𝔽₂₉`;
* at 7, `(1, 4)`: `ε^24 ≡ -1 (mod 7)` in `ℚ(√241)` (ε is not a square in
  `𝔽₄₉`), so `√ε` has no residue in `𝔽₄₉`.
-/

noncomputable section
open NumberField

namespace UnitDistance.Sqrt241.Genus

open CanonicalGenus UnitDistance.NumberFieldAnalysis

theorem radE_zero : radE 0 = -1 := by
  apply Subtype.ext
  simp [radE, radicandA, radicandB]

theorem gE_zero_sq : gE 0 ^ 2 = -1 := by rw [gE_sq, radE_zero]

theorem sqrt2_sq : (gE 2 * gE 3) ^ 2 = 2 := by
  rw [mul_pow, gE_sq, gE_sq, ← bHom_radQ, ← bHom_radQ, ← map_mul, radQ_two_mul_three, map_ofNat]

theorem sqrt2_ne_zero : gE 2 * gE 3 ≠ 0 := mul_ne_zero (gE_ne_zero 2) (gE_ne_zero 3)

/-- A primitive eighth root of unity in `E`. -/
def zeta8 : Carrier := (1 + gE 0) / (gE 2 * gE 3)

theorem zeta8_sq : zeta8 ^ 2 = gE 0 := by
  unfold zeta8
  rw [div_pow, sqrt2_sq]
  linear_combination (1 / 2 : Carrier) * gE_zero_sq

theorem zeta8_pow_four : zeta8 ^ 4 = -1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, zeta8_sq, gE_zero_sq]

theorem isIntegral_zeta8 : IsIntegral ℤ zeta8 := by
  apply IsIntegral.of_pow (n := 2) (by norm_num)
  rw [zeta8_sq]
  exact isIntegral_gE 0

def zetaO : 𝓞 Carrier := toO zeta8 isIntegral_zeta8

theorem zetaO_pow_four : zetaO ^ 4 = -1 := by
  apply RingOfIntegers.ext
  simp only [map_pow, map_neg, map_one]
  exact zeta8_pow_four

theorem one_sub_zetaO_pow_four :
    (1 - zetaO) ^ 4 = 2 * (-2 * zetaO + 3 * zetaO ^ 2 - 2 * zetaO ^ 3) := by
  linear_combination zetaO_pow_four

theorem one_sub_zetaO_pow_four_mul :
    (1 - zetaO) ^ 4 * (-2 * zetaO - 3 * zetaO ^ 2 - 2 * zetaO ^ 3) = 2 := by
  linear_combination (-2 - 2 * zetaO + 5 * zetaO ^ 2 - 2 * zetaO ^ 3) * zetaO_pow_four

/-- `e ≥ 4` at 2. -/
theorem four_le_ramificationIdxIn_two :
    4 ≤ (rationalPrimeIdeal 2).ramificationIdxIn (𝓞 Carrier) := by
  obtain ⟨P, hP1, hP2⟩ := exists_prime_liesOver Carrier 2
  apply le_ramificationIdxIn_of_mem_pow P 4
  have h2 : (2 : 𝓞 Carrier) ∈ P := by
    have := (intCast_mem_iff (p := 2) P 2).2 (dvd_refl _)
    simpa using this
  have hπ : (1 - zetaO) ∈ P := by
    apply hP1.mem_of_pow_mem 4
    rw [one_sub_zetaO_pow_four]
    exact P.mul_mem_right _ h2
  rw [show ((2 : ℕ) : 𝓞 Carrier) = 2 by norm_num, ← one_sub_zetaO_pow_four_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hπ 4)

/-- `√5 = √-1 · √-5` and the golden ratio. -/
def goldenE : Carrier := (1 + gE 0 * gE 6 * gE 7) / 2

theorem sqrt5_sq : (gE 0 * gE 6 * gE 7) ^ 2 = 5 := by
  have h67 : radQ 6 * radQ 7 = -5 := by decide +kernel
  rw [mul_pow, mul_pow, gE_zero_sq, gE_sq, gE_sq, ← bHom_radQ, ← bHom_radQ, mul_assoc,
    ← map_mul, h67, map_neg, map_ofNat]
  ring

theorem goldenE_eq : goldenE ^ 2 - (1 : ℤ) * goldenE + (-1 : ℤ) = 0 := by
  unfold goldenE
  push_cast
  linear_combination (1 / 4 : Carrier) * sqrt5_sq

def goldenO : 𝓞 Carrier := toO goldenE (isIntegral_of_quadratic 1 (-1) goldenE_eq)

theorem goldenO_sq_sub : goldenO ^ 2 - goldenO = 1 := by
  apply RingOfIntegers.ext
  simp only [map_pow, map_sub, map_one]
  change goldenE ^ 2 - goldenE = 1
  have := goldenE_eq
  push_cast at this
  linear_combination this

theorem inertiaDegIn_two_ne_one : (rationalPrimeIdeal 2).inertiaDegIn (𝓞 Carrier) ≠ 1 := by
  intro hf
  obtain ⟨P, hP1, hP2⟩ := exists_prime_liesOver Carrier 2
  have h := pow_prime_pow_sub_mem (p := 2) P goldenO 1
  rw [hf, mul_one, pow_one, goldenO_sq_sub] at h
  exact hP1.ne_top ((Ideal.eq_top_iff_one _).2 h)

/-- `f = 2` at 2. -/
theorem inertiaDegIn_two : (rationalPrimeIdeal 2).inertiaDegIn (𝓞 Carrier) = 2 := by
  rcases (Nat.dvd_prime Nat.prime_two).1 inertiaDegIn_two_dvd with h | h
  · exact absurd h inertiaDegIn_two_ne_one
  · exact h

/-- `e = 4` at 2. -/
theorem ramificationIdxIn_two : (rationalPrimeIdeal 2).ramificationIdxIn (𝓞 Carrier) = 4 := by
  have h1 := ramification_mul_inertia_two_le
  have h2 := four_le_ramificationIdxIn_two
  rw [inertiaDegIn_two] at h1
  omega

/-! ### 29 -/

def sqrt2O : 𝓞 Carrier := gO 2 * gO 3

theorem sqrt2O_sq : sqrt2O ^ 2 = 2 := by
  unfold sqrt2O
  rw [show (gO 2 * gO 3) ^ 2 = (gO 2 * gO 2) * (gO 3 * gO 3) by ring, gO_sq, gO_sq,
    radO_two_mul_three]

instance fact_prime_29 : Fact (Nat.Prime 29) := ⟨by norm_num⟩

theorem inertiaDegIn_29_ne_one : (rationalPrimeIdeal 29).inertiaDegIn (𝓞 Carrier) ≠ 1 := by
  intro hf
  obtain ⟨P, hP1, hP2⟩ := exists_prime_liesOver Carrier 29
  have h := pow_prime_pow_sub_mem (p := 29) P sqrt2O 1
  rw [hf, mul_one, pow_one] at h
  have e : sqrt2O ^ 29 - sqrt2O = ((16383 : ℤ) : 𝓞 Carrier) * sqrt2O := by
    rw [show sqrt2O ^ 29 = (sqrt2O ^ 2) ^ 14 * sqrt2O by ring, sqrt2O_sq]
    push_cast
    ring
  rw [e] at h
  rcases hP1.mem_or_mem h with h1 | h1
  · rw [intCast_mem_iff (p := 29) P] at h1
    norm_num at h1
  · have h2 : sqrt2O ^ 2 ∈ P := by rw [sq]; exact P.mul_mem_left _ h1
    rw [sqrt2O_sq, show (2 : 𝓞 Carrier) = ((2 : ℤ) : 𝓞 Carrier) by norm_num,
      intCast_mem_iff (p := 29) P] at h2
    norm_num at h2

/-- `(e, f) = (1, 2)` at 29. -/
theorem inertiaDegIn_29 : (rationalPrimeIdeal 29).inertiaDegIn (𝓞 Carrier) = 2 := by
  rcases (Nat.dvd_prime Nat.prime_two).1 genusLocalTypes.twentyNine_f with h | h
  · exact absurd h inertiaDegIn_29_ne_one
  · exact h

theorem ramificationIdxIn_29 : (rationalPrimeIdeal 29).ramificationIdxIn (𝓞 Carrier) = 1 :=
  genusLocalTypes.twentyNine_e

/-! ### 7 -/

/-- `(ε^24 + 1)/7`, an integer of `ℚ(√241)`. -/
def epsT : Q241 := (1 / 7 : ℚ) • (radQ 1 ^ 24 + 1)

theorem epsT_spec : radQ 1 ^ 24 = 7 * epsT - 1 := by
  unfold epsT
  rw [Algebra.smul_def, ← mul_assoc, ← map_ofNat (algebraMap ℚ Q241) 7, ← map_mul]
  norm_num

theorem epsT_trace_den : (QuadraticAlgebra.trace epsT).den = 1 := by decide +kernel
theorem epsT_norm_den : (QuadraticAlgebra.norm epsT).den = 1 := by decide +kernel

def epsTO : 𝓞 Carrier := toO (bHom epsT) (isIntegral_bHom _ epsT_trace_den epsT_norm_den)

theorem radO_one_pow : radO 1 ^ 24 = 7 * epsTO - 1 := by
  apply RingOfIntegers.ext
  simp only [map_pow, map_sub, map_mul, map_one, map_ofNat]
  change bHom (radQ 1) ^ 24 = 7 * bHom epsT - 1
  rw [← map_pow, epsT_spec, map_sub, map_mul, map_ofNat, map_one]

instance fact_prime_7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩

theorem inertiaDegIn_7_not_dvd_two : ¬ (rationalPrimeIdeal 7).inertiaDegIn (𝓞 Carrier) ∣ 2 := by
  intro hf
  obtain ⟨k, hk⟩ := hf
  obtain ⟨P, hP1, hP2⟩ := exists_prime_liesOver Carrier 7
  have h := pow_prime_pow_sub_mem (p := 7) P (gO 1) k
  rw [← hk] at h
  have e : gO 1 ^ (7 ^ 2) - gO 1 = 7 * epsTO * gO 1 - ((2 : ℤ) : 𝓞 Carrier) * gO 1 := by
    rw [show gO 1 ^ (7 ^ 2) = (gO 1 * gO 1) ^ 24 * gO 1 by ring, gO_sq, radO_one_pow]
    push_cast
    ring
  rw [e] at h
  have h7 : (7 : 𝓞 Carrier) ∈ P := by
    have := (intCast_mem_iff (p := 7) P 7).2 (dvd_refl _)
    simpa using this
  have h2 : ((2 : ℤ) : 𝓞 Carrier) * gO 1 ∈ P := by
    have h7' : 7 * epsTO * gO 1 ∈ P := P.mul_mem_right _ (P.mul_mem_right _ h7)
    have := P.sub_mem h7' h
    convert this using 1
    ring
  have h2' : 2 * gO 1 ∈ P := by simpa using h2
  have := dvd_of_two_gO_mem (p := 7) P 1 h2'
  revert this
  decide

/-- `(e, f) = (1, 4)` at 7. -/
theorem inertiaDegIn_7 : (rationalPrimeIdeal 7).inertiaDegIn (𝓞 Carrier) = 4 := by
  have h4 := genusLocalTypes.seven_f
  have hle : (rationalPrimeIdeal 7).inertiaDegIn (𝓞 Carrier) ≤ 4 := Nat.le_of_dvd (by norm_num) h4
  have hne := inertiaDegIn_7_not_dvd_two
  interval_cases h : (rationalPrimeIdeal 7).inertiaDegIn (𝓞 Carrier)
  · norm_num at h4
  · exact absurd (one_dvd 2) hne
  · exact absurd (dvd_refl 2) hne
  · norm_num at h4
  · rfl

theorem ramificationIdxIn_7 : (rationalPrimeIdeal 7).ramificationIdxIn (𝓞 Carrier) = 1 :=
  genusLocalTypes.seven_e

/-- The exact absolute local types of the canonical genus field at 2, 29, 7. -/
theorem exactLocalTypes :
    ((rationalPrimeIdeal 2).ramificationIdxIn (𝓞 Carrier) = 4 ∧
      (rationalPrimeIdeal 2).inertiaDegIn (𝓞 Carrier) = 2) ∧
    ((rationalPrimeIdeal 29).ramificationIdxIn (𝓞 Carrier) = 1 ∧
      (rationalPrimeIdeal 29).inertiaDegIn (𝓞 Carrier) = 2) ∧
    ((rationalPrimeIdeal 7).ramificationIdxIn (𝓞 Carrier) = 1 ∧
      (rationalPrimeIdeal 7).inertiaDegIn (𝓞 Carrier) = 4) :=
  ⟨⟨ramificationIdxIn_two, inertiaDegIn_two⟩, ⟨ramificationIdxIn_29, inertiaDegIn_29⟩,
    ⟨ramificationIdxIn_7, inertiaDegIn_7⟩⟩

end UnitDistance.Sqrt241.Genus
