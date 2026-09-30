module

public import UnitDistance.Sqrt241.Base.SUnits
public import UnitDistance.PadicTwoSquareclasses
public import Mathlib.NumberTheory.Padics.Hensel
public import Mathlib.NumberTheory.Padics.RingHoms

@[expose] public section
set_option backward.privateInPublic true

/-!
# `p`-adic embeddings of `B = ℚ(√241)` at the split primes `2, 3, 5, 29`

For a root `r ∈ ℤ_p` of `X² - X - 60` (the minimal polynomial of `ω`), `iotaInt r`
is the ring map `𝓞 B → ℤ_p`, `ω ↦ r`, and `iota r : B →ₐ[ℚ] ℚ_p` its extension
(`√241 ↦ 2r - 1`). Hensel's lemma gives the roots; the named embeddings are
`iota2, iota2', iota3, iota3', iota5, iota5', iota29, iota29'`, the unprimed/primed
one belonging to the prime `(π_p)`/`(π_p')` of `Primes.lean`:
`x ∈ P2 ↔ ‖iotaInt root2 x‖ < 1` etc.

The images of the eight radicands in `ℚ_p^×/ℚ_p^{×2}` are given by explicit
representatives (`squareclass2`, …), matching the Hilbert-symbol table of
`kummer241.gp`.
-/

noncomputable section

namespace UnitDistance.Sqrt241.Base

open NumberField Polynomial

/-! ## Residues of `p`-adic integers -/

section Residue

variable {p : ℕ} [Fact p.Prime]

theorem padicInt_norm_lt_one_iff (x : ℤ_[p]) : ‖x‖ < 1 ↔ PadicInt.toZMod x = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal,
    PadicInt.mem_nonunits]

theorem padicInt_norm_eq_one_iff (x : ℤ_[p]) : ‖x‖ = 1 ↔ PadicInt.toZMod x ≠ 0 := by
  rw [Ne, ← padicInt_norm_lt_one_iff]
  constructor
  · intro h
    rw [h]
    exact lt_irrefl 1
  · intro h
    exact le_antisymm (PadicInt.norm_le_one x) (not_lt.mp h)

theorem padicInt_isUnit_iff (x : ℤ_[p]) : IsUnit x ↔ PadicInt.toZMod x ≠ 0 := by
  rw [PadicInt.isUnit_iff, padicInt_norm_eq_one_iff]

/-- Composing an evaluation map with a ring map evaluates at the image of the root. -/
theorem ringHom_comp_evalHom {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (r : R)
    (hr : r * r = r + 60) :
    f.comp (evalHom r hr) = evalHom (f r) (by rw [← map_mul, hr, map_add, map_ofNat]) := by
  ext x
  obtain ⟨m, n, rfl⟩ := exists_mk x
  simp

end Residue

/-! ## Roots of `X² - X - 60` in `ℤ_p` -/

section Roots

variable {p : ℕ} [Fact p.Prime]

/-- **Hensel.** A simple root `a` of `X² - X - 60` modulo `p` lifts to a root in `ℤ_p`
with the same residue. -/
theorem exists_omegaRoot (a : ℤ) (hunit : ¬ (p : ℤ) ∣ 2 * a - 1)
    (hroot : (p : ℤ) ∣ a ^ 2 - a - 60) :
    ∃ r : ℤ_[p], r * r = r + 60 ∧ PadicInt.toZMod r = (a : ZMod p) := by
  let F : Polynomial ℤ := X ^ 2 - X - C 60
  have hFa : F.aeval (a : ℤ_[p]) = ((a ^ 2 - a - 60 : ℤ) : ℤ_[p]) := by
    simp [F, map_ofNat]
  have hF'a : F.derivative.aeval (a : ℤ_[p]) = ((2 * a - 1 : ℤ) : ℤ_[p]) := by
    simp [F, Polynomial.derivative_pow, map_ofNat]
  have hnorm' : ‖F.derivative.aeval (a : ℤ_[p])‖ = 1 := by
    rw [hF'a, padicInt_norm_eq_one_iff, map_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hunit
  have hnormF : ‖F.aeval (a : ℤ_[p])‖ < 1 := by
    rw [hFa, PadicInt.norm_int_lt_one_iff_dvd]
    exact hroot
  obtain ⟨r, hr, hra, -, -⟩ := hensels_lemma (F := F) (a := (a : ℤ_[p]))
    (by rw [hnorm', one_pow]; exact hnormF)
  refine ⟨r, ?_, ?_⟩
  · have h : r ^ 2 - r - 60 = 0 := by simpa [F, map_ofNat] using hr
    linear_combination h
  · rw [hnorm', padicInt_norm_lt_one_iff, map_sub, sub_eq_zero, map_intCast] at hra
    exact hra

/-- A root congruent to `a` modulo `p ^ k` (used for `p = 2`, `k = 3`). -/
theorem exists_omegaRoot_pow (a : ℤ) (k : ℕ) (hunit : ¬ (p : ℤ) ∣ 2 * a - 1)
    (hroot : (p : ℤ) ^ k ∣ a ^ 2 - a - 60) (hk : 1 ≤ k) :
    ∃ r : ℤ_[p], r * r = r + 60 ∧ PadicInt.toZMod r = (a : ZMod p) ∧
      r - a ∈ Ideal.span {(p : ℤ_[p]) ^ k} := by
  obtain ⟨r, hr, hra⟩ := exists_omegaRoot (p := p) a hunit
    (dvd_trans (dvd_pow_self _ (by omega)) hroot)
  refine ⟨r, hr, hra, ?_⟩
  -- `(r - a)(r + a - 1) = -(a² - a - 60)` and `r + a - 1` is a unit
  have hu : IsUnit (r + a - 1) := by
    rw [padicInt_isUnit_iff, map_sub, map_add, hra, map_intCast, map_one]
    intro h
    apply hunit
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    linear_combination h
  have hprod : (r - a) * (r + a - 1) = -((a ^ 2 - a - 60 : ℤ) : ℤ_[p]) := by
    push_cast
    linear_combination hr
  have hmem : ((a ^ 2 - a - 60 : ℤ) : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ k} := by
    obtain ⟨c, hc⟩ := hroot
    rw [Ideal.mem_span_singleton]
    exact ⟨c, by rw [hc]; push_cast; ring⟩
  have hsub : r - a ∈ Ideal.span {(p : ℤ_[p]) ^ k} := by
    have : r - a = -((a ^ 2 - a - 60 : ℤ) : ℤ_[p]) * ↑hu.unit⁻¹ := by
      rw [← hprod, mul_assoc, IsUnit.mul_val_inv, mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ (neg_mem hmem)
  exact hsub

/-- A root of `X² - X - 60` in `ℤ₂` congruent to `a` modulo `8`. -/
theorem exists_omegaRoot_two (a : ℤ) (hroot : (8 : ℤ) ∣ a ^ 2 - a - 60) :
    ∃ r : ℤ_[2], r * r = r + 60 ∧ PadicInt.toZMod r = (a : ZMod 2) ∧
      UnitDistance.PadicTwo.residue8 r = (a : ZMod 8) := by
  obtain ⟨r, hr, hra, hmem⟩ := exists_omegaRoot_pow (p := 2) a 3 (by omega)
    (by simpa using hroot) (by norm_num)
  refine ⟨r, hr, hra, ?_⟩
  have hk : r - a ∈ RingHom.ker (PadicInt.toZModPow 3 : ℤ_[2] →+* ZMod (2 ^ 3)) := by
    rwa [PadicInt.ker_toZModPow]
  have h8 : UnitDistance.PadicTwo.residue8 (r - a) = 0 := hk
  rwa [map_sub, sub_eq_zero, map_intCast] at h8

end Roots

/-! ## Embeddings -/

section Embeddings

variable {p : ℕ} [Fact p.Prime]

/-- The ring map `𝓞 B → ℤ_p`, `ω ↦ r`. -/
def iotaInt (r : ℤ_[p]) (hr : r * r = r + 60) : 𝓞 B →+* ℤ_[p] := evalHom r hr

theorem iotaInt_mk (r : ℤ_[p]) (hr : r * r = r + 60) (m n : ℤ) :
    iotaInt r hr (mk m n) = (m : ℤ_[p]) + (n : ℤ_[p]) * r := evalHom_mk r hr m n

theorem aeval_iota_root (r : ℤ_[p]) (hr : r * r = r + 60) :
    aeval (2 * (r : ℚ_[p]) - 1) (minpoly ℚ powerBasis.gen) = 0 := by
  rw [powerBasis_gen, minpoly_sqrt241]
  have h := congrArg PadicInt.Coe.ringHom hr
  simp only [map_mul, map_add, map_ofNat] at h
  change (r : ℚ_[p]) * r = r + 60 at h
  simp only [map_sub, map_pow, aeval_X, map_ofNat]
  linear_combination 4 * h

/-- The embedding `B → ℚ_p`, `√241 ↦ 2r - 1` (so `ω ↦ r`). -/
def iota (r : ℤ_[p]) (hr : r * r = r + 60) : B →ₐ[ℚ] ℚ_[p] :=
  powerBasis.lift (2 * (r : ℚ_[p]) - 1) (aeval_iota_root r hr)

theorem iota_sqrt241 (r : ℤ_[p]) (hr : r * r = r + 60) :
    iota r hr sqrt241 = 2 * (r : ℚ_[p]) - 1 :=
  PowerBasis.lift_gen _ _ _

/-- On `𝓞 B` the embedding takes values in `ℤ_p`. -/
theorem iota_coe (r : ℤ_[p]) (hr : r * r = r + 60) (x : 𝓞 B) :
    iota r hr (x : B) = (iotaInt r hr x : ℚ_[p]) := by
  obtain ⟨m, n, rfl⟩ := exists_mk x
  rw [coe_mk, map_add, map_mul, AlgHom.commutes, AlgHom.commutes, iota_sqrt241, iotaInt_mk]
  push_cast
  simp only [eq_ratCast, Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat]
  ring

end Embeddings

/-! ## Square classes -/

section SquareClasses

/-- Odd `p`: a `p`-adic integer with residue `c t²` (`2ct ≠ 0`) is `c` times a square. -/
theorem padicInt_eq_mul_sq_of_toZMod {p : ℕ} [Fact p.Prime] {u : ℤ_[p]} {c : ℤ}
    (h : ∃ t : ZMod p, (2 * c * t : ZMod p) ≠ 0 ∧ PadicInt.toZMod u = c * t ^ 2) :
    ∃ z : ℤ_[p], z ≠ 0 ∧ u = c * z ^ 2 := by
  obtain ⟨t, ht, hu⟩ := h
  obtain ⟨b, hb⟩ := ZMod.intCast_surjective t
  set a : ℤ_[p] := (b : ℤ_[p]) with ha
  have hta : PadicInt.toZMod a = t := by rw [ha, map_intCast, hb]
  let F : Polynomial ℤ_[p] := C (c : ℤ_[p]) * X ^ 2 - C u
  have hFeval : F.aeval a = (c : ℤ_[p]) * a ^ 2 - u := by simp [F]
  have hF'eval : F.derivative.aeval a = 2 * (c : ℤ_[p]) * a := by
    simp [F, Polynomial.derivative_pow]
    ring
  have hFa : ‖F.aeval a‖ < 1 := by
    rw [hFeval, padicInt_norm_lt_one_iff, map_sub, map_mul, map_pow, map_intCast, hta, hu,
      sub_self]
  have hF'a : ‖F.derivative.aeval a‖ = 1 := by
    rw [hF'eval, padicInt_norm_eq_one_iff, map_mul, map_mul, map_ofNat, map_intCast, hta]
    exact ht
  obtain ⟨z, hz, hza, -, -⟩ := hensels_lemma (F := F) (a := a)
    (by rw [hF'a, one_pow]; exact hFa)
  refine ⟨z, ?_, ?_⟩
  · rintro rfl
    rw [hF'a, zero_sub, norm_neg, padicInt_norm_lt_one_iff, hta] at hza
    apply ht
    rw [hza, mul_zero]
  · have h1 : F.aeval z = (c : ℤ_[p]) * z ^ 2 - u := by simp [F]
    rw [h1] at hz
    linear_combination -hz

theorem padicInt_two_ne_zero_of_residue8 {z : ℤ_[2]} {c : ℤ} (hc : Odd c)
    (h : UnitDistance.PadicTwo.residue8 z = (c : ZMod 8)) : z ≠ 0 := by
  rintro rfl
  rw [map_zero, eq_comm, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
  obtain ⟨k, rfl⟩ := hc
  push_cast at h
  omega

/-- `p = 2`: a `2`-adic integer congruent to an odd `c` modulo `8` is `c` times a square. -/
theorem padicInt_eq_mul_sq_of_residue8 {u : ℤ_[2]} {c : ℤ} (hc : Odd c)
    (h : UnitDistance.PadicTwo.residue8 u = (c : ZMod 8)) :
    ∃ z : ℤ_[2], z ≠ 0 ∧ u = c * z ^ 2 := by
  have hcu : IsUnit (c : ℤ_[2]) := by
    rw [padicInt_isUnit_iff, map_intCast]
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    obtain ⟨k, rfl⟩ := hc
    omega
  have hinv : UnitDistance.PadicTwo.residue8 (c : ℤ_[2]) *
      UnitDistance.PadicTwo.residue8 (↑hcu.unit⁻¹ : ℤ_[2]) = 1 := by
    rw [← map_mul, IsUnit.mul_val_inv, map_one]
  obtain ⟨z, hz⟩ := UnitDistance.PadicTwo.exists_sq_eq_of_residue_one
    (u * ↑hcu.unit⁻¹) (by rw [map_mul, h, ← hinv, map_intCast])
  have hu : u = c * z ^ 2 := by
    rw [hz, mul_comm u, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
  refine ⟨z, ?_, hu⟩
  rintro rfl
  apply padicInt_two_ne_zero_of_residue8 hc h
  rw [hu]
  ring

/-- In a field, if `x y = n` and `y = c z²` with `c z ≠ 0`, then `x = (n c) w²`. -/
theorem eq_mul_sq_of_mul_eq {K : Type*} [Field K] {x y n c z : K} (hxy : x * y = n)
    (hy : y = c * z ^ 2) (hc : c ≠ 0) (hz : z ≠ 0) :
    ∃ w : K, w ≠ 0 ∧ x = (n * c) * w ^ 2 := by
  refine ⟨(c * z)⁻¹, inv_ne_zero (mul_ne_zero hc hz), ?_⟩
  rw [← hxy, hy]
  field_simp

end SquareClasses

/-! ## Radicands under the embeddings -/

section Entries

theorem root_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {r : R}
    (hr : r * r = r + 60) : f r * f r = f r + 60 := by
  rw [← map_mul, hr, map_add, map_ofNat]

theorem evalHom_congr {R : Type*} [CommRing R] {r r' : R} (h : r = r') (hr : r * r = r + 60) :
    evalHom r hr = evalHom r' (h ▸ hr) := by
  subst h
  rfl

variable {p : ℕ} [Fact p.Prime]

theorem toZMod_iotaInt (r : ℤ_[p]) (hr : r * r = r + 60) (x : 𝓞 B) :
    PadicInt.toZMod (iotaInt r hr x) = evalHom (PadicInt.toZMod r) (root_map _ hr) x := by
  rw [iotaInt, ← RingHom.comp_apply, ringHom_comp_evalHom]

theorem residue8_iotaInt (r : ℤ_[2]) (hr : r * r = r + 60) (x : 𝓞 B) :
    UnitDistance.PadicTwo.residue8 (iotaInt r hr x) =
      evalHom (UnitDistance.PadicTwo.residue8 r) (root_map _ hr) x := by
  rw [iotaInt, ← RingHom.comp_apply, ringHom_comp_evalHom]

theorem sigmaInt_alpha (i : Fin 8) :
    sigmaInt (alpha i) = mk ((alphaCoords i).1 + (alphaCoords i).2) (-(alphaCoords i).2) := by
  rw [alpha_eq_mk, sigmaInt_mk]

theorem iota_alpha_mul_sigma (r : ℤ_[p]) (hr : r * r = r + 60) (i : Fin 8) (n : ℤ)
    (hn : Algebra.norm ℤ (alpha i) = n) :
    iota r hr ((alpha i : 𝓞 B) : B) * iota r hr ((sigmaInt (alpha i) : 𝓞 B) : B) =
      (n : ℚ_[p]) := by
  rw [← map_mul, ← coe_mul, mul_sigmaInt, hn]
  simp

/-- Odd `p`, radicand a unit at the prime: its class is read off from the residue. -/
theorem iota_alpha_of_unit_odd (r : ℤ_[p]) (hr : r * r = r + 60) (a : ZMod p)
    (hra : PadicInt.toZMod r = a) (i : Fin 8) (c : ℤ)
    (h : ∃ t : ZMod p, (2 * c * t : ZMod p) ≠ 0 ∧
      ((alphaCoords i).1 : ZMod p) + ((alphaCoords i).2 : ZMod p) * a = c * t ^ 2) :
    ∃ z : ℚ_[p], z ≠ 0 ∧ iota r hr ((alpha i : 𝓞 B) : B) = (c : ℚ_[p]) * z ^ 2 := by
  obtain ⟨z, hz0, hz⟩ := padicInt_eq_mul_sq_of_toZMod (u := iotaInt r hr (alpha i)) (c := c)
    (by rw [toZMod_iotaInt, evalHom_alpha, hra]; exact h)
  refine ⟨(z : ℚ_[p]), PadicInt.coe_ne_zero.mpr hz0, ?_⟩
  rw [iota_coe, hz]
  push_cast
  ring

/-- Odd `p`, radicand a uniformizer: `x σ(x) = N(x)` and `σ(x)` is a unit. -/
theorem iota_alpha_of_uniformizer_odd (r : ℤ_[p]) (hr : r * r = r + 60) (a : ZMod p)
    (hra : PadicInt.toZMod r = a) (i : Fin 8) (n c' c₀ : ℤ)
    (hn : Algebra.norm ℤ (alpha i) = n) (hc' : c' ≠ 0) (hc₀ : n * c' = c₀)
    (h : ∃ t : ZMod p, (2 * c' * t : ZMod p) ≠ 0 ∧
      (((alphaCoords i).1 + (alphaCoords i).2 : ℤ) : ZMod p) +
        ((-(alphaCoords i).2 : ℤ) : ZMod p) * a = c' * t ^ 2) :
    ∃ z : ℚ_[p], z ≠ 0 ∧ iota r hr ((alpha i : 𝓞 B) : B) = (c₀ : ℚ_[p]) * z ^ 2 := by
  obtain ⟨z, hz0, hz⟩ := padicInt_eq_mul_sq_of_toZMod
    (u := iotaInt r hr (sigmaInt (alpha i))) (c := c')
    (by rw [toZMod_iotaInt, sigmaInt_alpha, evalHom_mk, hra]; exact h)
  have hy : iota r hr ((sigmaInt (alpha i) : 𝓞 B) : B) = (c' : ℚ_[p]) * (z : ℚ_[p]) ^ 2 := by
    rw [iota_coe, hz]
    push_cast
    ring
  obtain ⟨w, hw0, hw⟩ := eq_mul_sq_of_mul_eq (iota_alpha_mul_sigma r hr i n hn) hy
    (by exact_mod_cast hc') (PadicInt.coe_ne_zero.mpr hz0)
  exact ⟨w, hw0, by rw [hw, ← hc₀]; push_cast; ring⟩

/-- `p = 2`, radicand a unit at the prime: its class is read off modulo `8`. -/
theorem iota_alpha_of_unit_two (r : ℤ_[2]) (hr : r * r = r + 60) (a : ZMod 8)
    (hra : UnitDistance.PadicTwo.residue8 r = a) (i : Fin 8) (c : ℤ) (hc : Odd c)
    (h : ((alphaCoords i).1 : ZMod 8) + ((alphaCoords i).2 : ZMod 8) * a = c) :
    ∃ z : ℚ_[2], z ≠ 0 ∧ iota r hr ((alpha i : 𝓞 B) : B) = (c : ℚ_[2]) * z ^ 2 := by
  obtain ⟨z, hz0, hz⟩ := padicInt_eq_mul_sq_of_residue8 (u := iotaInt r hr (alpha i)) hc
    (by rw [residue8_iotaInt, evalHom_alpha, hra]; exact h)
  refine ⟨(z : ℚ_[2]), PadicInt.coe_ne_zero.mpr hz0, ?_⟩
  rw [iota_coe, hz]
  push_cast
  ring

/-- `p = 2`, radicand a uniformizer. -/
theorem iota_alpha_of_uniformizer_two (r : ℤ_[2]) (hr : r * r = r + 60) (a : ZMod 8)
    (hra : UnitDistance.PadicTwo.residue8 r = a) (i : Fin 8) (n c' c₀ : ℤ)
    (hn : Algebra.norm ℤ (alpha i) = n) (hc' : Odd c') (hc₀ : n * c' = c₀)
    (h : (((alphaCoords i).1 + (alphaCoords i).2 : ℤ) : ZMod 8) +
        ((-(alphaCoords i).2 : ℤ) : ZMod 8) * a = c') :
    ∃ z : ℚ_[2], z ≠ 0 ∧ iota r hr ((alpha i : 𝓞 B) : B) = (c₀ : ℚ_[2]) * z ^ 2 := by
  obtain ⟨z, hz0, hz⟩ := padicInt_eq_mul_sq_of_residue8
    (u := iotaInt r hr (sigmaInt (alpha i))) hc'
    (by rw [residue8_iotaInt, sigmaInt_alpha, evalHom_mk, hra]; exact h)
  have hy : iota r hr ((sigmaInt (alpha i) : 𝓞 B) : B) = (c' : ℚ_[2]) * (z : ℚ_[2]) ^ 2 := by
    rw [iota_coe, hz]
    push_cast
    ring
  have hc'0 : (c' : ℚ_[2]) ≠ 0 := by
    have : c' ≠ 0 := by rintro rfl; exact absurd hc' (by decide)
    exact_mod_cast this
  obtain ⟨w, hw0, hw⟩ := eq_mul_sq_of_mul_eq (iota_alpha_mul_sigma r hr i n hn) hy hc'0
    (PadicInt.coe_ne_zero.mpr hz0)
  exact ⟨w, hw0, by rw [hw, ← hc₀]; push_cast; ring⟩

end Entries

/-! ## The eight embeddings at `2, 3, 5, 29` and the square classes of the radicands -/

-- BEGIN Generated by scripts/sqrt241/generate_base_tables.py local — do not edit by hand.
/-- The root of `X² - X - 60` in `ℤ_2` with `r ≡ 4 (mod 8)`. -/
def root2 : ℤ_[2] := (exists_omegaRoot_two 4 (by decide)).choose

theorem root2_mul_self : root2 * root2 = root2 + 60 :=
  (exists_omegaRoot_two 4 (by decide)).choose_spec.1

theorem toZMod_root2 : PadicInt.toZMod root2 = 0 := by
  rw [root2, (exists_omegaRoot_two 4 (by decide)).choose_spec.2.1]; decide

theorem residue8_root2 : UnitDistance.PadicTwo.residue8 root2 = 4 := by
  rw [root2, (exists_omegaRoot_two 4 (by decide)).choose_spec.2.2]; decide

/-- The embedding `B → ℚ_2` at `P2` (`ω ↦ root2`). -/
def iota2 : B →ₐ[ℚ] ℚ_[2] := iota root2 root2_mul_self

/-- The embedding `𝓞 B → ℤ_2` at `P2`. -/
def iotaInt2 : 𝓞 B →+* ℤ_[2] := iotaInt root2 root2_mul_self

theorem iota2_coe (x : 𝓞 B) : iota2 (x : B) = (iotaInt2 x : ℚ_[2]) :=
  iota_coe _ _ x

/-- `P2` is the prime of `iota2`: `x ∈ P2 ↔ ‖iota2 x‖ < 1`. -/
theorem mem_P2_iff_norm_iota (x : 𝓞 B) : x ∈ P2 ↔ ‖iotaInt2 x‖ < 1 := by
  rw [padicInt_norm_lt_one_iff, iotaInt2, toZMod_iotaInt, mem_P2, res2,
    evalHom_congr toZMod_root2]

/-- Square-class representatives of `iota2 (alpha i)` in `ℚ_2^×/ℚ_2^{×2}`. -/
def squareclass2 : Fin 8 → ℤ := ![7, 3, 6, 3, 1, 5, 3, 1]

theorem iota2_alpha (i : Fin 8) : ∃ z : ℚ_[2], z ≠ 0 ∧
    iota2 ((alpha i : 𝓞 B) : B) = (squareclass2 i : ℚ_[2]) * z ^ 2 := by
  fin_cases i
  · exact iota_alpha_of_unit_two _ _ _ residue8_root2 0 (7) (by decide) (by decide)
  · exact iota_alpha_of_unit_two _ _ _ residue8_root2 1 (3) (by decide) (by decide)
  · exact iota_alpha_of_uniformizer_two _ _ _ residue8_root2 2 (-2) (-3) 6 norm_pi2
      (by decide) (by norm_num) (by decide)
  · exact iota_alpha_of_unit_two _ _ _ residue8_root2 3 (3) (by decide) (by decide)
  · exact iota_alpha_of_unit_two _ _ _ residue8_root2 4 (1) (by decide) (by decide)
  · exact iota_alpha_of_unit_two _ _ _ residue8_root2 5 (5) (by decide) (by decide)
  · exact iota_alpha_of_unit_two _ _ _ residue8_root2 6 (3) (by decide) (by decide)
  · exact iota_alpha_of_unit_two _ _ _ residue8_root2 7 (1) (by decide) (by decide)
/-- The root of `X² - X - 60` in `ℤ_2` with `r ≡ 5 (mod 8)`. -/
def root2' : ℤ_[2] := (exists_omegaRoot_two 13 (by decide)).choose

theorem root2'_mul_self : root2' * root2' = root2' + 60 :=
  (exists_omegaRoot_two 13 (by decide)).choose_spec.1

theorem toZMod_root2' : PadicInt.toZMod root2' = 1 := by
  rw [root2', (exists_omegaRoot_two 13 (by decide)).choose_spec.2.1]; decide

theorem residue8_root2' : UnitDistance.PadicTwo.residue8 root2' = 5 := by
  rw [root2', (exists_omegaRoot_two 13 (by decide)).choose_spec.2.2]; decide

/-- The embedding `B → ℚ_2` at `P2'` (`ω ↦ root2'`). -/
def iota2' : B →ₐ[ℚ] ℚ_[2] := iota root2' root2'_mul_self

/-- The embedding `𝓞 B → ℤ_2` at `P2'`. -/
def iotaInt2' : 𝓞 B →+* ℤ_[2] := iotaInt root2' root2'_mul_self

theorem iota2'_coe (x : 𝓞 B) : iota2' (x : B) = (iotaInt2' x : ℚ_[2]) :=
  iota_coe _ _ x

/-- `P2'` is the prime of `iota2'`: `x ∈ P2' ↔ ‖iota2' x‖ < 1`. -/
theorem mem_P2'_iff_norm_iota (x : 𝓞 B) : x ∈ P2' ↔ ‖iotaInt2' x‖ < 1 := by
  rw [padicInt_norm_lt_one_iff, iotaInt2', toZMod_iotaInt, mem_P2', res2',
    evalHom_congr toZMod_root2']

/-- Square-class representatives of `iota2' (alpha i)` in `ℚ_2^×/ℚ_2^{×2}`. -/
def squareclass2' : Fin 8 → ℤ := ![7, 5, 5, 10, 5, 1, 1, 3]

theorem iota2'_alpha (i : Fin 8) : ∃ z : ℚ_[2], z ≠ 0 ∧
    iota2' ((alpha i : 𝓞 B) : B) = (squareclass2' i : ℚ_[2]) * z ^ 2 := by
  fin_cases i
  · exact iota_alpha_of_unit_two _ _ _ residue8_root2' 0 (7) (by decide) (by decide)
  · exact iota_alpha_of_unit_two _ _ _ residue8_root2' 1 (5) (by decide) (by decide)
  · exact iota_alpha_of_unit_two _ _ _ residue8_root2' 2 (5) (by decide) (by decide)
  · exact iota_alpha_of_uniformizer_two _ _ _ residue8_root2' 3 (-2) (-5) 10 norm_pi2'
      (by decide) (by norm_num) (by decide)
  · exact iota_alpha_of_unit_two _ _ _ residue8_root2' 4 (5) (by decide) (by decide)
  · exact iota_alpha_of_unit_two _ _ _ residue8_root2' 5 (1) (by decide) (by decide)
  · exact iota_alpha_of_unit_two _ _ _ residue8_root2' 6 (1) (by decide) (by decide)
  · exact iota_alpha_of_unit_two _ _ _ residue8_root2' 7 (3) (by decide) (by decide)
/-- The root of `X² - X - 60` in `ℤ_3` with `r ≡ 0 (mod 3)`. -/
def root3 : ℤ_[3] := (exists_omegaRoot (p := 3) 0 (by decide) (by decide)).choose

theorem root3_mul_self : root3 * root3 = root3 + 60 :=
  (exists_omegaRoot (p := 3) 0 (by decide) (by decide)).choose_spec.1

theorem toZMod_root3 : PadicInt.toZMod root3 = 0 := by
  rw [root3, (exists_omegaRoot (p := 3) 0 (by decide) (by decide)).choose_spec.2]; decide

/-- The embedding `B → ℚ_3` at `P3` (`ω ↦ root3`). -/
def iota3 : B →ₐ[ℚ] ℚ_[3] := iota root3 root3_mul_self

/-- The embedding `𝓞 B → ℤ_3` at `P3`. -/
def iotaInt3 : 𝓞 B →+* ℤ_[3] := iotaInt root3 root3_mul_self

theorem iota3_coe (x : 𝓞 B) : iota3 (x : B) = (iotaInt3 x : ℚ_[3]) :=
  iota_coe _ _ x

/-- `P3` is the prime of `iota3`: `x ∈ P3 ↔ ‖iota3 x‖ < 1`. -/
theorem mem_P3_iff_norm_iota (x : 𝓞 B) : x ∈ P3 ↔ ‖iotaInt3 x‖ < 1 := by
  rw [padicInt_norm_lt_one_iff, iotaInt3, toZMod_iotaInt, mem_P3, res3,
    evalHom_congr toZMod_root3]

/-- Square-class representatives of `iota3 (alpha i)` in `ℚ_3^×/ℚ_3^{×2}`. -/
def squareclass3 : Fin 8 → ℤ := ![-1, 1, -1, 1, 3, -1, -1, -1]

theorem iota3_alpha (i : Fin 8) : ∃ z : ℚ_[3], z ≠ 0 ∧
    iota3 ((alpha i : 𝓞 B) : B) = (squareclass3 i : ℚ_[3]) * z ^ 2 := by
  fin_cases i
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root3 0 (-1) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root3 1 (1) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root3 2 (-1) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root3 3 (1) (by decide)
  · exact iota_alpha_of_uniformizer_odd _ _ _ toZMod_root3 4 (-3) (-1) 3 norm_pi3
      (by norm_num) (by norm_num) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root3 5 (-1) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root3 6 (-1) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root3 7 (-1) (by decide)
/-- The root of `X² - X - 60` in `ℤ_3` with `r ≡ 1 (mod 3)`. -/
def root3' : ℤ_[3] := (exists_omegaRoot (p := 3) 1 (by decide) (by decide)).choose

theorem root3'_mul_self : root3' * root3' = root3' + 60 :=
  (exists_omegaRoot (p := 3) 1 (by decide) (by decide)).choose_spec.1

theorem toZMod_root3' : PadicInt.toZMod root3' = 1 := by
  rw [root3', (exists_omegaRoot (p := 3) 1 (by decide) (by decide)).choose_spec.2]; decide

/-- The embedding `B → ℚ_3` at `P3'` (`ω ↦ root3'`). -/
def iota3' : B →ₐ[ℚ] ℚ_[3] := iota root3' root3'_mul_self

/-- The embedding `𝓞 B → ℤ_3` at `P3'`. -/
def iotaInt3' : 𝓞 B →+* ℤ_[3] := iotaInt root3' root3'_mul_self

theorem iota3'_coe (x : 𝓞 B) : iota3' (x : B) = (iotaInt3' x : ℚ_[3]) :=
  iota_coe _ _ x

/-- `P3'` is the prime of `iota3'`: `x ∈ P3' ↔ ‖iota3' x‖ < 1`. -/
theorem mem_P3'_iff_norm_iota (x : 𝓞 B) : x ∈ P3' ↔ ‖iotaInt3' x‖ < 1 := by
  rw [padicInt_norm_lt_one_iff, iotaInt3', toZMod_iotaInt, mem_P3', res3',
    evalHom_congr toZMod_root3']

/-- Square-class representatives of `iota3' (alpha i)` in `ℚ_3^×/ℚ_3^{×2}`. -/
def squareclass3' : Fin 8 → ℤ := ![-1, -1, -1, 1, -1, 3, -1, -1]

theorem iota3'_alpha (i : Fin 8) : ∃ z : ℚ_[3], z ≠ 0 ∧
    iota3' ((alpha i : 𝓞 B) : B) = (squareclass3' i : ℚ_[3]) * z ^ 2 := by
  fin_cases i
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root3' 0 (-1) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root3' 1 (-1) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root3' 2 (-1) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root3' 3 (1) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root3' 4 (-1) (by decide)
  · exact iota_alpha_of_uniformizer_odd _ _ _ toZMod_root3' 5 (-3) (-1) 3 norm_pi3'
      (by norm_num) (by norm_num) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root3' 6 (-1) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root3' 7 (-1) (by decide)
/-- The root of `X² - X - 60` in `ℤ_5` with `r ≡ 1 (mod 5)`. -/
def root5 : ℤ_[5] := (exists_omegaRoot (p := 5) 1 (by decide) (by decide)).choose

theorem root5_mul_self : root5 * root5 = root5 + 60 :=
  (exists_omegaRoot (p := 5) 1 (by decide) (by decide)).choose_spec.1

theorem toZMod_root5 : PadicInt.toZMod root5 = 1 := by
  rw [root5, (exists_omegaRoot (p := 5) 1 (by decide) (by decide)).choose_spec.2]; decide

/-- The embedding `B → ℚ_5` at `P5` (`ω ↦ root5`). -/
def iota5 : B →ₐ[ℚ] ℚ_[5] := iota root5 root5_mul_self

/-- The embedding `𝓞 B → ℤ_5` at `P5`. -/
def iotaInt5 : 𝓞 B →+* ℤ_[5] := iotaInt root5 root5_mul_self

theorem iota5_coe (x : 𝓞 B) : iota5 (x : B) = (iotaInt5 x : ℚ_[5]) :=
  iota_coe _ _ x

/-- `P5` is the prime of `iota5`: `x ∈ P5 ↔ ‖iota5 x‖ < 1`. -/
theorem mem_P5_iff_norm_iota (x : 𝓞 B) : x ∈ P5 ↔ ‖iotaInt5 x‖ < 1 := by
  rw [padicInt_norm_lt_one_iff, iotaInt5, toZMod_iotaInt, mem_P5, res5,
    evalHom_congr toZMod_root5]

/-- Square-class representatives of `iota5 (alpha i)` in `ℚ_5^×/ℚ_5^{×2}`. -/
def squareclass5 : Fin 8 → ℤ := ![1, 2, 2, 1, 1, 2, 10, 2]

theorem iota5_alpha (i : Fin 8) : ∃ z : ℚ_[5], z ≠ 0 ∧
    iota5 ((alpha i : 𝓞 B) : B) = (squareclass5 i : ℚ_[5]) * z ^ 2 := by
  fin_cases i
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root5 0 (1) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root5 1 (2) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root5 2 (2) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root5 3 (1) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root5 4 (1) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root5 5 (2) (by decide)
  · exact iota_alpha_of_uniformizer_odd _ _ _ toZMod_root5 6 (-5) (-2) 10 norm_pi5
      (by norm_num) (by norm_num) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root5 7 (2) (by decide)
/-- The root of `X² - X - 60` in `ℤ_5` with `r ≡ 0 (mod 5)`. -/
def root5' : ℤ_[5] := (exists_omegaRoot (p := 5) 0 (by decide) (by decide)).choose

theorem root5'_mul_self : root5' * root5' = root5' + 60 :=
  (exists_omegaRoot (p := 5) 0 (by decide) (by decide)).choose_spec.1

theorem toZMod_root5' : PadicInt.toZMod root5' = 0 := by
  rw [root5', (exists_omegaRoot (p := 5) 0 (by decide) (by decide)).choose_spec.2]; decide

/-- The embedding `B → ℚ_5` at `P5'` (`ω ↦ root5'`). -/
def iota5' : B →ₐ[ℚ] ℚ_[5] := iota root5' root5'_mul_self

/-- The embedding `𝓞 B → ℤ_5` at `P5'`. -/
def iotaInt5' : 𝓞 B →+* ℤ_[5] := iotaInt root5' root5'_mul_self

theorem iota5'_coe (x : 𝓞 B) : iota5' (x : B) = (iotaInt5' x : ℚ_[5]) :=
  iota_coe _ _ x

/-- `P5'` is the prime of `iota5'`: `x ∈ P5' ↔ ‖iota5' x‖ < 1`. -/
theorem mem_P5'_iff_norm_iota (x : 𝓞 B) : x ∈ P5' ↔ ‖iotaInt5' x‖ < 1 := by
  rw [padicInt_norm_lt_one_iff, iotaInt5', toZMod_iotaInt, mem_P5', res5',
    evalHom_congr toZMod_root5']

/-- Square-class representatives of `iota5' (alpha i)` in `ℚ_5^×/ℚ_5^{×2}`. -/
def squareclass5' : Fin 8 → ℤ := ![1, 2, 1, 2, 2, 1, 2, 10]

theorem iota5'_alpha (i : Fin 8) : ∃ z : ℚ_[5], z ≠ 0 ∧
    iota5' ((alpha i : 𝓞 B) : B) = (squareclass5' i : ℚ_[5]) * z ^ 2 := by
  fin_cases i
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root5' 0 (1) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root5' 1 (2) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root5' 2 (1) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root5' 3 (2) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root5' 4 (2) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root5' 5 (1) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root5' 6 (2) (by decide)
  · exact iota_alpha_of_uniformizer_odd _ _ _ toZMod_root5' 7 (-5) (-2) 10 norm_pi5'
      (by norm_num) (by norm_num) (by decide)
/-- The root of `X² - X - 60` in `ℤ_29` with `r ≡ 2 (mod 29)`. -/
def root29 : ℤ_[29] := (exists_omegaRoot (p := 29) 2 (by decide) (by decide)).choose

theorem root29_mul_self : root29 * root29 = root29 + 60 :=
  (exists_omegaRoot (p := 29) 2 (by decide) (by decide)).choose_spec.1

theorem toZMod_root29 : PadicInt.toZMod root29 = 2 := by
  rw [root29, (exists_omegaRoot (p := 29) 2 (by decide) (by decide)).choose_spec.2]; decide

/-- The embedding `B → ℚ_29` at `P29` (`ω ↦ root29`). -/
def iota29 : B →ₐ[ℚ] ℚ_[29] := iota root29 root29_mul_self

/-- The embedding `𝓞 B → ℤ_29` at `P29`. -/
def iotaInt29 : 𝓞 B →+* ℤ_[29] := iotaInt root29 root29_mul_self

theorem iota29_coe (x : 𝓞 B) : iota29 (x : B) = (iotaInt29 x : ℚ_[29]) :=
  iota_coe _ _ x

/-- `P29` is the prime of `iota29`: `x ∈ P29 ↔ ‖iota29 x‖ < 1`. -/
theorem mem_P29_iff_norm_iota (x : 𝓞 B) : x ∈ P29 ↔ ‖iotaInt29 x‖ < 1 := by
  rw [padicInt_norm_lt_one_iff, iotaInt29, toZMod_iotaInt, mem_P29, res29,
    evalHom_congr toZMod_root29]

/-- Square-class representatives of `iota29 (alpha i)` in `ℚ_29^×/ℚ_29^{×2}`. -/
def squareclass29 : Fin 8 → ℤ := ![1, 1, 2, 1, 1, 2, 2, 2]

theorem iota29_alpha (i : Fin 8) : ∃ z : ℚ_[29], z ≠ 0 ∧
    iota29 ((alpha i : 𝓞 B) : B) = (squareclass29 i : ℚ_[29]) * z ^ 2 := by
  fin_cases i
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root29 0 (1) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root29 1 (1) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root29 2 (2) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root29 3 (1) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root29 4 (1) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root29 5 (2) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root29 6 (2) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root29 7 (2) (by decide)
/-- The root of `X² - X - 60` in `ℤ_29` with `r ≡ 28 (mod 29)`. -/
def root29' : ℤ_[29] := (exists_omegaRoot (p := 29) 28 (by decide) (by decide)).choose

theorem root29'_mul_self : root29' * root29' = root29' + 60 :=
  (exists_omegaRoot (p := 29) 28 (by decide) (by decide)).choose_spec.1

theorem toZMod_root29' : PadicInt.toZMod root29' = 28 := by
  rw [root29', (exists_omegaRoot (p := 29) 28 (by decide) (by decide)).choose_spec.2]; decide

/-- The embedding `B → ℚ_29` at `P29'` (`ω ↦ root29'`). -/
def iota29' : B →ₐ[ℚ] ℚ_[29] := iota root29' root29'_mul_self

/-- The embedding `𝓞 B → ℤ_29` at `P29'`. -/
def iotaInt29' : 𝓞 B →+* ℤ_[29] := iotaInt root29' root29'_mul_self

theorem iota29'_coe (x : 𝓞 B) : iota29' (x : B) = (iotaInt29' x : ℚ_[29]) :=
  iota_coe _ _ x

/-- `P29'` is the prime of `iota29'`: `x ∈ P29' ↔ ‖iota29' x‖ < 1`. -/
theorem mem_P29'_iff_norm_iota (x : 𝓞 B) : x ∈ P29' ↔ ‖iotaInt29' x‖ < 1 := by
  rw [padicInt_norm_lt_one_iff, iotaInt29', toZMod_iotaInt, mem_P29', res29',
    evalHom_congr toZMod_root29']

/-- Square-class representatives of `iota29' (alpha i)` in `ℚ_29^×/ℚ_29^{×2}`. -/
def squareclass29' : Fin 8 → ℤ := ![1, 1, 1, 2, 2, 1, 2, 2]

theorem iota29'_alpha (i : Fin 8) : ∃ z : ℚ_[29], z ≠ 0 ∧
    iota29' ((alpha i : 𝓞 B) : B) = (squareclass29' i : ℚ_[29]) * z ^ 2 := by
  fin_cases i
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root29' 0 (1) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root29' 1 (1) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root29' 2 (1) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root29' 3 (2) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root29' 4 (2) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root29' 5 (1) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root29' 6 (2) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root29' 7 (2) (by decide)
-- END Generated by scripts/sqrt241/generate_base_tables.py local.


/-! ## The two embeddings above `p` differ by `σ` -/

section Conjugate

theorem omegaRoot_eq_one_sub {R : Type*} [CommRing R] [IsDomain R] {r r' : R}
    (hr : r * r = r + 60) (hr' : r' * r' = r' + 60) (hne : r ≠ r') : r' = 1 - r := by
  have h : (r - r') * (r + r' - 1) = 0 := by linear_combination hr - hr'
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · linear_combination h

theorem one_sub_root_mul_self {R : Type*} [CommRing R] {r : R} (hr : r * r = r + 60) :
    (1 - r) * (1 - r) = (1 - r) + 60 := by
  linear_combination hr

variable {p : ℕ} [Fact p.Prime]

theorem iota_congr {r r' : ℤ_[p]} (h : r = r') (hr : r * r = r + 60) :
    iota r hr = iota r' (h ▸ hr) := by
  subst h
  rfl

theorem iota_one_sub (r : ℤ_[p]) (hr : r * r = r + 60) :
    iota (1 - r) (one_sub_root_mul_self hr) = (iota r hr).comp (sigma : B →ₐ[ℚ] B) := by
  apply algHom_ext
  have h1 : ((sigma : B →ₐ[ℚ] B) : B → B) sqrt241 = -sqrt241 := sigma_sqrt241
  rw [iota_sqrt241, AlgHom.comp_apply, h1, map_neg, iota_sqrt241]
  push_cast
  ring

theorem root2'_eq : root2' = 1 - root2 :=
  omegaRoot_eq_one_sub root2_mul_self root2'_mul_self fun h ↦ by
    have := congrArg PadicInt.toZMod h
    rw [toZMod_root2, toZMod_root2'] at this
    exact absurd this (by decide)

theorem root3'_eq : root3' = 1 - root3 :=
  omegaRoot_eq_one_sub root3_mul_self root3'_mul_self fun h ↦ by
    have := congrArg PadicInt.toZMod h
    rw [toZMod_root3, toZMod_root3'] at this
    exact absurd this (by decide)

theorem root5_eq : root5 = 1 - root5' :=
  omegaRoot_eq_one_sub root5'_mul_self root5_mul_self fun h ↦ by
    have := congrArg PadicInt.toZMod h
    rw [toZMod_root5, toZMod_root5'] at this
    exact absurd this (by decide)

theorem root29'_eq : root29' = 1 - root29 :=
  omegaRoot_eq_one_sub root29_mul_self root29'_mul_self fun h ↦ by
    have := congrArg PadicInt.toZMod h
    rw [toZMod_root29, toZMod_root29'] at this
    exact absurd this (by decide)

/-- The embedding at `𝔭₂'` is the embedding at `𝔭₂` composed with `σ`. -/
theorem iota2'_eq_comp_sigma : iota2' = iota2.comp (sigma : B →ₐ[ℚ] B) :=
  (iota_congr root2'_eq root2'_mul_self).trans (iota_one_sub root2 root2_mul_self)

theorem iota3'_eq_comp_sigma : iota3' = iota3.comp (sigma : B →ₐ[ℚ] B) :=
  (iota_congr root3'_eq root3'_mul_self).trans (iota_one_sub root3 root3_mul_self)

theorem iota5_eq_comp_sigma : iota5 = iota5'.comp (sigma : B →ₐ[ℚ] B) :=
  (iota_congr root5_eq root5_mul_self).trans (iota_one_sub root5' root5'_mul_self)

theorem iota29'_eq_comp_sigma : iota29' = iota29.comp (sigma : B →ₐ[ℚ] B) :=
  (iota_congr root29'_eq root29'_mul_self).trans (iota_one_sub root29 root29_mul_self)

end Conjugate

end UnitDistance.Sqrt241.Base
