module

public import UnitDistance.Sqrt241.Genus.Integers

@[expose] public section
set_option backward.privateInPublic true


/-!
# Decomposition and inertia groups of the canonical genus field

Let `P` be a prime of `𝓞 E` above a rational prime `p`.

* If `p ∤ 964 = 4·241` and `p ∤ 4 N(α_i)` for all `i` (that is, `p ∉ {2,3,5,241}`),
  the inertia group of `P` is trivial: an inertia element moving `√241` or
  some `√α_i` would put `2√241` or `2√α_i` into `P`.
* If moreover `241 ≡ c² (mod p)`, the stabilizer of `P` fixes `√241`
  (it cannot exchange the two primes `(p, √241 ∓ c)` of `B`), hence has
  exponent 2.
* Above 2 the stabilizer fixes `√241` (it cannot exchange `π₂`, `π₂'`), and
  five explicit products `ρ` of genus roots with `ρ² ≡ 1 (mod π³)` are fixed
  by it (`stab_fixes_of_gamma`: otherwise `γ = π'(1+ρ)/2` gives a
  contradiction), so it has at most 8 elements.
-/

noncomputable section
open NumberField IntermediateField

namespace UnitDistance.Sqrt241.Genus

open CanonicalGenus UnitDistance.NumberFieldAnalysis
open scoped Pointwise

/-! ### Action on explicit integers -/

theorem smul_intCast_O (σ : Carrier ≃ₐ[ℚ] Carrier) (n : ℤ) : σ • (n : 𝓞 Carrier) = n := by
  apply RingOfIntegers.ext
  rw [coe_smul_O]
  simp [map_intCast]

theorem smul_bO_of_neg (σ : Carrier ≃ₐ[ℚ] Carrier) (h : σ bE = -bE) : σ • bO = -bO := by
  apply RingOfIntegers.ext
  show σ bE = -bE
  exact h

theorem smul_gO_of_neg (σ : Carrier ≃ₐ[ℚ] Carrier) (i : Fin 8) (h : σ (gE i) = -gE i) :
    σ • gO i = -gO i := by
  apply RingOfIntegers.ext
  show σ (gE i) = -gE i
  exact h

theorem smul_radO_of_neg (σ : Carrier ≃ₐ[ℚ] Carrier) (h : σ bE = -bE) (i j : Fin 8)
    (hij : star (radQ i) = -radQ j) : σ • radO i = -radO j := by
  apply RingOfIntegers.ext
  show σ (bHom (radQ i)) = -bHom (radQ j)
  rw [aut_bHom_of_neg σ h, hij, map_neg]

variable {p : ℕ} (P : Ideal (𝓞 Carrier)) [hPp : P.IsPrime] [hPl : P.LiesOver (rationalPrimeIdeal p)]

omit hPp hPl in
theorem smul_mem_of_mem_stab {σ : Gal(Carrier/ℚ)}
    (hσ : σ ∈ MulAction.stabilizer Gal(Carrier/ℚ) P) {x : 𝓞 Carrier} (hx : x ∈ P) : σ • x ∈ P := by
  have h := Ideal.smul_mem_pointwise_smul σ x P hx
  rwa [MulAction.mem_stabilizer_iff.1 hσ] at h

omit hPp in
theorem dvd_of_two_bO_mem (h : 2 * bO ∈ P) : (p : ℤ) ∣ 964 := by
  have h2 : (2 * bO) * (2 * bO) ∈ P := P.mul_mem_left _ h
  have e : (2 * bO) * (2 * bO) = ((964 : ℤ) : 𝓞 Carrier) := by
    apply ext_closure
    simp only [coe_mul_O, coe_two_O, coe_bO, coe_intCast_O]
    push_cast
    linear_combination 4 * baseRoot_sq
  rw [e] at h2
  exact (intCast_mem_iff (p := p) P 964).1 h2

omit hPp in
theorem dvd_of_two_gO_mem (i : Fin 8) (h : 2 * gO i ∈ P) : (p : ℤ) ∣ 4 * normValue i := by
  have h2 : (2 * gO i) * (2 * gO i) * conjO i ∈ P := P.mul_mem_right _ (P.mul_mem_left _ h)
  have e : (2 * gO i) * (2 * gO i) * conjO i = ((4 * normValue i : ℤ) : 𝓞 Carrier) := by
    calc (2 * gO i) * (2 * gO i) * conjO i = 4 * ((gO i * gO i) * conjO i) := by ring
      _ = 4 * (radO i * conjO i) := by rw [gO_sq]
      _ = _ := by rw [radO_mul_conjO]; push_cast; ring
  rw [e] at h2
  exact (intCast_mem_iff (p := p) P _).1 h2

/-! ### Inertia -/

omit hPp in
/-- Away from `2, 3, 5, 241` the inertia groups are trivial. -/
theorem inertia_trivial (h964 : ¬ (p : ℤ) ∣ 964) (hN : ∀ i, ¬ (p : ℤ) ∣ 4 * normValue i) :
    ∀ σ ∈ P.inertia Gal(Carrier/ℚ), σ = 1 := by
  intro σ hσ
  rw [Ideal.mem_inertia] at hσ
  have hb : σ bE = bE := by
    rcases aut_bE σ with h | h
    · exact h
    · exfalso
      have h1 := hσ bO
      rw [smul_bO_of_neg σ h] at h1
      have h2 : 2 * bO ∈ P := by
        have := P.neg_mem_iff.2 h1
        convert this using 1
        ring
      exact h964 (dvd_of_two_bO_mem P h2)
  apply aut_ext
  · simp [hb]
  · intro i
    rcases aut_gE σ hb i with h | h
    · simp [h]
    · exfalso
      have h1 := hσ (gO i)
      rw [smul_gO_of_neg σ i h] at h1
      have h2 : 2 * gO i ∈ P := by
        have := P.neg_mem_iff.2 h1
        convert this using 1
        ring
      exact hN i (dvd_of_two_gO_mem P i h2)

/-! ### Split primes -/

include hPp hPl in
/-- If `241` is a square mod `p` and `p ∤ 964`, the decomposition group fixes `√241`. -/
theorem stab_fix_bE_of_sqrt (h964 : ¬ (p : ℤ) ∣ 964) (c : ℤ) (hc : (p : ℤ) ∣ c ^ 2 - 241)
    {σ : Gal(Carrier/ℚ)} (hσ : σ ∈ MulAction.stabilizer Gal(Carrier/ℚ) P) : σ bE = bE := by
  rcases aut_bE σ with h | h
  · exact h
  exfalso
  have hprod : (bO - c) * (bO + c) ∈ P := by
    have e : (bO - c) * (bO + c) = ((241 - c ^ 2 : ℤ) : 𝓞 Carrier) := by
      apply ext_closure
      simp only [coe_mul_O, coe_sub_O, coe_add_O, coe_bO, coe_intCast_O]
      push_cast
      linear_combination baseRoot_sq
    rw [e]
    apply (intCast_mem_iff (p := p) P _).2
    rw [show (241 - c ^ 2 : ℤ) = -(c ^ 2 - 241) by ring]
    exact dvd_neg.2 hc
  rcases hPp.mem_or_mem hprod with h1 | h1
  · have h2 := smul_mem_of_mem_stab P hσ h1
    rw [smul_sub, smul_bO_of_neg σ h, smul_intCast_O] at h2
    have h3 : 2 * bO ∈ P := by
      have := P.sub_mem h1 h2
      convert this using 1
      ring
    exact h964 (dvd_of_two_bO_mem P h3)
  · have h2 := smul_mem_of_mem_stab P hσ h1
    rw [smul_add, smul_bO_of_neg σ h, smul_intCast_O] at h2
    have h3 : 2 * bO ∈ P := by
      have := P.sub_mem h1 h2
      convert this using 1
      ring
    exact h964 (dvd_of_two_bO_mem P h3)

/-! ### The dyadic primes -/

theorem radQ_two_mul_three : radQ 2 * radQ 3 = 2 := by decide +kernel
theorem radQ_three_sub_two : radQ 3 - radQ 2 = 6101 := by decide +kernel
theorem star_radQ_two : star (radQ 2) = -radQ 3 := by decide +kernel
theorem star_radQ_three : star (radQ 3) = -radQ 2 := by decide +kernel

theorem radO_two_mul_three : radO 2 * radO 3 = 2 := by
  apply ext_closure
  simp only [coe_mul_O, coe_radO, coe_two_O]
  rw [← map_mul, radQ_two_mul_three, map_ofNat]

theorem radO_three_sub_two : radO 3 - radO 2 = ((6101 : ℤ) : 𝓞 Carrier) := by
  apply ext_closure
  simp only [coe_sub_O, coe_radO, coe_intCast_O]
  rw [← map_sub, radQ_three_sub_two, map_ofNat]
  norm_num

omit hPp in
theorem not_both_dyadic (hp : p = 2) (h2 : radO 2 ∈ P) (h3 : radO 3 ∈ P) : False := by
  have h := P.sub_mem h3 h2
  rw [radO_three_sub_two, intCast_mem_iff (p := p) P] at h
  subst hp
  norm_num at h

include hPp hPl in
theorem dyadic_mem (hp : p = 2) : radO 2 ∈ P ∨ radO 3 ∈ P := by
  apply hPp.mem_or_mem
  rw [radO_two_mul_three]
  have := (intCast_mem_iff (p := p) P 2).2 (by subst hp; norm_num)
  simpa using this

include hPp hPl in
/-- Above 2 the decomposition group fixes `√241`. -/
theorem stab_fix_bE_two (hp : p = 2) {σ : Gal(Carrier/ℚ)}
    (hσ : σ ∈ MulAction.stabilizer Gal(Carrier/ℚ) P) : σ bE = bE := by
  rcases aut_bE σ with h | h
  · exact h
  exfalso
  rcases dyadic_mem P hp with h2 | h3
  · have h' := smul_mem_of_mem_stab P hσ h2
    rw [smul_radO_of_neg σ h 2 3 star_radQ_two] at h'
    exact not_both_dyadic P hp h2 (P.neg_mem_iff.1 h')
  · have h' := smul_mem_of_mem_stab P hσ h3
    rw [smul_radO_of_neg σ h 3 2 star_radQ_three] at h'
    exact not_both_dyadic P hp (P.neg_mem_iff.1 h') h3

include hPp in
/-- The `γ`-argument: a product `ρ` of genus roots with `ρ² ≡ 1 (mod π³)` is
fixed by every element of the decomposition group fixing `√241`. -/
theorem stab_fixes_of_gamma {σ : Gal(Carrier/ℚ)}
    (hσ : σ ∈ MulAction.stabilizer Gal(Carrier/ℚ) P) (hB : σ bE = bE) (j k : Fin 8)
    (hπ : radO j ∈ P) (hu : radO k ∉ P) (hjk : radQ j * radQ k = 2)
    (ρ : Carrier) (z κ : Q241) (hρ : ρ ^ 2 = bHom z)
    (hκ1 : (QuadraticAlgebra.trace κ).den = 1) (hκ2 : (QuadraticAlgebra.norm κ).den = 1)
    (hκ : κ * radQ j ^ 3 = 1 - z) :
    σ ρ = ρ := by
  have hσρ2 : (σ ρ) ^ 2 = ρ ^ 2 := by
    rw [← map_pow, hρ, aut_bHom_of_fix σ hB]
  rcases eq_or_eq_neg_of_sq_eq_sq' hσρ2 with h | h
  · exact h
  exfalso
  set u : Carrier := bHom (radQ k) with hu_def
  set π : Carrier := bHom (radQ j) with hπ_def
  set κE : Carrier := bHom κ with hκE_def
  have hjk' : π * u = 2 := by
    rw [hπ_def, hu_def, ← map_mul, hjk, map_ofNat]
  have hκ' : κE * π ^ 3 = 1 - ρ ^ 2 := by
    rw [hκE_def, hπ_def, ← map_pow, ← map_mul, hκ, map_sub, map_one, hρ]
  set γ : Carrier := u * (1 + ρ) / 2 with hγ_def
  have hγeq : γ ^ 2 - u * γ + π * κE = 0 := by
    rw [hγ_def]
    linear_combination (u ^ 2 / 4) * hκ' - (π * κE * (π * u + 2) / 4) * hjk'
  have hγint : IsIntegral ℤ γ := by
    have hA : IsIntegral (𝓞 Carrier) γ := by
      refine ⟨Polynomial.X ^ 2 - Polynomial.C (radO k) * Polynomial.X +
        Polynomial.C (radO j * toO κE (isIntegral_bHom κ hκ1 hκ2)), ?_, ?_⟩
      · monicity!
      · simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
          Polynomial.eval₂_X_pow, Polynomial.eval₂_C, Polynomial.eval₂_X]
        rw [map_mul]
        exact hγeq
    exact isIntegral_trans (A := 𝓞 Carrier) γ hA
  set γO : 𝓞 Carrier := toO γ hγint with hγO_def
  have hmem : γO * (radO k - γO) ∈ P := by
    have e : γO * (radO k - γO) = radO j * toO κE (isIntegral_bHom κ hκ1 hκ2) := by
      apply RingOfIntegers.ext
      change γ * (u - γ) = π * κE
      linear_combination -hγeq
    rw [e]
    exact P.mul_mem_right _ hπ
  have hsγ : σ • γO = radO k - γO := by
    apply RingOfIntegers.ext
    rw [coe_smul_O]
    change σ γ = u - γ
    rw [hγ_def, map_div₀, map_mul, map_add, map_one, h, map_ofNat, hu_def,
      aut_bHom_of_fix σ hB]
    ring
  have hsu : σ • radO k = radO k := by
    apply RingOfIntegers.ext
    rw [coe_smul_O]
    simp only [radO, toO]
    exact aut_bHom_of_fix σ hB _
  rcases hPp.mem_or_mem hmem with h1 | h1
  · have h2 := smul_mem_of_mem_stab P hσ h1
    rw [hsγ] at h2
    apply hu
    have := P.add_mem h1 h2
    simpa using this
  · have h2 := smul_mem_of_mem_stab P hσ h1
    rw [smul_sub, hsu, hsγ, sub_sub_cancel] at h2
    apply hu
    have := P.add_mem h1 h2
    simpa using this

/-- A group of automorphisms fixing `√241`, each determined by its signs on
three genus roots, has at most 8 elements. -/
theorem card_le_eight_of_det (S : Subgroup Gal(Carrier/ℚ)) (i0 i1 i2 : Fin 8)
    (hB : ∀ σ ∈ S, σ bE = bE)
    (hdet : ∀ σ ∈ S, ∀ τ ∈ S, σ (gE i0) = τ (gE i0) → σ (gE i1) = τ (gE i1) →
      σ (gE i2) = τ (gE i2) → σ = τ) :
    Nat.card S ≤ 8 := by
  classical
  let f : S → Bool × Bool × Bool := fun σ =>
    (decide (σ.1 (gE i0) = gE i0), decide (σ.1 (gE i1) = gE i1), decide (σ.1 (gE i2) = gE i2))
  have hsign : ∀ σ ∈ S, ∀ τ ∈ S, ∀ i : Fin 8,
      decide (σ (gE i) = gE i) = decide (τ (gE i) = gE i) → σ (gE i) = τ (gE i) := by
    intro σ hσ τ hτ i hdec
    have hne : gE i ≠ -gE i := by
      intro h
      have h2 : (2 : Carrier) * gE i = 0 := by linear_combination h
      rcases mul_eq_zero.1 h2 with h3 | h3
      · norm_num at h3
      · exact gE_ne_zero i h3
    rcases aut_gE σ (hB σ hσ) i with h1 | h1 <;> rcases aut_gE τ (hB τ hτ) i with h2 | h2
    · rw [h1, h2]
    · rw [h1, h2] at hdec
      simp [hne.symm] at hdec
    · rw [h1, h2] at hdec
      simp [hne.symm] at hdec
    · rw [h1, h2]
  have hinj : Function.Injective f := by
    intro σ τ hστ
    simp only [f, Prod.mk.injEq] at hστ
    apply Subtype.ext
    exact hdet σ.1 σ.2 τ.1 τ.2 (hsign _ σ.2 _ τ.2 i0 hστ.1) (hsign _ σ.2 _ τ.2 i1 hστ.2.1)
      (hsign _ σ.2 _ τ.2 i2 hστ.2.2)
  have h := Nat.card_le_card_of_injective f hinj
  simpa using h

/-! Explicit dyadic data: `κ = (1 - z)/π³` for the five products `z` of
radicands that are squares in `ℚ₂` at the prime `π`. -/

/-- Case `π₂ ∈ P`: `π = radQ 2`, `π' = radQ 3`. -/
theorem kappaA1 : (⟨12298163166375688078043, -792194329617952320064⟩ : Q241) * radQ 2 ^ 3 =
    1 - radQ 1 * radQ 3 := by decide +kernel
theorem kappaA2 : (⟨-866477098293, 55814696449⟩ : Q241) * radQ 2 ^ 3 = 1 - radQ 4 := by
  decide +kernel
theorem kappaA3 : (⟨97460870816282755, -6278006575110389⟩ : Q241) * radQ 2 ^ 3 =
    1 - radQ 0 * radQ 1 * radQ 5 := by decide +kernel
theorem kappaA4 : (⟨1314292126482129535550, -84660998229990265442⟩ : Q241) * radQ 2 ^ 3 =
    1 - radQ 1 * radQ 6 := by decide +kernel
theorem kappaA5 : (⟨28604271593 / 2, -1842563109 / 2⟩ : Q241) * radQ 2 ^ 3 = 1 - radQ 7 := by
  decide +kernel

/-- Case `π₂' ∈ P`: `π = radQ 3`, `π' = radQ 2`. -/
theorem kappaB1 : (⟨-28387805047 / 2, -1828619273 / 2⟩ : Q241) * radQ 3 ^ 3 =
    1 - radQ 1 * radQ 2 := by decide +kernel
theorem kappaB2 : (⟨-28386585623 / 2, -1828540723 / 2⟩ : Q241) * radQ 3 ^ 3 =
    1 - radQ 1 * radQ 4 := by decide +kernel
theorem kappaB3 : (⟨866477098293, 55814696449⟩ : Q241) * radQ 3 ^ 3 = 1 - radQ 5 := by
  decide +kernel
theorem kappaB4 : (⟨-28604271593 / 2, -1842563109 / 2⟩ : Q241) * radQ 3 ^ 3 = 1 - radQ 6 := by
  decide +kernel
theorem kappaB5 : (⟨-28386715933 / 2, -1828549117 / 2⟩ : Q241) * radQ 3 ^ 3 =
    1 - radQ 0 * radQ 1 * radQ 7 := by decide +kernel

theorem sq_gE_mul (i j : Fin 8) : (gE i * gE j) ^ 2 = bHom (radQ i * radQ j) := by
  rw [mul_pow, gE_sq, gE_sq, map_mul, bHom_radQ, bHom_radQ]

theorem sq_gE_mul3 (i j k : Fin 8) :
    (gE i * gE j * gE k) ^ 2 = bHom (radQ i * radQ j * radQ k) := by
  rw [mul_pow, mul_pow, gE_sq, gE_sq, gE_sq, map_mul, map_mul, bHom_radQ, bHom_radQ, bHom_radQ]

theorem sq_gE (i : Fin 8) : (gE i) ^ 2 = bHom (radQ i) := by
  rw [gE_sq, bHom_radQ]

theorem cancel_left {a x y : Carrier} (ha : a ≠ 0) (h : a * x = a * y) : x = y :=
  mul_left_cancel₀ ha h

theorem aut_gE_ne_zero (σ : Carrier ≃ₐ[ℚ] Carrier) (i : Fin 8) : σ (gE i) ≠ 0 := by
  intro h
  apply gE_ne_zero i
  have := congrArg σ.symm h
  simpa using this

include hPp hPl in
/-- Above 2 the decomposition group has at most 8 elements. -/
theorem card_stab_two_le (hp : p = 2) :
    Nat.card (MulAction.stabilizer Gal(Carrier/ℚ) P) ≤ 8 := by
  have hB : ∀ σ ∈ MulAction.stabilizer Gal(Carrier/ℚ) P, σ bE = bE :=
    fun σ hσ => stab_fix_bE_two P hp hσ
  rcases dyadic_mem P hp with h2 | h3
  · have hu : radO 3 ∉ P := fun h3 => not_both_dyadic P hp h2 h3
    have fix : ∀ σ ∈ MulAction.stabilizer Gal(Carrier/ℚ) P,
        σ (gE 1 * gE 3) = gE 1 * gE 3 ∧ σ (gE 4) = gE 4 ∧
        σ (gE 0 * gE 1 * gE 5) = gE 0 * gE 1 * gE 5 ∧ σ (gE 1 * gE 6) = gE 1 * gE 6 ∧
        σ (gE 7) = gE 7 := by
      intro σ hσ
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact stab_fixes_of_gamma P hσ (hB σ hσ) 2 3 h2 hu radQ_two_mul_three _ _ _
          (sq_gE_mul 1 3) (by decide +kernel) (by decide +kernel) kappaA1
      · exact stab_fixes_of_gamma P hσ (hB σ hσ) 2 3 h2 hu radQ_two_mul_three _ _ _
          (sq_gE 4) (by decide +kernel) (by decide +kernel) kappaA2
      · exact stab_fixes_of_gamma P hσ (hB σ hσ) 2 3 h2 hu radQ_two_mul_three _ _ _
          (sq_gE_mul3 0 1 5) (by decide +kernel) (by decide +kernel) kappaA3
      · exact stab_fixes_of_gamma P hσ (hB σ hσ) 2 3 h2 hu radQ_two_mul_three _ _ _
          (sq_gE_mul 1 6) (by decide +kernel) (by decide +kernel) kappaA4
      · exact stab_fixes_of_gamma P hσ (hB σ hσ) 2 3 h2 hu radQ_two_mul_three _ _ _
          (sq_gE 7) (by decide +kernel) (by decide +kernel) kappaA5
    apply card_le_eight_of_det _ 0 1 2 hB
    intro σ hσ τ hτ h0 h1 h2'
    obtain ⟨s13, s4, s015, s16, s7⟩ := fix σ hσ
    obtain ⟨t13, t4, t015, t16, t7⟩ := fix τ hτ
    simp only [map_mul] at s13 s015 s16 t13 t015 t16
    have e3 : σ (gE 3) = τ (gE 3) :=
      cancel_left (aut_gE_ne_zero σ 1) (by rw [s13, h1, t13])
    have e4 : σ (gE 4) = τ (gE 4) := by rw [s4, t4]
    have e5 : σ (gE 5) = τ (gE 5) :=
      cancel_left (mul_ne_zero (aut_gE_ne_zero σ 0) (aut_gE_ne_zero σ 1))
        (by rw [s015, h0, h1, t015])
    have e6 : σ (gE 6) = τ (gE 6) :=
      cancel_left (aut_gE_ne_zero σ 1) (by rw [s16, h1, t16])
    have e7 : σ (gE 7) = τ (gE 7) := by rw [s7, t7]
    apply aut_ext (by rw [hB σ hσ, hB τ hτ])
    intro i
    fin_cases i
    exacts [h0, h1, h2', e3, e4, e5, e6, e7]
  · have hu : radO 2 ∉ P := fun h2 => not_both_dyadic P hp h2 h3
    have hjk : radQ 3 * radQ 2 = 2 := by rw [mul_comm]; exact radQ_two_mul_three
    have fix : ∀ σ ∈ MulAction.stabilizer Gal(Carrier/ℚ) P,
        σ (gE 1 * gE 2) = gE 1 * gE 2 ∧ σ (gE 1 * gE 4) = gE 1 * gE 4 ∧
        σ (gE 5) = gE 5 ∧ σ (gE 6) = gE 6 ∧
        σ (gE 0 * gE 1 * gE 7) = gE 0 * gE 1 * gE 7 := by
      intro σ hσ
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact stab_fixes_of_gamma P hσ (hB σ hσ) 3 2 h3 hu hjk _ _ _
          (sq_gE_mul 1 2) (by decide +kernel) (by decide +kernel) kappaB1
      · exact stab_fixes_of_gamma P hσ (hB σ hσ) 3 2 h3 hu hjk _ _ _
          (sq_gE_mul 1 4) (by decide +kernel) (by decide +kernel) kappaB2
      · exact stab_fixes_of_gamma P hσ (hB σ hσ) 3 2 h3 hu hjk _ _ _
          (sq_gE 5) (by decide +kernel) (by decide +kernel) kappaB3
      · exact stab_fixes_of_gamma P hσ (hB σ hσ) 3 2 h3 hu hjk _ _ _
          (sq_gE 6) (by decide +kernel) (by decide +kernel) kappaB4
      · exact stab_fixes_of_gamma P hσ (hB σ hσ) 3 2 h3 hu hjk _ _ _
          (sq_gE_mul3 0 1 7) (by decide +kernel) (by decide +kernel) kappaB5
    apply card_le_eight_of_det _ 0 1 3 hB
    intro σ hσ τ hτ h0 h1 h3'
    obtain ⟨s12, s14, s5, s6, s017⟩ := fix σ hσ
    obtain ⟨t12, t14, t5, t6, t017⟩ := fix τ hτ
    simp only [map_mul] at s12 s14 s017 t12 t14 t017
    have e2 : σ (gE 2) = τ (gE 2) :=
      cancel_left (aut_gE_ne_zero σ 1) (by rw [s12, h1, t12])
    have e4 : σ (gE 4) = τ (gE 4) :=
      cancel_left (aut_gE_ne_zero σ 1) (by rw [s14, h1, t14])
    have e5 : σ (gE 5) = τ (gE 5) := by rw [s5, t5]
    have e6 : σ (gE 6) = τ (gE 6) := by rw [s6, t6]
    have e7 : σ (gE 7) = τ (gE 7) :=
      cancel_left (mul_ne_zero (aut_gE_ne_zero σ 0) (aut_gE_ne_zero σ 1))
        (by rw [s017, h0, h1, t017])
    apply aut_ext (by rw [hB σ hσ, hB τ hτ])
    intro i
    fin_cases i
    exacts [h0, h1, e2, h3', e4, e5, e6, e7]

end UnitDistance.Sqrt241.Genus
