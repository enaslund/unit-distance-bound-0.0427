module

public import UnitDistance.Sqrt241.Discriminant.Dyadic
public import UnitDistance.Sqrt241.Discriminant.Tame
public import UnitDistance.Sqrt241.CanonicalGenus
public import UnitDistance.Sqrt241.Witness

@[expose] public section
set_option backward.privateInPublic true


/-!
# The root discriminant of the tower fields over `ℚ(√241)`

For a number field `K`, Galois over `ℚ`, with ramification indices `8, 2, 2, 2` at
`2, 3, 5, 241` and `1` elsewhere,

    log rd(K) = Σ_p v_p |disc K| / [K:ℚ] · log p ≤ (9/4) log 2 + (1/2) log 3615,

provided `K` contains `√-3`, `√5`, `√241` (tame primes, `Discriminant.Tame`) and the
dyadic data of `Discriminant.Dyadic`: `√2`, `√π₂'`, `√β₁`, `√(-π₂)`, `√β₂`.

* `log_rootDiscriminant_le_of_elements`: the statement with explicit elements of `K`;
* `UnitDistance.Sqrt241.log_rootDiscriminant_le`: the statement with
  `[Algebra CanonicalGenus.Carrier K]` and square roots `s₁`, `s₂` of `β₁`, `β₂ ∈ E`.
-/

noncomputable section
open NumberField

namespace UnitDistance.Sqrt241.Discriminant

open UnitDistance.NumberFieldAnalysis

variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]

theorem not_isSquare_neg_three : ¬ IsSquare ((-3 : ℤ) : ℚ) := by
  rintro ⟨q, hq⟩
  have : 0 ≤ q * q := mul_self_nonneg q
  push_cast at hq
  linarith

theorem not_isSquare_five : ¬ IsSquare ((5 : ℤ) : ℚ) := by
  push_cast
  decide +kernel

theorem not_isSquare_241 : ¬ IsSquare ((241 : ℤ) : ℚ) := by
  push_cast
  decide +kernel

/-- **Root discriminant bound from the dyadic exponent.** `K` Galois over `ℚ`, containing
square roots of `-3`, `5`, `241`, with ramification index `2` at `3, 5, 241`, unramified
outside `{2, 3, 5, 241}`, and with dyadic discriminant exponent `8 v₂ |disc K| ≤ 18 [K:ℚ]`
(supplied by `Dyadic.Realization.eight_mul_factorization_two_le` from the explicit dyadic
certificate, or by the comparison with the verified ℚ retained field in `RouteT`). -/
theorem log_rootDiscriminant_le_of_dyadic (x₃ x₅ r : K) (hx₃ : x₃ ^ 2 = -3) (hx₅ : x₅ ^ 2 = 5)
    (hr : r * r = 241)
    (h2 : 8 * (discr K).natAbs.factorization 2 ≤ 18 * Module.finrank ℚ K)
    (he3 : (rationalPrimeIdeal 3).ramificationIdxIn (𝓞 K) = 2)
    (he5 : (rationalPrimeIdeal 5).ramificationIdxIn (𝓞 K) = 2)
    (he241 : (rationalPrimeIdeal 241).ramificationIdxIn (𝓞 K) = 2)
    (hunr : ∀ p : ℕ, p.Prime → p ∉ ({2, 3, 5, 241} : Finset ℕ) →
      (rationalPrimeIdeal p).ramificationIdxIn (𝓞 K) = 1) :
    Real.log (rootDiscriminant K) ≤ Witness.logRD := by
  have hn : (0 : ℝ) ≤ Module.finrank ℚ K := Nat.cast_nonneg _
  -- the four exponents
  have h2 : ((discr K).natAbs.factorization 2 : ℝ) ≤ 9 / 4 * Module.finrank ℚ K := by
    have h' : (8 : ℝ) * (discr K).natAbs.factorization 2 ≤ 18 * Module.finrank ℚ K := by
      exact_mod_cast h2
    linarith
  have hp3 : Nat.Prime 3 := by norm_num
  have hp5 : Nat.Prime 5 := by norm_num
  have hp241 : Nat.Prime 241 := by norm_num
  have h3 : ((discr K).natAbs.factorization 3 : ℝ) ≤ 1 / 2 * Module.finrank ℚ K := by
    have h := two_mul_factorization_discr_eq_of_sqrt_of_ramificationIdxIn (-3)
      (show Squarefree (-3 : ℤ).natAbs from (Nat.prime_iff.mp hp3).squarefree)
      not_isSquare_neg_three (by decide) x₃ (by rw [hx₃]; push_cast; ring)
      hp3 (by decide) he3
    have h' : ((discr K).natAbs.factorization 3 : ℝ) * 2 = Module.finrank ℚ K := by
      exact_mod_cast h
    linarith
  have h5 : ((discr K).natAbs.factorization 5 : ℝ) ≤ 1 / 2 * Module.finrank ℚ K := by
    have h := two_mul_factorization_discr_eq_of_sqrt_of_ramificationIdxIn 5
      (Nat.prime_iff.mp hp5).squarefree not_isSquare_five (by decide) x₅ (by rw [hx₅]; push_cast; ring)
      hp5 (by decide) he5
    have h' : ((discr K).natAbs.factorization 5 : ℝ) * 2 = Module.finrank ℚ K := by
      exact_mod_cast h
    linarith
  have h241 : ((discr K).natAbs.factorization 241 : ℝ) ≤ 1 / 2 * Module.finrank ℚ K := by
    have h := two_mul_factorization_discr_eq_of_sqrt_of_ramificationIdxIn 241
      (Nat.prime_iff.mp hp241).squarefree not_isSquare_241 (by decide) r (by rw [sq, hr]; push_cast; ring)
      hp241 (by decide) he241
    have h' : ((discr K).natAbs.factorization 241 : ℝ) * 2 = Module.finrank ℚ K := by
      exact_mod_cast h
    linarith
  -- assembly
  have hT : ∀ p, p.Prime → p ∣ (discr K).natAbs → p ∈ ({2, 3, 5, 241} : Finset ℕ) := by
    intro p hp hdvd
    by_contra hnot
    exact not_dvd_natAbs_discr_of_ramificationIdxIn_eq_one K hp (hunr p hp hnot) hdvd
  have hbound := log_rootDiscriminant_le_sum K {2, 3, 5, 241}
    (fun p => if p = 2 then 9 / 4 else 1 / 2) hT (by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl
      · simpa using h2
      · simpa using h3
      · simpa using h5
      · simpa using h241)
  refine hbound.trans (le_of_eq ?_)
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [↓reduceIte, show (3 : ℕ) ≠ 2 by decide, show (5 : ℕ) ≠ 2 by decide,
    show (241 : ℕ) ≠ 2 by decide]
  unfold Witness.logRD
  have h3615 : (3615 : ℝ) = 3 * 5 * 241 := by norm_num
  rw [h3615, Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
  push_cast
  ring

/-- **Root discriminant bound, explicit elements** (dyadic certificate `Dyadic.Realization`). -/
theorem log_rootDiscriminant_le_of_elements (T : Dyadic.Realization K) (g' s' : K)
    (hg' : g' * g' = (6101 + 393 * T.r) / 2)
    (hs' : s' * s' = (-25 - 2 * T.r) + (-139 + 9 * T.r) * g')
    (x₃ x₅ : K) (hx₃ : x₃ ^ 2 = -3) (hx₅ : x₅ ^ 2 = 5)
    (he2 : (rationalPrimeIdeal 2).ramificationIdxIn (𝓞 K) = 8)
    (he3 : (rationalPrimeIdeal 3).ramificationIdxIn (𝓞 K) = 2)
    (he5 : (rationalPrimeIdeal 5).ramificationIdxIn (𝓞 K) = 2)
    (he241 : (rationalPrimeIdeal 241).ramificationIdxIn (𝓞 K) = 2)
    (hunr : ∀ p : ℕ, p.Prime → p ∉ ({2, 3, 5, 241} : Finset ℕ) →
      (rationalPrimeIdeal p).ramificationIdxIn (𝓞 K) = 1) :
    Real.log (rootDiscriminant K) ≤ Witness.logRD :=
  log_rootDiscriminant_le_of_dyadic K x₃ x₅ T.r hx₃ hx₅ T.hr
    (T.eight_mul_factorization_two_le g' s' hg' hs' (fun Q hQ h2Q => by
      rw [ramificationIdx_eq_ramificationIdxIn K Nat.prime_two Q h2Q, he2]))
    he3 he5 he241 hunr

/-- **Root discriminant bound from one realization.** For `K` Galois over `ℚ` the
conjugate data (`√(-π₂)`, `√β₂`) are not needed. -/
theorem log_rootDiscriminant_le_of_realization (T : Dyadic.Realization K)
    (x₃ x₅ : K) (hx₃ : x₃ ^ 2 = -3) (hx₅ : x₅ ^ 2 = 5)
    (he2 : (rationalPrimeIdeal 2).ramificationIdxIn (𝓞 K) = 8)
    (he3 : (rationalPrimeIdeal 3).ramificationIdxIn (𝓞 K) = 2)
    (he5 : (rationalPrimeIdeal 5).ramificationIdxIn (𝓞 K) = 2)
    (he241 : (rationalPrimeIdeal 241).ramificationIdxIn (𝓞 K) = 2)
    (hunr : ∀ p : ℕ, p.Prime → p ∉ ({2, 3, 5, 241} : Finset ℕ) →
      (rationalPrimeIdeal p).ramificationIdxIn (𝓞 K) = 1) :
    Real.log (rootDiscriminant K) ≤ Witness.logRD :=
  log_rootDiscriminant_le_of_dyadic K x₃ x₅ T.r hx₃ hx₅ T.hr
    (T.eight_mul_factorization_two_le_of_isGalois (fun Q hQ h2Q => by
      rw [ramificationIdx_eq_ramificationIdxIn K Nat.prime_two Q h2Q, he2]))
    he3 he5 he241 hunr

end UnitDistance.Sqrt241.Discriminant

namespace UnitDistance.Sqrt241.Discriminant

open CanonicalGenus

/-- `√241` as an element of the canonical genus field `E`. -/
def rootE : Carrier := ⟨baseRoot, baseRoot_mem⟩

/-- The genus roots as elements of `E`. -/
def genusE (i : Fin 8) : Carrier := ⟨genusRoot i, genusRoot_mem i⟩

/-- `β₁ = (-25 + 2√241) + (-139 - 9√241) √π₂'` in `E` (`√π₂' = genusRoot 3`). -/
def beta₁ : Carrier := (-25 + 2 * rootE) + (-139 - 9 * rootE) * genusE 3

/-- `β₂ = (-25 - 2√241) + (-139 + 9√241) √(-π₂)` in `E`
(`√(-π₂) = genusRoot 0 · genusRoot 2`). -/
def beta₂ : Carrier := (-25 - 2 * rootE) + (-139 + 9 * rootE) * (genusE 0 * genusE 2)

theorem rootE_sq : rootE * rootE = 241 := by
  apply Subtype.ext
  change baseRoot * baseRoot = (241 : Closure)
  rw [← sq, baseRoot_sq]

theorem genusE_sq (i : Fin 8) :
    genusE i * genusE i = (radicandA i : Carrier) + (radicandB i : Carrier) * rootE := by
  apply Subtype.ext
  change genusRoot i * genusRoot i = _
  rw [← sq, genusRoot_sq, radicand]
  simp [rootE]

end UnitDistance.Sqrt241.Discriminant

namespace UnitDistance.Sqrt241

open CanonicalGenus NumberField UnitDistance.NumberFieldAnalysis Discriminant

/-- **Root discriminant of the tower fields.** `K` is Galois over `ℚ`, contains the
canonical genus field `E` and square roots of `β₁` and `β₂`, and has ramification
indices `8, 2, 2, 2` at `2, 3, 5, 241` and `1` at every other prime. -/
theorem log_rootDiscriminant_le
    (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] [Algebra Carrier K]
    (s₁ s₂ : K) (hs₁ : s₁ ^ 2 = algebraMap Carrier K beta₁)
    (hs₂ : s₂ ^ 2 = algebraMap Carrier K beta₂)
    (he2 : (rationalPrimeIdeal 2).ramificationIdxIn (𝓞 K) = 8)
    (he3 : (rationalPrimeIdeal 3).ramificationIdxIn (𝓞 K) = 2)
    (he5 : (rationalPrimeIdeal 5).ramificationIdxIn (𝓞 K) = 2)
    (he241 : (rationalPrimeIdeal 241).ramificationIdxIn (𝓞 K) = 2)
    (hunr : ∀ p : ℕ, p.Prime → p ∉ ({2, 3, 5, 241} : Finset ℕ) →
      (rationalPrimeIdeal p).ramificationIdxIn (𝓞 K) = 1) :
    Real.log (rootDiscriminant K) ≤ Witness.logRD := by
  set φ := algebraMap Carrier K with hφ
  have hr : φ rootE * φ rootE = 241 := by rw [← map_mul, rootE_sq, map_ofNat]
  have hsq : ∀ i, φ (genusE i) * φ (genusE i) =
      (radicandA i : K) + (radicandB i : K) * φ rootE := by
    intro i
    rw [← map_mul, genusE_sq, map_add, map_mul, map_ratCast, map_ratCast]
  have h2 := hsq 2
  have h3 := hsq 3
  have h0 := hsq 0
  have h4 := hsq 4
  have h5 := hsq 5
  have h6 := hsq 6
  have h7 := hsq 7
  simp only [radicandA, radicandB, Fin.isValue, Matrix.cons_val, Matrix.cons_val_zero]
    at h0 h2 h3 h4 h5 h6 h7
  push_cast at h0 h2 h3 h4 h5 h6 h7
  let T : Discriminant.Dyadic.Realization K :=
    { r := φ rootE
      t := φ (genusE 2) * φ (genusE 3)
      g := φ (genusE 3)
      s := s₁
      hr := hr
      ht := by
        linear_combination (φ (genusE 2) * φ (genusE 2)) * h3 +
          ((6101 : K) / 2 - 393 / 2 * φ rootE) * h2 + (393 ^ 2 / 4 : K) * hr
      hg := by linear_combination h3
      hs := by
        rw [← sq, hs₁, beta₁]
        simp only [map_add, map_mul, map_sub, map_neg, map_ofNat] }
  apply Discriminant.log_rootDiscriminant_le_of_elements K T (φ (genusE 0) * φ (genusE 2)) s₂
    ?_ ?_ (φ (genusE 4) * φ (genusE 5)) (φ (genusE 0) * φ (genusE 6) * φ (genusE 7)) ?_ ?_
    he2 he3 he5 he241 hunr
  · change φ (genusE 0) * φ (genusE 2) * (φ (genusE 0) * φ (genusE 2)) =
      (6101 + 393 * φ rootE) / 2
    linear_combination (φ (genusE 2) * φ (genusE 2)) * h0 + (-1 : K) * h2
  · change s₂ * s₂ = (-25 - 2 * φ rootE) + (-139 + 9 * φ rootE) * (φ (genusE 0) * φ (genusE 2))
    rw [← sq, hs₂, beta₂]
    simp only [map_add, map_mul, map_sub, map_neg, map_ofNat]
  · linear_combination (φ (genusE 5) * φ (genusE 5)) * h4 +
      ((31 : K) - 2 * φ rootE) * h5 - (4 : K) * hr
  · linear_combination (φ (genusE 6) * φ (genusE 6) * (φ (genusE 7) * φ (genusE 7))) * h0 +
      (-(φ (genusE 7) * φ (genusE 7))) * h6 + (-((326 : K) - 21 * φ rootE)) * h7 +
      (441 : K) * hr

/-- **Root discriminant of the tower fields, `√β₁` only.** Same as
`log_rootDiscriminant_le` without the square root of `β₂`: since `K` is Galois over
`ℚ`, an automorphism with `√241 ↦ -√241` supplies the conjugate data. -/
theorem log_rootDiscriminant_le_of_sqrt_beta₁
    (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] [Algebra Carrier K]
    (s₁ : K) (hs₁ : s₁ ^ 2 = algebraMap Carrier K beta₁)
    (he2 : (rationalPrimeIdeal 2).ramificationIdxIn (𝓞 K) = 8)
    (he3 : (rationalPrimeIdeal 3).ramificationIdxIn (𝓞 K) = 2)
    (he5 : (rationalPrimeIdeal 5).ramificationIdxIn (𝓞 K) = 2)
    (he241 : (rationalPrimeIdeal 241).ramificationIdxIn (𝓞 K) = 2)
    (hunr : ∀ p : ℕ, p.Prime → p ∉ ({2, 3, 5, 241} : Finset ℕ) →
      (rationalPrimeIdeal p).ramificationIdxIn (𝓞 K) = 1) :
    Real.log (rootDiscriminant K) ≤ Witness.logRD := by
  set φ := algebraMap Carrier K with hφ
  have hr : φ rootE * φ rootE = 241 := by rw [← map_mul, rootE_sq, map_ofNat]
  have hsq : ∀ i, φ (genusE i) * φ (genusE i) =
      (radicandA i : K) + (radicandB i : K) * φ rootE := by
    intro i
    rw [← map_mul, genusE_sq, map_add, map_mul, map_ratCast, map_ratCast]
  have h2 := hsq 2
  have h3 := hsq 3
  have h0 := hsq 0
  have h4 := hsq 4
  have h5 := hsq 5
  have h6 := hsq 6
  have h7 := hsq 7
  simp only [radicandA, radicandB, Fin.isValue, Matrix.cons_val, Matrix.cons_val_zero]
    at h0 h2 h3 h4 h5 h6 h7
  push_cast at h0 h2 h3 h4 h5 h6 h7
  let T : Discriminant.Dyadic.Realization K :=
    { r := φ rootE
      t := φ (genusE 2) * φ (genusE 3)
      g := φ (genusE 3)
      s := s₁
      hr := hr
      ht := by
        linear_combination (φ (genusE 2) * φ (genusE 2)) * h3 +
          ((6101 : K) / 2 - 393 / 2 * φ rootE) * h2 + (393 ^ 2 / 4 : K) * hr
      hg := by linear_combination h3
      hs := by
        rw [← sq, hs₁, beta₁]
        simp only [map_add, map_mul, map_sub, map_neg, map_ofNat] }
  apply Discriminant.log_rootDiscriminant_le_of_realization K T
    (φ (genusE 4) * φ (genusE 5)) (φ (genusE 0) * φ (genusE 6) * φ (genusE 7)) ?_ ?_
    he2 he3 he5 he241 hunr
  · linear_combination (φ (genusE 5) * φ (genusE 5)) * h4 +
      ((31 : K) - 2 * φ rootE) * h5 - (4 : K) * hr
  · linear_combination (φ (genusE 6) * φ (genusE 6) * (φ (genusE 7) * φ (genusE 7))) * h0 +
      (-(φ (genusE 7) * φ (genusE 7))) * h6 + (-((326 : K) - 21 * φ rootE)) * h7 +
      (441 : K) * hr

end UnitDistance.Sqrt241
