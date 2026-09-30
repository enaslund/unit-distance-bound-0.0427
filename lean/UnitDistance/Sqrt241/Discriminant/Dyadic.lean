module

public import UnitDistance.Sqrt241.Discriminant.DyadicModel
public import UnitDistance.Sqrt241.Discriminant.NormFactorization
public import UnitDistance.Sqrt241.Discriminant.Tame

@[expose] public section
set_option backward.privateInPublic true


/-!
# The dyadic different exponent is at most 18

Let `K` be a number field containing `r, t, g, s` with `r² = 241`, `t² = 2`,
`g² = π₂'(r)` and `s² = β₁(r, g)` (a `Realization` of the model `M4`), and let `P`
be a prime of `𝓞 K` containing `π₂ = (-6101 - 393 r)/2` with `e(P|2) ≤ 8`.
Put `y = φ(yM)` and `F = ℚ(y) ⊆ K`. Then

* `y ∈ P` (`y⁸ = π₂ u` with `u` integral);
* in `𝓞 F`, `y⁸ G(y) = -2 Kp(y)` with `Kp(y) ≡ 1 (mod y)`, so the prime
  `Q = P ∩ 𝓞 F` has `e(Q|2) ≥ 8`, hence `K/F` is unramified at `P`;
* `f'(y) ∈ 𝔇(F/ℚ)` and `f'(y) = y¹⁸ Z(y)` with `Z(y) ≡ Z(0) (mod y)` odd, so
  `v_P(f'(y)) = 18 v_P(y) ≤ 18`;
* by the tower formula `𝔇(K/ℚ) = 𝔇(K/F) · 𝔇(F/ℚ)𝓞_K`, `P¹⁹ ∤ 𝔇(K/ℚ)`
  (`not_pow_nineteen_dvd_differentIdeal`).

With a second realization with `r ↦ -r` (which swaps the two dyadic primes of
`ℚ(√241)`), this covers every prime above `2`; the norm factorization then gives
`8 · v₂ |disc K| ≤ 18 · [K : ℚ]` when every prime above 2 has `e = 8`
(`eight_mul_factorization_two_le`).
-/

noncomputable section
open NumberField Polynomial IntermediateField

namespace UnitDistance.Sqrt241.Discriminant.Dyadic

open UnitDistance.Sqrt241.Discriminant UnitDistance.NumberFieldAnalysis

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- Elements of a field realizing the generators of the model `M4`. -/
structure Realization (K : Type*) [Field K] where
  r : K
  t : K
  g : K
  s : K
  hr : r * r = 241
  ht : t * t = 2
  hg : g * g = (6101 - 393 * r) / 2
  hs : s * s = (-25 + 2 * r) + (-139 - 9 * r) * g

namespace Realization

variable {K : Type*} [Field K] [CharZero K] (T : Realization K)

/-- `M1 → K`. -/
def φ1 : M1 →+* K := quadLift (Rat.castHom K) 241 T.r (by rw [T.hr]; simp)

/-- `M2 → K`. -/
def φ2 : M2 →+* K := quadLift T.φ1 2 T.t (by rw [T.ht, map_ofNat])

theorem φ1_mk (x y : ℚ) : T.φ1 ⟨x, y⟩ = (x : K) + (y : K) * T.r := rfl

theorem φ2_mk (x y : M1) : T.φ2 ⟨x, y⟩ = T.φ1 x + T.φ1 y * T.t := rfl

/-- `M3 → K`. -/
def φ3 : M3 →+* K := quadLift T.φ2 pi2pM T.g (by
  simp only [T.hg, pi2pM, φ2_mk, φ1_mk, map_zero, zero_mul, add_zero]
  push_cast
  ring)

theorem φ3_mk (x y : M2) : T.φ3 ⟨x, y⟩ = T.φ2 x + T.φ2 y * T.g := rfl

/-- `M4 → K`. -/
def φ4 : M4 →+* K := quadLift T.φ3 beta1M T.s (by
  simp only [T.hs, beta1M, φ3_mk, φ2_mk, φ1_mk, map_zero, zero_mul, add_zero]
  push_cast
  ring)

theorem φ4_mk (x y : M3) : T.φ4 ⟨x, y⟩ = T.φ3 x + T.φ3 y * T.s := rfl

/-- The image of `π₂`. -/
def pi2 : K := (-6101 - 393 * T.r) / 2

theorem φ4_pi2M : T.φ4 pi2M = T.pi2 := by
  simp only [pi2M, φ4_mk, φ3_mk, φ2_mk, φ1_mk, map_zero, zero_mul, add_zero, pi2]
  push_cast
  ring

/-- The generator `y`. -/
def y : K := T.φ4 yM

/-- The unit `u = y⁸ / π₂`. -/
def u : K := T.φ4 uM

theorem horner_f_y : horner fL T.y = 0 := by
  rw [y, ← map_horner, f_yM, map_zero]

theorem horner_h_u : horner hL T.u = 0 := by
  rw [u, ← map_horner, h_uM, map_zero]

theorem pi2_mul_u : T.pi2 * T.u = T.y ^ 8 := by
  have h := congrArg T.φ4 u_yM
  simp only [map_mul] at h
  rw [φ4_pi2M] at h
  rw [u, h, y]
  ring

theorem pi2_mul_pi2_conj : T.pi2 * ((6101 - 393 * T.r) / 2) = 2 := by
  rw [pi2]
  linear_combination ((393 : K) ^ 2 / 4) * T.hr

/-- The conjugate realization `r ↦ -r`, from a square root `g'` of `π₂'(-r) = -π₂(r)`
and a square root `s'` of `β₁(-r, g')`. -/
def conj (g' s' : K) (hg' : g' * g' = (6101 + 393 * T.r) / 2)
    (hs' : s' * s' = (-25 - 2 * T.r) + (-139 + 9 * T.r) * g') : Realization K where
  r := -T.r
  t := T.t
  g := g'
  s := s'
  hr := by rw [neg_mul_neg, T.hr]
  ht := T.ht
  hg := by rw [hg']; ring
  hs := by rw [hs']; ring

theorem conj_pi2 (g' s' : K) (hg' hs') :
    (T.conj g' s' hg' hs').pi2 = -((6101 - 393 * T.r) / 2) := by
  simp only [conj, pi2]
  ring

/-- Transport of a realization along a ring homomorphism (e.g. a field automorphism). -/
def map {K' : Type*} [Field K'] [CharZero K'] (φ : K →+* K') : Realization K' where
  r := φ T.r
  t := φ T.t
  g := φ T.g
  s := φ T.s
  hr := by rw [← map_mul, T.hr, map_ofNat]
  ht := by rw [← map_mul, T.ht, map_ofNat]
  hg := by
    rw [← map_mul, T.hg]
    simp only [map_div₀, map_sub, map_mul, map_ofNat]
  hs := by
    rw [← map_mul, T.hs]
    simp only [map_add, map_sub, map_mul, map_neg, map_ofNat]

theorem map_pi2 {K' : Type*} [Field K'] [CharZero K'] (φ : K →+* K') :
    (T.map φ).pi2 = φ T.pi2 := by
  simp only [map, pi2, map_div₀, map_sub, map_mul, map_neg, map_ofNat]

section Integers

theorem isIntegral_y : IsIntegral ℤ T.y :=
  isIntegral_of_horner fL₀ T.y (by rw [← fL_eq]; exact T.horner_f_y)

theorem isIntegral_u : IsIntegral ℤ T.u :=
  isIntegral_of_horner hL₀ T.u (by rw [← hL_eq]; exact T.horner_h_u)

theorem isIntegral_pi2 : IsIntegral ℤ T.pi2 :=
  isIntegral_of_horner [-2, 6101] T.pi2 (by
    simp only [List.cons_append, List.nil_append, horner_cons, horner_nil, pi2]
    push_cast
    linear_combination ((393 : K) ^ 2 / 4) * T.hr)

theorem isIntegral_pi2_conj : IsIntegral ℤ ((6101 - 393 * T.r) / 2 : K) :=
  isIntegral_of_horner [-2, -6101] _ (by
    simp only [List.cons_append, List.nil_append, horner_cons, horner_nil]
    push_cast
    linear_combination ((393 : K) ^ 2 / 4) * T.hr)

def yO : 𝓞 K := ⟨T.y, T.isIntegral_y⟩
def uO : 𝓞 K := ⟨T.u, T.isIntegral_u⟩
def piO : 𝓞 K := ⟨T.pi2, T.isIntegral_pi2⟩
def piO' : 𝓞 K := ⟨(6101 - 393 * T.r) / 2, T.isIntegral_pi2_conj⟩

theorem yO_pow : T.yO ^ 8 = T.piO * T.uO := by
  apply FaithfulSMul.algebraMap_injective (𝓞 K) K
  rw [map_pow, map_mul]
  exact T.pi2_mul_u.symm

theorem piO_mul_piO' : T.piO * T.piO' = 2 := by
  apply FaithfulSMul.algebraMap_injective (𝓞 K) K
  rw [map_mul, map_ofNat]
  exact T.pi2_mul_pi2_conj

theorem horner_f_yO : horner fL T.yO = 0 := by
  apply FaithfulSMul.algebraMap_injective (𝓞 K) K
  rw [map_horner, map_zero]
  exact T.horner_f_y

end Integers

end Realization

/-! ### The valuation argument -/

section Valuation

variable {S : Type*} [CommRing S] [IsDedekindDomain S]

/-- Multiplicity of a prime ideal in a principal ideal. -/
abbrev vP (P : Ideal S) (x : S) : ℕ := multiplicity P (Ideal.span {x})

theorem vP_mul (P : Ideal S) (hP : Prime P) {x z : S} (hx : x ≠ 0) (hz : z ≠ 0) :
    vP P (x * z) = vP P x + vP P z := by
  unfold vP
  rw [← Ideal.span_singleton_mul_span_singleton]
  apply multiplicity_mul hP
  apply FiniteMultiplicity.of_prime_left hP
  rw [Ideal.span_singleton_mul_span_singleton, ne_eq, Ideal.zero_eq_bot,
    Ideal.span_singleton_eq_bot]
  exact mul_ne_zero hx hz

theorem vP_pow (P : Ideal S) (hP : Prime P) {x : S} (hx : x ≠ 0) (k : ℕ) :
    vP P (x ^ k) = k * vP P x := by
  induction k with
  | zero =>
    unfold vP
    rw [pow_zero, Ideal.span_singleton_one, ← Ideal.one_eq_top, multiplicity_eq_zero_of_not_dvd]
    · ring
    · exact hP.not_dvd_one
  | succ k ih => rw [pow_succ, vP_mul P hP (pow_ne_zero _ hx) hx, ih]; ring

theorem vP_eq_zero (P : Ideal S) {x : S} (hx : x ∉ P) : vP P x = 0 := by
  unfold vP
  apply multiplicity_eq_zero_of_not_dvd
  rwa [Ideal.dvd_span_singleton]

theorem one_le_vP (P : Ideal S) (hP : Prime P) {x : S} (hx0 : x ≠ 0) (hx : x ∈ P) :
    1 ≤ vP P x := by
  unfold vP
  have hfin : FiniteMultiplicity P (Ideal.span {x}) := by
    apply FiniteMultiplicity.of_prime_left hP
    rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  rw [← hfin.pow_dvd_iff_le_multiplicity, pow_one, Ideal.dvd_span_singleton]
  exact hx

theorem pow_dvd_span_iff (P : Ideal S) (hP : Prime P) {x : S} (hx0 : x ≠ 0) (n : ℕ) :
    P ^ n ∣ Ideal.span {x} ↔ n ≤ vP P x := by
  have hfin : FiniteMultiplicity P (Ideal.span {x}) := by
    apply FiniteMultiplicity.of_prime_left hP
    rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  exact hfin.pow_dvd_iff_le_multiplicity

/-- The ramification index over `ℤ` of a prime containing `2` is `v_P(2)`. -/
theorem ramificationIdx_eq_vP_two {R : Type*} [CommRing R] [IsDedekindDomain R] [CharZero R]
    (P : Ideal R) [P.IsPrime] (h2 : (2 : R) ∈ P) :
    P.ramificationIdx ℤ = vP P 2 := by
  have hl : P.LiesOver (rationalPrimeIdeal 2) := by
    constructor
    have hle : rationalPrimeIdeal 2 ≤ P.under ℤ := by
      rw [rationalPrimeIdeal, Ideal.span_le, Set.singleton_subset_iff]
      change algebraMap ℤ R ((2 : ℕ) : ℤ) ∈ P
      simpa using h2
    exact (rationalPrimeIdeal_isMaximal Nat.prime_two).eq_of_le
      (Ideal.comap_ne_top _ (Ideal.IsPrime.ne_top ‹_›)) hle
  have hmap : (rationalPrimeIdeal 2).map (algebraMap ℤ R) = Ideal.span {(2 : R)} := by
    rw [rationalPrimeIdeal, Ideal.map_span, Set.image_singleton]
    simp
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (rationalPrimeIdeal 2) P
    (by rw [hmap, ne_eq, Ideal.span_singleton_eq_bot]; exact two_ne_zero), hmap]

end Valuation

namespace Realization

variable {K : Type*} [Field K] [NumberField K] (T : Realization K)

/-- The subfield `F = ℚ(y)`. -/
abbrev F : IntermediateField ℚ K := ℚ⟮T.y⟯

/-- `y` as an element of `F`. -/
def yF' : T.F := IntermediateField.AdjoinSimple.gen ℚ T.y

theorem coe_yF' : ((T.yF' : T.F) : K) = T.y := rfl

theorem horner_f_yF' : horner fL T.yF' = 0 := by
  apply FaithfulSMul.algebraMap_injective T.F K
  rw [map_horner, map_zero]
  exact T.horner_f_y

/-- `y` as an algebraic integer of `F`. -/
def yF : 𝓞 T.F :=
  ⟨T.yF', isIntegral_of_horner fL₀ T.yF' (by rw [← fL_eq]; exact T.horner_f_yF')⟩

theorem algebraMap_yF : algebraMap (𝓞 T.F) (𝓞 K) T.yF = T.yO := by
  apply FaithfulSMul.algebraMap_injective (𝓞 K) K
  rfl

theorem horner_f_yF : horner fL T.yF = 0 := by
  apply FaithfulSMul.algebraMap_injective (𝓞 T.F) T.F
  rw [map_horner, map_zero]
  exact T.horner_f_yF'

theorem adjoin_yF : Algebra.adjoin ℚ {algebraMap (𝓞 T.F) T.F T.yF} = ⊤ := by
  have hint : IsIntegral ℚ T.y := (T.isIntegral_y).tower_top
  have h := (IntermediateField.adjoin.powerBasis hint).adjoin_gen_eq_top
  rw [IntermediateField.adjoin.powerBasis_gen] at h
  exact h

/-- `f'(y)` lies in the different of `F/ℚ`. -/
theorem hornerD_mem_different : hornerD fL T.yF ∈ differentIdeal ℤ (𝓞 T.F) := by
  have hmem := aeval_derivative_mem_differentIdeal ℤ ℚ T.F T.yF T.adjoin_yF
  have hroot : aeval T.yF (hornerPoly fL) = 0 := by
    rw [aeval_hornerPoly, T.horner_f_yF]
  have hint : IsIntegral ℤ T.yF := RingOfIntegers.isIntegral T.yF
  obtain ⟨q, hq⟩ := minpoly.isIntegrallyClosed_dvd hint hroot
  rw [← aeval_derivative_hornerPoly, hq, derivative_mul, map_add, map_mul, map_mul,
    minpoly.aeval, zero_mul, add_zero]
  exact (differentIdeal ℤ (𝓞 T.F)).mul_mem_right _ hmem

/-- **Dyadic different bound.** For a prime `P` of `𝓞 K` containing `π₂` whose
ramification index over `ℤ` is at most `8`, `P¹⁹ ∤ 𝔇(K/ℚ)`. -/
theorem not_pow_nineteen_dvd_differentIdeal (P : Ideal (𝓞 K)) [hP : P.IsPrime]
    (hπ : T.piO ∈ P) (he : P.ramificationIdx ℤ ≤ 8) :
    ¬ P ^ 19 ∣ differentIdeal ℤ (𝓞 K) := by
  -- `y ∈ P` and `2 ∈ P`
  have hyP : T.yO ∈ P := hP.mem_of_pow_mem 8 (by rw [T.yO_pow]; exact P.mul_mem_right _ hπ)
  have h2P : (2 : 𝓞 K) ∈ P := by
    rw [← T.piO_mul_piO']
    exact P.mul_mem_right _ hπ
  have hP0 : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at h2P
    exact two_ne_zero h2P
  have hPprime : Prime P := Ideal.prime_of_isPrime hP0 hP
  -- the prime `Q` of `F`
  set Q : Ideal (𝓞 T.F) := P.under (𝓞 T.F) with hQdef
  have hQ : Q.IsPrime := Ideal.comap_isPrime _ P
  have hPQ : P.LiesOver Q := ⟨rfl⟩
  have hyQ : T.yF ∈ Q := by
    change algebraMap (𝓞 T.F) (𝓞 K) T.yF ∈ P
    rw [T.algebraMap_yF]
    exact hyP
  have h2Q : (2 : 𝓞 T.F) ∈ Q := by
    change algebraMap (𝓞 T.F) (𝓞 K) 2 ∈ P
    rw [map_ofNat]
    exact h2P
  have hQ0 : Q ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at h2Q
    exact two_ne_zero h2Q
  have hQprime : Prime Q := Ideal.prime_of_isPrime hQ0 hQ
  -- `e(Q|2) ≥ 8`
  have hsplitF := f_split T.yF
  rw [T.horner_f_yF] at hsplitF
  have hKpQ : (1 + T.yF * horner Kp₁L T.yF) ∉ Q := by
    intro h
    apply hQ.ne_top
    rw [Ideal.eq_top_iff_one]
    have := Q.sub_mem h (Q.mul_mem_right (horner Kp₁L T.yF) hyQ)
    simpa using this
  have hy0F : T.yF ≠ 0 := by
    intro h
    rw [h] at hsplitF
    simp at hsplitF
  have heQ : 8 ≤ Q.ramificationIdx ℤ := by
    rw [ramificationIdx_eq_vP_two Q h2Q]
    have hG0 : horner GhiL T.yF ≠ 0 := by
      intro h
      rw [h, mul_zero, zero_add] at hsplitF
      have : (1 + T.yF * horner Kp₁L T.yF) = 0 := by
        have h2 : (2 : 𝓞 T.F) ≠ 0 := two_ne_zero
        exact (mul_eq_zero.mp hsplitF.symm).resolve_left h2
      exact hKpQ (this ▸ Q.zero_mem)
    have hK0 : (1 + T.yF * horner Kp₁L T.yF) ≠ 0 := fun h => hKpQ (h ▸ Q.zero_mem)
    have heq : T.yF ^ 8 * horner GhiL T.yF = -2 * (1 + T.yF * horner Kp₁L T.yF) := by
      linear_combination (-1 : 𝓞 T.F) * hsplitF
    have hv := congrArg (vP Q) heq
    rw [vP_mul Q hQprime (pow_ne_zero _ hy0F) hG0, vP_pow Q hQprime hy0F,
      show (-2 : 𝓞 T.F) * (1 + T.yF * horner Kp₁L T.yF) =
        (-1) * (2 * (1 + T.yF * horner Kp₁L T.yF)) by ring,
      vP_mul Q hQprime (by norm_num) (mul_ne_zero two_ne_zero hK0),
      vP_mul Q hQprime two_ne_zero hK0, vP_eq_zero Q hKpQ,
      vP_eq_zero Q (fun h => hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ h isUnit_neg_one))] at hv
    have h1 := one_le_vP Q hQprime hy0F hyQ
    omega
  -- `K/F` is unramified at `P`
  have ht := Ideal.ramificationIdx_tower (R := ℤ) Q P
  have hrel : P.ramificationIdx (𝓞 T.F) = 1 := by
    have hpos : 0 < P.ramificationIdx (𝓞 T.F) := Ideal.ramificationIdx_pos P (𝓞 T.F)
    by_contra hne
    have h2le : 2 ≤ P.ramificationIdx (𝓞 T.F) := by omega
    have : Q.ramificationIdx ℤ * 2 ≤ Q.ramificationIdx ℤ * P.ramificationIdx (𝓞 T.F) :=
      Nat.mul_le_mul_left _ h2le
    omega
  have hunr : Algebra.IsUnramifiedAt (𝓞 T.F) P := Ideal.ramificationIdx_eq_one_iff.mp hrel
  have hndvd : ¬ P ∣ differentIdeal (𝓞 T.F) (𝓞 K) := not_dvd_differentIdeal_iff.mpr hunr
  -- the explicit element of the different
  set x : 𝓞 K := algebraMap (𝓞 T.F) (𝓞 K) (hornerD fL T.yF) with hxdef
  have hxmem : x ∈ (differentIdeal ℤ (𝓞 T.F)).map (algebraMap (𝓞 T.F) (𝓞 K)) :=
    Ideal.mem_map_of_mem _ T.hornerD_mem_different
  have hxval : x = T.yO ^ 18 * horner ZL T.yO := by
    rw [hxdef, map_hornerD, T.algebraMap_yF, f_deriv, T.horner_f_yO, zero_mul, add_zero]
  -- valuations in `𝓞 K`
  have hy0 : T.yO ≠ 0 := by
    intro h
    have := T.horner_f_yO
    rw [h] at this
    simp [fL] at this
  have hZP : horner ZL T.yO ∉ P := by
    intro h
    rw [ZL_eq, horner_cons] at h
    have hZ0 : ((Z₀ : ℤ) : 𝓞 K) ∈ P := by
      have := P.sub_mem h (P.mul_mem_right (horner Z₁L T.yO) hyP)
      simpa using this
    obtain ⟨k, hk⟩ := Z₀_odd
    apply hP.ne_top
    rw [Ideal.eq_top_iff_one]
    have : ((2 * k + 1 : ℤ) : 𝓞 K) ∈ P := hk ▸ hZ0
    push_cast at this
    have := P.sub_mem this (P.mul_mem_right (k : 𝓞 K) h2P)
    simpa using this
  have hZ0' : horner ZL T.yO ≠ 0 := fun h => hZP (h ▸ P.zero_mem)
  have hvy : vP P T.yO ≤ 1 := by
    have hsplit := f_split T.yO
    rw [T.horner_f_yO] at hsplit
    have hKpP : (1 + T.yO * horner Kp₁L T.yO) ∉ P := by
      intro h
      apply hP.ne_top
      rw [Ideal.eq_top_iff_one]
      have := P.sub_mem h (P.mul_mem_right (horner Kp₁L T.yO) hyP)
      simpa using this
    have hK0 : (1 + T.yO * horner Kp₁L T.yO) ≠ 0 := fun h => hKpP (h ▸ P.zero_mem)
    have hG0 : horner GhiL T.yO ≠ 0 := by
      intro h
      rw [h, mul_zero, zero_add] at hsplit
      exact hK0 ((mul_eq_zero.mp hsplit.symm).resolve_left two_ne_zero)
    have heq : T.yO ^ 8 * horner GhiL T.yO = (-1) * (2 * (1 + T.yO * horner Kp₁L T.yO)) := by
      linear_combination (-1 : 𝓞 K) * hsplit
    have hv := congrArg (vP P) heq
    rw [vP_mul P hPprime (pow_ne_zero _ hy0) hG0, vP_pow P hPprime hy0,
      vP_mul P hPprime (by norm_num) (mul_ne_zero two_ne_zero hK0),
      vP_mul P hPprime two_ne_zero hK0, vP_eq_zero P hKpP,
      vP_eq_zero P (fun h => hP.ne_top (Ideal.eq_top_of_isUnit_mem _ h isUnit_neg_one)),
      ← ramificationIdx_eq_vP_two P h2P] at hv
    omega
  have hvx : vP P x ≤ 18 := by
    rw [hxval, vP_mul P hPprime (pow_ne_zero _ hy0) hZ0', vP_pow P hPprime hy0,
      vP_eq_zero P hZP]
    omega
  -- the tower formula
  intro hdiv
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 T.F) (𝓞 K)] at hdiv
  have h1 := hPprime.pow_dvd_of_dvd_mul_left 19 hndvd hdiv
  have h2 : (differentIdeal ℤ (𝓞 T.F)).map (algebraMap (𝓞 T.F) (𝓞 K)) ∣ Ideal.span {x} := by
    rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
    exact hxmem
  have hx0 : x ≠ 0 := by
    rw [hxval]
    exact mul_ne_zero (pow_ne_zero _ hy0) hZ0'
  have := (pow_dvd_span_iff P hPprime hx0 19).mp (h1.trans h2)
  omega

/-- The conjugate realization has `π₂(-r) = -π₂'(r)`. -/
theorem conj_piO (g' s' : K) (hg' : g' * g' = (6101 + 393 * T.r) / 2)
    (hs' : s' * s' = (-25 - 2 * T.r) + (-139 + 9 * T.r) * g') :
    (T.conj g' s' hg' hs').piO = -T.piO' := by
  apply FaithfulSMul.algebraMap_injective (𝓞 K) K
  rw [map_neg]
  exact T.conj_pi2 g' s' hg' hs'

/-- **Every dyadic prime.** With the conjugate realization, `P¹⁹ ∤ 𝔇(K/ℚ)` for every prime
`P ∋ 2` of ramification index at most `8`. -/
theorem not_pow_nineteen_dvd_differentIdeal_of_two_mem (g' s' : K)
    (hg' : g' * g' = (6101 + 393 * T.r) / 2)
    (hs' : s' * s' = (-25 - 2 * T.r) + (-139 + 9 * T.r) * g')
    (P : Ideal (𝓞 K)) [hP : P.IsPrime] (h2 : (2 : 𝓞 K) ∈ P)
    (he : P.ramificationIdx ℤ ≤ 8) :
    ¬ P ^ 19 ∣ differentIdeal ℤ (𝓞 K) := by
  rw [← T.piO_mul_piO'] at h2
  rcases hP.mem_or_mem h2 with h | h
  · exact T.not_pow_nineteen_dvd_differentIdeal P h he
  · apply (T.conj g' s' hg' hs').not_pow_nineteen_dvd_differentIdeal P _ he
    rw [T.conj_piO g' s' hg' hs']
    exact P.neg_mem h

/-- **The dyadic discriminant exponent.** If every prime of `𝓞 K` above `2` has
ramification index `8`, then `8 · v₂ |disc K| ≤ 18 · [K : ℚ]`, i.e. the `2`-part of the
root discriminant is at most `2^{9/4}`. -/
theorem eight_mul_factorization_two_le (g' s' : K)
    (hg' : g' * g' = (6101 + 393 * T.r) / 2)
    (hs' : s' * s' = (-25 - 2 * T.r) + (-139 + 9 * T.r) * g')
    (he : ∀ Q : Ideal (𝓞 K), Q.IsPrime → ((2 : ℕ) : 𝓞 K) ∈ Q → Q.ramificationIdx ℤ = 8) :
    8 * (discr K).natAbs.factorization 2 ≤ 18 * Module.finrank ℚ K := by
  rw [← absNorm_differentIdeal K (𝓞 K)]
  apply mul_factorization_absNorm_le Nat.prime_two _ differentIdeal_ne_bot 8 18 he
  intro Q hQ h2Q
  have h2Q' : (2 : 𝓞 K) ∈ Q := by exact_mod_cast h2Q
  exact T.not_pow_nineteen_dvd_differentIdeal_of_two_mem g' s' hg' hs' Q h2Q'
    (le_of_eq (he Q hQ h2Q))

section Galois

variable [IsGalois ℚ K]

/-- In a Galois field, some automorphism sends `r = √241` to `-r`. -/
theorem exists_aut_neg_r : ∃ σ : K ≃ₐ[ℚ] K, σ T.r = -T.r := by
  have hsq : T.r ^ 2 = ((241 : ℤ) : K) := by rw [sq, T.hr]; push_cast; ring
  have hns : ¬ IsSquare ((241 : ℤ) : ℚ) := by push_cast; decide +kernel
  have hmin := minpoly_sqrt 241 T.r hsq hns
  have halg : IsAlgebraic ℚ T.r := (isIntegral_sqrt 241 T.r hsq).isAlgebraic
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' halg (x := -T.r) (by
    rw [hmin]
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, neg_sq, hsq]
    rw [show ((241 : ℤ) : ℚ) = (241 : ℚ) by norm_num, map_ofNat]
    push_cast
    ring)
  exact ⟨σ, hσ⟩

include T in
/-- **Every dyadic prime, Galois form.** For `K` Galois over `ℚ`, no conjugate data are
needed: an automorphism with `r ↦ -r` transports the realization. -/
theorem not_pow_nineteen_dvd_differentIdeal_of_two_mem_of_isGalois
    (P : Ideal (𝓞 K)) [hP : P.IsPrime] (h2 : (2 : 𝓞 K) ∈ P)
    (he : P.ramificationIdx ℤ ≤ 8) :
    ¬ P ^ 19 ∣ differentIdeal ℤ (𝓞 K) := by
  obtain ⟨σ, hσ⟩ := T.exists_aut_neg_r
  rw [← T.piO_mul_piO'] at h2
  rcases hP.mem_or_mem h2 with h | h
  · exact T.not_pow_nineteen_dvd_differentIdeal P h he
  · apply (T.map (σ : K →+* K)).not_pow_nineteen_dvd_differentIdeal P _ he
    have hpi : (T.map (σ : K →+* K)).piO = -T.piO' := by
      apply FaithfulSMul.algebraMap_injective (𝓞 K) K
      rw [map_neg]
      change (T.map (σ : K →+* K)).pi2 = -((6101 - 393 * T.r) / 2)
      rw [map_pi2, pi2]
      change σ ((-6101 - 393 * T.r) / 2) = _
      rw [map_div₀, map_sub, map_mul, map_neg, map_ofNat, map_ofNat, map_ofNat, hσ]
      ring
    rw [hpi]
    exact P.neg_mem h

include T in
/-- **The dyadic discriminant exponent, Galois form** (only `√β₁` needed). -/
theorem eight_mul_factorization_two_le_of_isGalois
    (he : ∀ Q : Ideal (𝓞 K), Q.IsPrime → ((2 : ℕ) : 𝓞 K) ∈ Q → Q.ramificationIdx ℤ = 8) :
    8 * (discr K).natAbs.factorization 2 ≤ 18 * Module.finrank ℚ K := by
  rw [← absNorm_differentIdeal K (𝓞 K)]
  apply mul_factorization_absNorm_le Nat.prime_two _ differentIdeal_ne_bot 8 18 he
  intro Q hQ h2Q
  have h2Q' : (2 : 𝓞 K) ∈ Q := by exact_mod_cast h2Q
  exact T.not_pow_nineteen_dvd_differentIdeal_of_two_mem_of_isGalois Q h2Q'
    (le_of_eq (he Q hQ h2Q))

end Galois

end Realization

end UnitDistance.Sqrt241.Discriminant.Dyadic
