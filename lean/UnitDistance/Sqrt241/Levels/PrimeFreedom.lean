module

public import UnitDistance.Sqrt241.Levels.Unramified
public import UnitDistance.GeneratedQuadraticSigns
public import UnitDistance.Sqrt241.Local.Complex
public import UnitDistance.Sqrt241.Base.Local
public import UnitDistance.Sqrt241.Geometry.WitnessPrimePairs

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Prime freedom: complex conjugation moves every prime above `2, 3, 5, 29, 7`

The `√d` argument: for each witness prime `p` there is `d < 0`, a square
in `ℚ_p`, with `√d ∈ E ⊆ M`:

| `p` | 2 | 3 | 5 | 29 | 7 |
|---|---|---|---|---|---|
| `d` | `−15` | `−2` | `−1` | `−1` | `−3` |
| `√d` | `√−1√α₄√α₅√α₆√α₇` | `√−1√α₂√α₃` | `√−1` | `√−1` | `√α₄√α₅` |

Every element of the chosen absolute decomposition group at `p` fixes `√d`
(`decomposition_fixes_sqrt`: `√d` is a local square), while complex conjugation
negates it (`d < 0`). With the sign character of `√d` on `Gal(K/ℚ)`
(`Multiquadratic.rootSignHom`, commutative target) the ℚ package's
`PrimeCompletion.prime_moved_of_absolute_genus_exclusion` gives: for every finite Galois
`K ≤ Ω` containing `E` (e.g. admissible `K`), the restriction of `c₁` moves every prime of
`K` of norm `p^{f}`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Retained

open Tower Presentation Cut GroupData ProCGroups UnitDistance.PrimeCompletion
open _root_.UnitDistance.Sqrt241.Local NumberFieldAnalysis CanonicalGenus NumberField

attribute [local instance] PrimeCompletion.primeFact PrimeCompletion.baseRationalAlgebra

/-! ### Decomposition groups fix square roots of local squares -/

/-- **`PrimeCompletion.decomposition_fixes_sqrt`**: if `d` is a square in `ℚ_p`, every
element of the chosen absolute decomposition group at `p` fixes every square root of `d`. -/
theorem decomposition_fixes_sqrt (p : Nat.Primes) (d : ℚ) (hd : IsSquare ((d : ℚ_[p.val])))
    (x : Closure) (hx : x ^ 2 = (d : Closure)) (σ : AbsoluteDecomposition p) :
    σ.val x = x := by
  obtain ⟨s, hs⟩ := hd
  set t : SeparableClosure (Base p) := algebraMap (Base p) _ ((equiv p).symm s) with htdef
  have ht : t ^ 2 = absoluteEmbedding p (d : Closure) := by
    rw [map_ratCast, htdef, ← map_pow, sq, ← map_mul, ← hs, map_ratCast, map_ratCast]
  have hy : (absoluteEmbedding p x) ^ 2 = t ^ 2 := by rw [← map_pow, hx, ht]
  have hfix : decompositionEquiv p σ t = t := (decompositionEquiv p σ).commutes _
  have hfy : decompositionEquiv p σ (absoluteEmbedding p x) = absoluteEmbedding p x := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy with h | h
    · rw [h, hfix]
    · rw [h, map_neg, hfix]
  have hc := decomposition_commutes p σ x
  exact (absoluteEmbedding p).injective (hc.symm.trans hfy)

/-! ### The local squares -/

/-- The negative integers `d` at `2, 3, 5, 29, 7`. -/
def dInt : Fin 5 → ℤ := ![-15, -2, -1, -1, -3]

theorem isSquare_padic_of_int {p : ℕ} [Fact p.Prime] {d : ℤ} {z : ℤ_[p]}
    (h : (d : ℤ_[p]) = (1 : ℤ) * z ^ 2) : IsSquare ((d : ℚ) : ℚ_[p]) := by
  refine ⟨(z : ℚ_[p]), ?_⟩
  have h' := congrArg (fun y : ℤ_[p] => (y : ℚ_[p])) h
  simp only [Int.cast_one, one_mul, PadicInt.coe_pow, PadicInt.coe_intCast] at h'
  rw [Rat.cast_intCast, h', sq]

theorem isSquare_odd {p : ℕ} [Fact p.Prime] (d : ℤ) (t : ZMod p) (ht : (2 * t : ZMod p) ≠ 0)
    (hd : ((d : ZMod p)) = t ^ 2) : IsSquare ((d : ℚ) : ℚ_[p]) := by
  obtain ⟨z, -, hz⟩ := Base.padicInt_eq_mul_sq_of_toZMod (u := (d : ℤ_[p])) (c := 1)
    ⟨t, by simpa using ht, by rw [map_intCast, hd]; simp⟩
  exact isSquare_padic_of_int hz

theorem isSquare_dInt (a : Fin 5) :
    IsSquare (((dInt a : ℤ) : ℚ) : ℚ_[(selectedPrime a).val]) := by
  fin_cases a
  · -- `-15` in `ℚ₂`
    change IsSquare ((((-15 : ℤ)) : ℚ) : ℚ_[2])
    obtain ⟨z, -, hz⟩ := Base.padicInt_eq_mul_sq_of_residue8 (u := ((-15 : ℤ) : ℤ_[2])) (c := 1)
      (by decide) (by rw [map_intCast]; decide)
    exact isSquare_padic_of_int hz
  · change IsSquare ((((-2 : ℤ)) : ℚ) : ℚ_[3])
    exact isSquare_odd (p := 3) (-2) 1 (by decide) (by decide)
  · change IsSquare ((((-1 : ℤ)) : ℚ) : ℚ_[5])
    exact isSquare_odd (p := 5) (-1) 2 (by decide) (by decide)
  · change IsSquare ((((-1 : ℤ)) : ℚ) : ℚ_[29])
    exact isSquare_odd (p := 29) (-1) 12 (by decide) (by decide)
  · change IsSquare ((((-3 : ℤ)) : ℚ) : ℚ_[7])
    exact isSquare_odd (p := 7) (-3) 2 (by decide) (by decide)

/-! ### The square roots in `E` -/

open Genus in
/-- `√d ∈ E`. -/
def rootD : Fin 5 → CanonicalGenus.Carrier :=
  ![gE 0 * gE 4 * gE 5 * gE 6 * gE 7, gE 0 * gE 2 * gE 3, gE 0, gE 0, gE 4 * gE 5]

theorem radQ_products :
    Genus.radQ 0 * Genus.radQ 4 * Genus.radQ 5 * Genus.radQ 6 * Genus.radQ 7 = -15 ∧
    Genus.radQ 0 * Genus.radQ 2 * Genus.radQ 3 = -2 ∧
    Genus.radQ 0 = -1 ∧ Genus.radQ 4 * Genus.radQ 5 = -3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

open Genus in
theorem rootD_sq (a : Fin 5) : rootD a ^ 2 = ((dInt a : ℤ) : CanonicalGenus.Carrier) := by
  obtain ⟨h1, h2, h3, h4⟩ := radQ_products
  fin_cases a
  · change (gE 0 * gE 4 * gE 5 * gE 6 * gE 7) ^ 2 = ((-15 : ℤ) : Carrier)
    rw [mul_pow, mul_pow, mul_pow, mul_pow, sq_gE, sq_gE, sq_gE, sq_gE, sq_gE, ← map_mul,
      ← map_mul, ← map_mul, ← map_mul, h1, map_neg, map_ofNat]
    norm_num
  · change (gE 0 * gE 2 * gE 3) ^ 2 = ((-2 : ℤ) : Carrier)
    rw [sq_gE_mul3, h2, map_neg, map_ofNat]
    norm_num
  · change (gE 0) ^ 2 = ((-1 : ℤ) : Carrier)
    rw [sq_gE, h3]
    simp
  · change (gE 0) ^ 2 = ((-1 : ℤ) : Carrier)
    rw [sq_gE, h3]
    simp
  · change (gE 4 * gE 5) ^ 2 = ((-3 : ℤ) : Carrier)
    rw [sq_gE_mul, h4, map_neg, map_ofNat]
    norm_num

theorem dInt_neg (a : Fin 5) : dInt a < 0 := by fin_cases a <;> decide

/-! ### The sign character of `√d` on a subfield of `Ω` containing `E` -/

section Sign

variable {K : IntermediateField ℚ Omega} [FiniteDimensional ℚ K] [IsGalois ℚ K]
  (hE : EOmega ≤ K)

/-- `√d` in `K`. -/
def rootK (a : Fin 5) : K :=
  ⟨⟨((rootD a : CanonicalGenus.Carrier) : Closure),
    canonicalGenus_le_Omega (rootD a).2⟩, hE (Input.mem_EOmega_of_mem_field (rootD a).2)⟩

omit [FiniteDimensional ℚ K] [IsGalois ℚ K] in
theorem coe_rootK (a : Fin 5) :
    (((rootK hE a : K) : Omega) : Closure) = ((rootD a : CanonicalGenus.Carrier) : Closure) :=
  rfl

theorem rootD_sq_closure (a : Fin 5) :
    ((rootD a : CanonicalGenus.Carrier) : Closure) ^ 2 = (((dInt a : ℤ) : ℚ) : Closure) := by
  have h := congrArg (fun y : CanonicalGenus.Carrier => (y : Closure)) (rootD_sq a)
  simpa using h

omit [FiniteDimensional ℚ K] [IsGalois ℚ K] in
theorem rootK_sq (a : Fin 5) :
    rootK hE a ^ 2 = algebraMap ℚ K ((dInt a : ℤ) : ℚ) := by
  apply Subtype.ext
  apply Subtype.ext
  change ((rootD a : CanonicalGenus.Carrier) : Closure) ^ 2 = _
  rw [rootD_sq_closure]
  simp

theorem rootK_ne_zero (a : Fin 5) : rootK hE a ≠ 0 := by
  intro h
  have h2 := rootK_sq hE a
  rw [h, zero_pow two_ne_zero] at h2
  have h3 : ((dInt a : ℤ) : ℚ) = 0 := (algebraMap ℚ K).injective (by rw [← h2, map_zero])
  have h4 := dInt_neg a
  have : (dInt a : ℚ) < 0 := by exact_mod_cast h4
  linarith

/-- The sign character of `√d`. -/
def signChar (a : Fin 5) : Gal(K/ℚ) →* Multiplicative (Unit → ZMod 2) :=
  Multiquadratic.rootSignHom (fun _ : Unit => ((dInt a : ℤ) : ℚ)) (fun _ => rootK hE a)
    (fun _ => rootK_sq hE a) (fun _ => rootK_ne_zero hE a)

theorem res_apply_rootK (g : Ghat) (a : Fin 5) :
    (((Input.res K g (rootK hE a) : K) : Omega) : Closure) =
      ((g ⟨((rootD a : CanonicalGenus.Carrier) : Closure),
        canonicalGenus_le_Omega (rootD a).2⟩ : Omega) : Closure) := by
  have h := GaloisEmbedding.restriction_commutes K.val g (rootK hE a)
  exact congrArg (fun y : Omega => (y : Closure)) h

theorem signChar_eq_zero_of_fix (a : Fin 5) (g : Ghat)
    (hg : ((g ⟨((rootD a : CanonicalGenus.Carrier) : Closure),
        canonicalGenus_le_Omega (rootD a).2⟩ : Omega) : Closure) =
      ((rootD a : CanonicalGenus.Carrier) : Closure)) :
    signChar hE a (Input.res K g) = 1 := by
  apply Multiplicative.toAdd.injective
  funext u
  change Multiquadratic.rootCharacter (fun _ => rootK hE a) (Input.res K g) u = 0
  have hfix : Input.res K g (rootK hE a) = rootK hE a := by
    apply Subtype.ext
    apply Subtype.ext
    rw [res_apply_rootK, hg]
    rfl
  simp [Multiquadratic.rootCharacter, hfix]

theorem signChar_ne_zero_of_neg (a : Fin 5) (g : Ghat)
    (hg : ((g ⟨((rootD a : CanonicalGenus.Carrier) : Closure),
        canonicalGenus_le_Omega (rootD a).2⟩ : Omega) : Closure) =
      -((rootD a : CanonicalGenus.Carrier) : Closure)) :
    signChar hE a (Input.res K g) ≠ 1 := by
  intro h
  have h0 := congrFun (congrArg Multiplicative.toAdd h) ()
  change Multiquadratic.rootCharacter (fun _ => rootK hE a) (Input.res K g) () = 0 at h0
  have hmove : Input.res K g (rootK hE a) = -rootK hE a := by
    apply Subtype.ext
    apply Subtype.ext
    rw [res_apply_rootK, hg]
    rfl
  have hne : -rootK hE a ≠ rootK hE a := by
    intro he
    have h2 : (2 : K) * rootK hE a = 0 := by linear_combination -he
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact two_ne_zero h3
    · exact rootK_ne_zero hE a h3
  simp [Multiquadratic.rootCharacter, hmove, hne] at h0

end Sign

/-! ### Complex conjugation negates `√d` -/

theorem conj_moves_rootD (I : Input) (a : Fin 5) :
    ((((I.E.conj 0 : GB) : Ghat) ⟨((rootD a : CanonicalGenus.Carrier) : Closure),
        canonicalGenus_le_Omega (rootD a).2⟩ : Omega) : Closure) =
      -((rootD a : CanonicalGenus.Carrier) : Closure) := by
  set y : Omega := ⟨((rootD a : CanonicalGenus.Carrier) : Closure),
    canonicalGenus_le_Omega (rootD a).2⟩
  have hsq : I.phi y ^ 2 = (((dInt a : ℤ) : ℝ) : ℂ) := by
    have h : y ^ 2 = (((dInt a : ℤ) : ℚ) : Omega) := by
      apply Subtype.ext
      simpa using rootD_sq_closure a
    rw [← map_pow, h, map_ratCast]
    push_cast
    rfl
  have hneg : ((dInt a : ℤ) : ℝ) < 0 := by exact_mod_cast dInt_neg a
  have hc := conj_eq_neg_of_sq_neg hsq hneg
  have hconj : I.phi (((I.E.conj 0 : GB) : Ghat) y) = star (I.phi y) := I.conj_isConj.eq y
  rw [show star (I.phi y) = starRingEnd ℂ (I.phi y) from rfl, hc] at hconj
  have hinj : ((I.E.conj 0 : GB) : Ghat) y = -y := by
    apply I.phi.injective
    rw [map_neg, hconj]
  exact congrArg (fun z : Omega => (z : Closure)) hinj

/-! ### Prime freedom -/

/-- **Prime freedom** in every finite Galois `K ≤ Ω` containing `E`: the restriction of
`c₁` moves every prime of `K` of norm `p^{f_a}` above the witness prime `p`. -/
theorem prime_moved (I : Input) {K : IntermediateField ℚ Omega} [FiniteDimensional ℚ K]
    [IsGalois ℚ K] (hE : EOmega ≤ K) (a : Fin 5)
    (P : PrimeNormFiber K (Witness.primeNorm a)) :
    Ideal.map (RingOfIntegers.mapRingHom (Input.res K ((I.E.conj 0 : GB) : Ghat)).toRingHom)
      P.1.asIdeal ≠ P.1.asIdeal := by
  have hnorm : Witness.primeNorm a = (selectedPrime a).val ^ Witness.residueDegree a := by
    rw [selectedPrime_val]
    rfl
  let P' : PrimeNormFiber K ((selectedPrime a).val ^ Witness.residueDegree a) :=
    ⟨P.1, P.2.trans hnorm⟩
  have hpos : 0 < Witness.residueDegree a := by fin_cases a <;> decide
  apply prime_moved_of_absolute_genus_exclusion (M := K) (p := selectedPrime a) (j := jK K)
    (signChar hE a) (Input.res K ((I.E.conj 0 : GB) : Ghat)) ?_ (Witness.residueDegree a) hpos P'
  intro σ
  rw [decompositionRestriction_eq, signChar_eq_zero_of_fix hE a]
  · exact (signChar_ne_zero_of_neg hE a _ (conj_moves_rootD I a)).symm
  · rw [decompositionMap_apply, toGhat_apply]
    exact decomposition_fixes_sqrt (selectedPrime a) _ (isSquare_dInt a) _
      (rootD_sq_closure a) σ

end UnitDistance.Sqrt241.Retained
