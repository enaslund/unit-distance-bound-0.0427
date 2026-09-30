module

public import UnitDistance.Sqrt241.Local.Place
public import UnitDistance.PadicTwoRootSigns
public import UnitDistance.PadicTwoGlobalMap
public import UnitDistance.PadicTwoSquareclassIndependence
public import UnitDistance.GroupAugmentationRetainedQuadratic

@[expose] public section
set_option backward.privateInPublic true

/-!
# Dyadic signs of the genus roots at the chosen place above 2

The chosen place of the closure above `2` restricts on `B` to `iota2` (first
dyadic prime `𝔭₁`, `dyadicPlace = 0`) or to `iota2'` (`𝔭₂`, `dyadicPlace = 1`);
which one is not known. For either one, the Base square-class tables
(`7, 3, 6, 3, 1, 5, 3, 1` resp. `7, 5, 5, 10, 5, 1, 1, 3`) express every radicand
as `c · z²`, and `c · (-1)^{e₀} 2^{e₁} 5^{e₂}` is a `2`-adic square for the
exponent vector `dyadicExp P k`. Hence an element `σ` of the absolute Galois
group of `ℚ₂` acts on the image of the genus root `√α_k` by the sign
`∑ᵢ e_i v_i`, where `v = absoluteSigns σ` records its action on `√-1, √2, √5`
(`decomposition_genusRoot`). The three local generators `(a, b, c)` of
`PadicTwoQuadraticRelation` (signs `e₀, e₁, e₂`) have the genus masks
`(79, 4, 110)` at `𝔭₁` and `(129, 8, 158)` at `𝔭₂`
(`dyadicSignVector_genusBasis`); for `(x, y, z) = (b, a, a c)` these are the
vectors `00100000, 11110010, 10000100` resp. `00010000, 10000001, 11111000` of
construction.md §3.4 (bit `k` ↔ `α_k`).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Local

open NumberField CanonicalGenus Base UnitDistance.PrimeCompletion Multiquadratic

attribute [local instance] PrimeCompletion.primeFact PrimeCompletion.baseRationalAlgebra

/-! ## Square classes and exponent vectors -/

/-- Square-class representatives of the eight radicands at `𝔭₁` (`P = 0`) and `𝔭₂` (`P = 1`). -/
def dyadicClass : Fin 2 → Fin 8 → ℤ := ![squareclass2, squareclass2']

/-- Exponents of `-1, 2, 5` making `dyadicClass P k` a square. -/
def dyadicExp : Fin 2 → Fin 8 → Fin 3 → ZMod 2 :=
  ![![![1, 0, 0], ![1, 0, 1], ![1, 1, 1], ![1, 0, 1], ![0, 0, 0], ![0, 0, 1], ![1, 0, 1],
      ![0, 0, 0]],
    ![![1, 0, 0], ![0, 0, 1], ![0, 0, 1], ![0, 1, 1], ![0, 0, 1], ![0, 0, 0], ![0, 0, 0],
      ![1, 0, 1]]]

/-- The power of `4` in `dyadicClass P k · ∏ (-1, 2, 5)^e`. -/
def dyadicFour : Fin 2 → Fin 8 → ℕ := ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0]]

/-- The odd part of `dyadicClass P k · ∏ (-1, 2, 5)^e`, always `≡ 1 (mod 8)`. -/
def dyadicOdd : Fin 2 → Fin 8 → ℤ :=
  ![![-7, -15, -15, -15, 1, 25, -15, 1], ![-7, 25, 25, 25, 25, 1, 1, -15]]

theorem dyadic_product_eq : ∀ P : Fin 2, ∀ k : Fin 8,
    dyadicClass P k * ∏ i, PadicTwo.independentRadicand i ^ (dyadicExp P k i).val =
      4 ^ dyadicFour P k * dyadicOdd P k := by decide +kernel

theorem dyadicOdd_mod_eight : ∀ P : Fin 2, ∀ k : Fin 8, (dyadicOdd P k : ZMod 8) = 1 := by
  decide +kernel

theorem dyadic_product_isSquare (P : Fin 2) (k : Fin 8) :
    IsSquare ((dyadicClass P k : ℚ_[2]) *
      ∏ i, (PadicTwo.independentRadicand i : ℚ_[2]) ^ (dyadicExp P k i).val) := by
  have h := congrArg (fun n : ℤ => (n : ℚ_[2])) (dyadic_product_eq P k)
  push_cast at h
  rw [h]
  obtain ⟨w, hw⟩ := PadicTwo.int_isSquare_of_residue_one (dyadicOdd P k) (dyadicOdd_mod_eight P k)
  refine ⟨2 ^ dyadicFour P k * w, ?_⟩
  rw [hw, show (4 : ℚ_[2]) = 2 * 2 by norm_num, mul_pow]
  ring

/-- The genus sign vector of a local element with signs `v` on `√-1, √2, √5`. -/
def dyadicSignVector (P : Fin 2) (v : Fin 3 → ZMod 2) : Fin 8 → ZMod 2 :=
  fun k => ∑ i, dyadicExp P k i * v i

/-- The generator masks: `(a, b, c)` ↦ `(79, 4, 110)` at `𝔭₁`, `(129, 8, 158)` at `𝔭₂`. -/
def dyadicMasks : Fin 2 → Fin 3 → ℕ := ![![79, 4, 110], ![129, 8, 158]]

theorem dyadicSignVector_single : ∀ P : Fin 2, ∀ i : Fin 3,
    dyadicSignVector P (Pi.single i 1) = RetainedQuadratic.binaryVector 8 (dyadicMasks P i) := by
  decide +kernel

theorem dyadicSignVector_genusBasis (P : Fin 2) (i : Fin 3) :
    dyadicSignVector P (PadicTwoMaximalProTwo.genusBasis i).toAdd =
      RetainedQuadratic.binaryVector 8 (dyadicMasks P i) :=
  dyadicSignVector_single P i

theorem dyadicSignVector_add (P : Fin 2) (v w : Fin 3 → ZMod 2) :
    dyadicSignVector P (v + w) = dyadicSignVector P v + dyadicSignVector P w := by
  funext k
  simp only [dyadicSignVector, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-! ## The chosen place above 2 -/

/-- The prime `2`, as the ℚ package's dyadic prime. -/
abbrev prime2 : Nat.Primes := PadicTwoGlobalMap.prime

/-- The chosen place above `2`, restricted to `B`. -/
def dyadicEmb : B →ₐ[ℚ] ℚ_[2] := placeEmb prime2 isSquare_241_two

open Classical in
/-- `0` if the chosen place above `2` lies over `𝔭₁ = (π₂)`, `1` if over `𝔭₂ = (π₂')`. -/
def dyadicPlace : Fin 2 := if dyadicEmb = iota2 then 0 else 1

theorem dyadicEmb_eq_zero (h : dyadicPlace = 0) : dyadicEmb = iota2 := by
  by_contra hne
  simp [dyadicPlace, hne] at h

theorem dyadicEmb_eq_one (h : dyadicPlace = 1) : dyadicEmb = iota2' := by
  rcases algHom_eq_iota2_or dyadicEmb with he | he
  · simp [dyadicPlace, he] at h
  · exact he

theorem dyadicEmb_alpha (k : Fin 8) : ∃ z : ℚ_[2], z ≠ 0 ∧
    dyadicEmb (alphaB k) = (dyadicClass dyadicPlace k : ℚ_[2]) * z ^ 2 := by
  rw [alphaB_eq]
  rcases Fin.exists_fin_two.mp ⟨dyadicPlace, rfl⟩ with h | h
  · rw [dyadicEmb_eq_zero h, h]
    exact iota2_alpha k
  · rw [dyadicEmb_eq_one h, h]
    exact iota2'_alpha k

/-- On `B` the ℚ package's embedding into `AlgebraicClosure ℚ₂` is `dyadicEmb`. -/
theorem globalEmbedding_coe (x : B) :
    PadicTwoGlobalMap.globalEmbedding (x : Closure) =
      algebraMap ℚ_[2] PadicTwoMaximalProTwo.Closure (dyadicEmb x) := by
  change PadicTwoGlobalMap.closureEquiv.symm (absoluteEmbedding prime2 (x : Closure)) = _
  rw [absoluteEmbedding_coe prime2 isSquare_241_two x]
  apply PadicTwoGlobalMap.closureEquiv.injective
  rw [RingEquiv.apply_symm_apply, PadicTwoGlobalMap.closureEquiv_commutes]
  rfl

theorem globalEmbedding_genusRoot_sq (k : Fin 8) :
    (PadicTwoGlobalMap.globalEmbedding (genusRoot k)) ^ 2 =
      algebraMap ℚ_[2] PadicTwoMaximalProTwo.Closure (dyadicEmb (alphaB k)) := by
  rw [← map_pow, genusRoot_sq, ← coe_alphaB, globalEmbedding_coe]

/-! ## Signs -/

theorem binarySign_pow_val {E : Type*} [Field E] [CharZero E] (e v : ZMod 2) :
    (binarySign (E := E) v) ^ e.val = binarySign (e * v) := by
  have h : ∀ e v : ZMod 2, binarySignInteger v ^ e.val = binarySignInteger (e * v) := by
    decide +kernel
  unfold binarySign
  exact_mod_cast h e v

/-- The product of local roots selected by an exponent vector. -/
def localProd (e : Fin 3 → ZMod 2) : PadicTwoMaximalProTwo.Closure :=
  ∏ i, PadicTwoRootSigns.localRoot i ^ (e i).val

theorem localProd_ne_zero (e : Fin 3 → ZMod 2) : localProd e ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (PadicTwoRootSigns.localRoot_ne_zero i)

theorem localProd_sq (e : Fin 3 → ZMod 2) :
    (localProd e) ^ 2 = algebraMap ℚ_[2] PadicTwoMaximalProTwo.Closure
      (∏ i, (PadicTwo.independentRadicand i : ℚ_[2]) ^ (e i).val) := by
  rw [localProd, ← Finset.prod_pow, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← pow_mul, mul_comm, pow_mul, PadicTwoRootSigns.localRoot_sq, map_pow, map_intCast]

theorem localProd_action (σ : PadicTwoMaximalProTwo.AbsoluteGroup) (e : Fin 3 → ZMod 2) :
    σ (localProd e) =
      binarySign (∑ i, e i * (PadicTwoMaximalProTwo.absoluteSigns σ).toAdd i) * localProd e := by
  rw [localProd, map_prod]
  simp only [map_pow, PadicTwoRootSigns.localRoot_action, mul_pow, Finset.prod_mul_distrib,
    binarySign_pow_val]
  congr 1
  rw [Fin.prod_univ_three, Fin.sum_univ_three, binarySign_add, binarySign_add]

/-- Sign of `σ` on the image of a genus root, read from the square-class table. -/
theorem action_genusRoot (σ : PadicTwoMaximalProTwo.AbsoluteGroup) (k : Fin 8) :
    σ (PadicTwoGlobalMap.globalEmbedding (genusRoot k)) =
      binarySign (dyadicSignVector dyadicPlace (PadicTwoMaximalProTwo.absoluteSigns σ).toAdd k) *
        PadicTwoGlobalMap.globalEmbedding (genusRoot k) := by
  obtain ⟨z, hz, hzk⟩ := dyadicEmb_alpha k
  set e := dyadicExp dyadicPlace k
  apply PadicTwoRootSigns.transfer_sign σ _ (localProd e)
    (z ^ 2 * ((dyadicClass dyadicPlace k : ℚ_[2]) *
      ∏ i, (PadicTwo.independentRadicand i : ℚ_[2]) ^ (e i).val))
    (localProd_ne_zero e)
  · rw [mul_pow, globalEmbedding_genusRoot_sq, localProd_sq, hzk, ← map_mul]
    ring_nf
  · exact (IsSquare.sq z).mul (dyadic_product_isSquare dyadicPlace k)
  · rw [localProd_action]
    rfl

/-- **Dyadic genus signs.** The decomposition element attached to a local
automorphism `σ` of `ℚ̄₂` multiplies the genus root `√α_k` by the sign
`dyadicSignVector dyadicPlace (absoluteSigns σ) k`. -/
theorem decomposition_genusRoot (σ : PadicTwoMaximalProTwo.AbsoluteGroup) (k : Fin 8) :
    (PadicTwoGlobalMap.decomposition σ).val (genusRoot k) =
      binarySign (dyadicSignVector dyadicPlace (PadicTwoMaximalProTwo.absoluteSigns σ).toAdd k) *
        genusRoot k := by
  apply PadicTwoGlobalMap.globalEmbedding.injective
  change PadicTwoGlobalMap.globalEmbedding ((PadicTwoGlobalMap.decomposition σ).val (genusRoot k)) =
    PadicTwoGlobalMap.globalEmbedding (_ * genusRoot k)
  rw [← PadicTwoGlobalMap.decomposition_commutes, action_genusRoot, map_mul]
  congr 1
  simp only [binarySign, map_intCast]

theorem dyadicDecomposition_fixes_B (σ : PadicTwoMaximalProTwo.AbsoluteGroup) (x : B) :
    (PadicTwoGlobalMap.decomposition σ).val (x : Closure) = x :=
  Local.decomposition_fixes_B prime2 isSquare_241_two _ x

end UnitDistance.Sqrt241.Local
