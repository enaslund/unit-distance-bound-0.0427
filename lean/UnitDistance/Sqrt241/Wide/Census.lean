module

public import UnitDistance.Sqrt241.Wide.Count
public import UnitDistance.Sqrt241.Levels.LocalData
public import UnitDistance.AbsolutePrimeIndices
public import UnitDistance.Sqrt241.Local.Unramified
public import Mathlib.RingTheory.Frobenius

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Residue degree `≤ 2` of `E_W/B` at split census places

Let `p ∉ {2, 3, 5, 241}` be odd and split in `B`, and let `𝔮 = ker(𝓞 B → 𝔽_p, ω ↦ a)` for a root
`a` of `X² - X - 60` mod `p` (`censusPlace`). Let `v ∈ F₂⁸` be the vector of Legendre symbols of
the radicands `α_k` modulo `𝔮`, and assume `bil_i(φ₁ v, φ₁ v) = 0` for the four D4 forms (the
paper's `fW = 2`). Then every prime `P` of `E_W` above `𝔮` has `N P ≤ p²` and `e f ≤ 2`
(`census_fiber_bound`).

Proof. Take a prime `Q` of `M` above `P` and an arithmetic Frobenius `σ ∈ Gal(M/ℚ)` at `Q`
(`σ y ≡ y^p mod Q`, Mathlib `IsArithFrobAt.exists_of_isInvariant`), lifted to `τ ∈ Ĝ`. Euler's
criterion modulo `Q` shows `τ √241 = √241` and `τ √α_k = (-1)^{v_k} √α_k` (the alternative sign
would put `2 α_k` or `2·241` into `𝔮`). So `τ ∈ G_B` has label `v`, and `τ²` has trivial label
and trivial D4 signs, hence fixes `E_W`. For `x ∈ 𝓞 E_W`, `x = σ² x ≡ x^{p²} mod Q`, so the
residue field of `P` has at most `p²` elements. `M` is unramified at `p` (`Local.inertia_killed`),
hence so is `E_W`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Wide

open NumberField IsDedekindDomain UnitDistance.NumberFieldAnalysis UnitDistance.Sqrt241.Analytic
open CanonicalGenus CanonicalWide Base Tower Multiquadratic Retained ClassTwo
open UnitDistance.PrimeCompletion

local notation "EW" => CanonicalWide.Carrier

attribute [local instance] PrimeCompletion.primeFact PrimeCompletion.baseRationalAlgebra

/-! ### `M` and the maps of rings of integers -/

/-- `M` of the canonical input. -/
abbrev MW : IntermediateField ℚ Omega := input.M

instance algebraCarrierM : Algebra EW MW := (wideToM input).toRingHom.toAlgebra

instance : IsScalarTower ℚ EW MW := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

/-- `𝓞 M → Ω`. -/
def toOmega : 𝓞 MW →+* Omega := MW.val.toRingHom.comp (algebraMap (𝓞 MW) MW)

theorem toOmega_injective : Function.Injective toOmega := by
  intro x y h
  apply RingOfIntegers.ext
  exact MW.val.injective h

/-- `𝓞 B → 𝓞 M`. -/
def iotaB : 𝓞 B →+* 𝓞 MW :=
  (algebraMap (𝓞 EW) (𝓞 MW)).comp (algebraMap (𝓞 B) (𝓞 EW))

theorem toOmega_algebraMap (x : 𝓞 EW) :
    (toOmega (algebraMap (𝓞 EW) (𝓞 MW) x) : Closure) = ((x : EW) : Closure) := by
  change (((wideToM input (x : EW) : MW) : Omega) : Closure) = _
  rw [coe_wideToM]

theorem toOmega_iotaB (b : 𝓞 B) : (toOmega (iotaB b) : Closure) = ((b : B) : Closure) := by
  change (toOmega (algebraMap (𝓞 EW) (𝓞 MW) (algebraMap (𝓞 B) (𝓞 EW) b)) : Closure) = _
  rw [toOmega_algebraMap]
  change ((algebraMap B EW (b : B) : EW) : Closure) = _
  rw [coe_algebraMap_BCarrier]

theorem toOmega_coe (y : 𝓞 MW) : toOmega y = ((y : MW) : Omega) := rfl

theorem genusRootOmega_mem_M (k : Fin 8) : genusRootOmega k ∈ MW :=
  input.mem_M_of_mem_field (genusRoot_mem k)

/-- `√α_k ∈ 𝓞 M`. -/
def gM (k : Fin 8) : 𝓞 MW :=
  ⟨⟨genusRootOmega k, genusRootOmega_mem_M k⟩, by
    have h : (⟨genusRootOmega k, genusRootOmega_mem_M k⟩ : MW) ^ 2 =
        ((iotaB (alpha k) : 𝓞 MW) : MW) := by
      apply Subtype.ext
      rw [IntermediateField.coe_pow, ← toOmega_coe]
      change genusRootOmega k ^ 2 = _
      apply Subtype.ext
      rw [genusRootOmega_sq, toOmega_iotaB, coe_alpha]
      rfl
    have hi : IsIntegral ℤ (((iotaB (alpha k) : 𝓞 MW) : MW)) := RingOfIntegers.isIntegral_coe _
    rw [← h] at hi
    exact IsIntegral.of_pow two_pos hi⟩

theorem toOmega_gM (k : Fin 8) : toOmega (gM k) = genusRootOmega k := rfl

theorem gM_sq (k : Fin 8) : gM k ^ 2 = iotaB (alpha k) := by
  apply toOmega_injective
  apply Subtype.ext
  rw [map_pow, toOmega_gM, toOmega_iotaB, coe_alpha]
  exact genusRoot_sq k

/-- `√241 ∈ 𝓞 M`. -/
def sM : 𝓞 MW := iotaB sqrt241Int

theorem toOmega_sM : toOmega sM = rootOmega := by
  apply Subtype.ext
  rw [sM, toOmega_iotaB, coe_sqrt241Int, coe_sqrt241]
  rfl

theorem sM_sq : sM ^ 2 = 241 := by
  apply toOmega_injective
  apply Subtype.ext
  rw [map_pow, toOmega_sM, map_ofNat]
  exact baseRoot_sq

/-- The action of `Gal(M/ℚ)` on `𝓞 M` through a lift to `Ĝ`. -/
theorem toOmega_smul (τ : Ghat) (y : 𝓞 MW) :
    toOmega (Input.res MW τ • y) = τ (toOmega y) :=
  GaloisEmbedding.restriction_commutes MW.val τ (y : MW)

/-- Elements of `𝓞 E_W` land in `E_W ≤ Ω`. -/
theorem toOmega_algebraMap_mem (x : 𝓞 EW) :
    toOmega (algebraMap (𝓞 EW) (𝓞 MW) x) ∈ EWOmega := by
  have hx : ((x : EW) : Closure) ∈ IntermediateField.lift EWOmega := by
    rw [lift_EWOmega]
    exact (x : EW).2
  rw [← toOmega_algebraMap] at hx
  exact (IntermediateField.mem_lift _).mp hx

/-! ### Frobenius iterates -/

theorem frob_iterate {S : Type*} [CommRing S] (f : S →+* S) (Q : Ideal S) (q : ℕ) (hq : 0 < q)
    (h : ∀ y, f y - y ^ q ∈ Q) (y : S) : f (f y) - y ^ (q * q) ∈ Q := by
  have hQ : ∀ z ∈ Q, f z ∈ Q := fun z hz => by
    have := Q.add_mem (h z) (Q.pow_mem_of_mem hz q hq)
    simpa using this
  have h1 : f (f y - y ^ q) ∈ Q := hQ _ (h y)
  have h2 : (f y) ^ q - (y ^ q) ^ q ∈ Q := by
    obtain ⟨c, hc⟩ := sub_dvd_pow_sub_pow (f y) (y ^ q) q
    rw [hc]
    exact Q.mul_mem_right c (h y)
  have : f (f y) - y ^ (q * q) = f (f y - y ^ q) + ((f y) ^ q - (y ^ q) ^ q) := by
    rw [map_sub, map_pow, ← pow_mul]
    ring
  rw [this]
  exact Q.add_mem h1 h2

/-! ### The census place -/

section Place

variable (p : Nat.Primes) (a : ZMod p.val) (ha : a * a = a + 60)

/-- The prime `ker(𝓞 B → 𝔽_p, ω ↦ a)` of `B` above `p`. -/
def censusPlace : HeightOneSpectrum (𝓞 B) :=
  haveI : Fact p.val.Prime := ⟨p.prop⟩
  { asIdeal := RingHom.ker (evalHom a ha)
    isPrime := RingHom.ker_isPrime _
    ne_bot := by
      intro h
      have hp : ((p.val : ℕ) : 𝓞 B) ∈ RingHom.ker (evalHom a ha) := by
        rw [RingHom.mem_ker, map_natCast, ZMod.natCast_self]
      rw [h, Ideal.mem_bot] at hp
      exact p.prop.ne_zero (by exact_mod_cast hp) }

theorem mem_censusPlace (b : 𝓞 B) : b ∈ (censusPlace p a ha).asIdeal ↔ evalHom a ha b = 0 :=
  RingHom.mem_ker

theorem censusPlace_under :
    (censusPlace p a ha).under (𝓞 ℚ) = rationalPrimePlace p := by
  haveI : Fact p.val.Prime := ⟨p.prop⟩
  apply HeightOneSpectrum.ext
  symm
  apply Ideal.IsMaximal.eq_of_le ((rationalPrimePlace p).isPrime.isMaximal (rationalPrimePlace p).ne_bot)
    (Ideal.IsPrime.ne_top inferInstance)
  rw [rationalPrimePlace_asIdeal, Ideal.span_singleton_le_iff_mem]
  change algebraMap (𝓞 ℚ) (𝓞 B) (p.val : 𝓞 ℚ) ∈ (censusPlace p a ha).asIdeal
  rw [map_natCast, mem_censusPlace, map_natCast, ZMod.natCast_self]

/-- The census place as a prime of `B` above `p`. -/
def censusPlaceFiber : PrimeFiber ℚ B (rationalPrimePlace p) :=
  ⟨censusPlace p a ha, censusPlace_under p a ha⟩

theorem absNorm_censusPlace : Ideal.absNorm (censusPlace p a ha).asIdeal = p.val := by
  haveI : Fact p.val.Prime := ⟨p.prop⟩
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  change Nat.card (𝓞 B ⧸ RingHom.ker (evalHom a ha)) = _
  rw [Nat.card_congr (RingHom.quotientKerEquivOfSurjective (evalHom_surjective a ha)).toEquiv,
    Nat.card_zmod]

end Place

/-! ### The main lemma -/

/-- `x ∈ 𝓞 B` lies in `Q` (a prime of `M` above `𝔮`) iff it lies in `𝔮`. -/
theorem iotaB_mem_iff (𝔮 : HeightOneSpectrum (𝓞 B)) (P : PrimeFiber B EW 𝔮) (Q : Ideal (𝓞 MW))
    [Q.LiesOver P.1.asIdeal] (b : 𝓞 B) : iotaB b ∈ Q ↔ b ∈ 𝔮.asIdeal := by
  have h1 : P.1.asIdeal.LiesOver 𝔮.asIdeal := primeFiber_liesOver B EW 𝔮 P
  rw [Ideal.over_def P.1.asIdeal 𝔮.asIdeal, Ideal.over_def Q P.1.asIdeal]
  rfl

theorem sign_sub_cases (c d : ZMod 2) (h : c ≠ d) :
    binarySignInteger c - binarySignInteger d = 2 ∨ binarySignInteger c - binarySignInteger d = -2 := by
  revert c d
  decide

/-- **Census bound.** -/
theorem census_fiber_bound (p : Nat.Primes) (hpS : p.val ∉ ({2, 3, 5, 241} : Finset ℕ))
    (hodd : p.val % 2 = 1) (a : ZMod p.val) (ha : a * a = a + 60) (v : Fin 8 → ZMod 2)
    (hE : ∀ k, (((alphaCoords k).1 : ZMod p.val) + ((alphaCoords k).2 : ZMod p.val) * a) ^
        ((p.val - 1) / 2) = ((binarySignInteger (v k) : ℤ) : ZMod p.val))
    (hN : ∀ k, (2 : ZMod p.val) *
        (((alphaCoords k).1 : ZMod p.val) + ((alphaCoords k).2 : ZMod p.val) * a) ≠ 0)
    (hS : (241 : ZMod p.val) ^ ((p.val - 1) / 2) = 1) (h482 : (482 : ZMod p.val) ≠ 0)
    (hW : ∀ i : Fin 4, bilFormula i (phi1 i v) (phi1 i v) = 0)
    (P : PrimeFiber B EW (censusPlace p a ha)) :
    Ideal.absNorm P.1.asIdeal ≤ p.val ^ 2 ∧
      P.1.asIdeal.ramificationIdx (𝓞 B) * P.1.asIdeal.inertiaDeg (𝓞 B) ≤ 2 := by
  haveI : Fact p.val.Prime := ⟨p.prop⟩
  have hPprime := P.1.isPrime
  haveI : P.1.asIdeal.IsMaximal := P.1.isPrime.isMaximal P.1.ne_bot
  haveI hPover : P.1.asIdeal.LiesOver (censusPlace p a ha).asIdeal := primeFiber_liesOver B EW (censusPlace p a ha) P
  -- a prime of `M` above `P`
  obtain ⟨Q, hQprime, hQover⟩ : ∃ Q : Ideal (𝓞 MW), Q.IsPrime ∧ Q.LiesOver P.1.asIdeal := by
    obtain ⟨⟨Q, hQ1, hQ2⟩⟩ := (inferInstance : Nonempty (P.1.asIdeal.primesOver (𝓞 MW)))
    exact ⟨Q, hQ1, hQ2⟩
  have hmem : ∀ b : 𝓞 B, iotaB b ∈ Q ↔ evalHom a ha b = 0 := fun b =>
    (iotaB_mem_iff (censusPlace p a ha) P Q b).trans (mem_censusPlace p a ha b)
  have hpQ : ((p.val : ℕ) : 𝓞 MW) ∈ Q := by
    have := (hmem (p.val : 𝓞 B)).mpr (by rw [map_natCast, ZMod.natCast_self])
    simpa using this
  have hQne : Q ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hpQ
    exact p.prop.ne_zero (by exact_mod_cast hpQ)
  -- `Q` lies over `p`
  have hQunder : Q.under ℤ = Ideal.span {((p.val : ℕ) : ℤ)} := by
    symm
    apply Ideal.IsMaximal.eq_of_le (Int.ideal_span_isMaximal_of_prime p.val)
      (Ideal.IsPrime.ne_top inferInstance)
    rw [Ideal.span_singleton_le_iff_mem]
    change algebraMap ℤ (𝓞 MW) _ ∈ Q
    simpa using hpQ
  have hcard : Nat.card (ℤ ⧸ Q.under ℤ) = p.val := by
    rw [hQunder, Nat.card_congr (Int.quotientSpanNatEquivZMod p.val).toEquiv, Nat.card_zmod]
  -- the arithmetic Frobenius
  haveI : Finite (𝓞 MW ⧸ Q) := Ring.HasFiniteQuotients.finiteQuotient hQne
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant ℤ Gal(MW/ℚ) Q
  have hfrob : ∀ y : 𝓞 MW, σ • y - y ^ p.val ∈ Q := by
    intro y
    have := hσ y
    rwa [hcard] at this
  obtain ⟨τ, hτ⟩ := GaloisEmbedding.restriction_surjective MW.val σ
  have hact : ∀ y : 𝓞 MW, toOmega (σ • y) = τ (toOmega y) := by
    intro y
    rw [← hτ]
    exact toOmega_smul τ y
  have hpow : ∀ y : 𝓞 MW, y ^ p.val = y * (y ^ 2) ^ ((p.val - 1) / 2) := by
    intro y
    rw [← pow_mul, ← pow_succ']
    congr 1
    omega
  -- `√241` is fixed
  have hsfix : σ • sM = sM := by
    have h1 : σ • sM - sM ∈ Q := by
      have h2 : sM ^ p.val - sM ∈ Q := by
        rw [hpow, sM_sq]
        have h3 : (241 : 𝓞 MW) ^ ((p.val - 1) / 2) - 1 ∈ Q := by
          have := (hmem ((241 : 𝓞 B) ^ ((p.val - 1) / 2) - 1)).mpr (by
            rw [map_sub, map_pow, map_ofNat, map_one, hS, sub_self])
          rwa [map_sub, map_pow, map_ofNat, map_one] at this
        have e : sM * (241 : 𝓞 MW) ^ ((p.val - 1) / 2) - sM =
            sM * ((241 : 𝓞 MW) ^ ((p.val - 1) / 2) - 1) := by ring
        rw [e]
        exact Q.mul_mem_left _ h3
      have := Q.add_mem (hfrob sM) h2
      simpa using this
    have hsq : (σ • sM) ^ 2 = sM ^ 2 := by
      rw [← smul_pow', sM_sq]
      exact map_ofNat (MulSemiringAction.toRingHom Gal(MW/ℚ) (𝓞 MW) σ) 241
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact h
    · exfalso
      rw [h] at h1
      have h4 := Q.mul_mem_right sM h1
      have e : (-sM - sM) * sM = -iotaB (2 * 241) := by
        rw [map_mul, map_ofNat, map_ofNat, ← sM_sq]
        ring
      rw [e] at h4
      have h5 := (hmem (2 * 241)).mp (by simpa only [neg_neg] using Q.neg_mem h4)
      apply h482
      rw [map_mul, map_ofNat, map_ofNat] at h5
      norm_num at h5 ⊢
      exact h5
  have hτGB : τ ∈ GB := by
    rw [mem_GB_iff]
    have := hact sM
    rw [hsfix, toOmega_sM] at this
    exact this.symm
  set g : GB := ⟨τ, hτGB⟩ with hg
  have hgact : ∀ k, σ • gM k = ((binarySignInteger (genusChar g k) : ℤ) : 𝓞 MW) * gM k := by
    intro k
    apply toOmega_injective
    rw [hact, toOmega_gM, map_mul, map_intCast, toOmega_gM]
    exact genusChar_action g k
  have hlabel : ∀ k, genusChar g k = v k := by
    intro k
    by_contra hne
    have h1 : gM k ^ p.val - ((binarySignInteger (v k) : ℤ) : 𝓞 MW) * gM k ∈ Q := by
      rw [hpow, gM_sq]
      have h3 : iotaB (alpha k) ^ ((p.val - 1) / 2) - ((binarySignInteger (v k) : ℤ) : 𝓞 MW) ∈ Q := by
        have := (hmem (alpha k ^ ((p.val - 1) / 2) - ((binarySignInteger (v k) : ℤ) : 𝓞 B))).mpr (by
          rw [map_sub, map_pow, evalHom_alpha, map_intCast, hE k, sub_self])
        simpa using this
      have e : gM k * iotaB (alpha k) ^ ((p.val - 1) / 2) -
          ((binarySignInteger (v k) : ℤ) : 𝓞 MW) * gM k =
          gM k * (iotaB (alpha k) ^ ((p.val - 1) / 2) - ((binarySignInteger (v k) : ℤ) : 𝓞 MW)) := by
        ring
      rw [e]
      exact Q.mul_mem_left _ h3
    have h2 := Q.add_mem (hfrob (gM k)) h1
    rw [hgact] at h2
    have h4 : (((binarySignInteger (genusChar g k) - binarySignInteger (v k) : ℤ)) : 𝓞 MW) * gM k ∈ Q := by
      have e : ((binarySignInteger (genusChar g k) : ℤ) : 𝓞 MW) * gM k - gM k ^ p.val +
          (gM k ^ p.val - ((binarySignInteger (v k) : ℤ) : 𝓞 MW) * gM k) =
          (((binarySignInteger (genusChar g k) - binarySignInteger (v k) : ℤ)) : 𝓞 MW) * gM k := by
        push_cast
        ring
      rwa [e] at h2
    have h5 := Q.mul_mem_right (gM k) h4
    rw [mul_assoc, ← pow_two, gM_sq] at h5
    have h6 : iotaB (2 * alpha k) ∈ Q := by
      rw [map_mul, map_ofNat]
      rcases sign_sub_cases _ _ hne with hd | hd
      · rw [hd] at h5
        exact_mod_cast h5
      · rw [hd] at h5
        have := Q.neg_mem h5
        have e : -(((-2 : ℤ) : 𝓞 MW) * iotaB (alpha k)) = 2 * iotaB (alpha k) := by push_cast; ring
        rwa [e] at this
    have h7 := (hmem _).mp h6
    rw [map_mul, evalHom_alpha, map_ofNat] at h7
    exact hN k h7
  -- `τ²` fixes `E_W`
  have hlab : genusLabel g = Multiplicative.ofAdd v := by
    apply Multiplicative.toAdd.injective
    funext k
    rw [genusLabel_apply, hlabel]
    rfl
  have hsq_label : genusLabel (g ^ 2) = 1 := by
    rw [map_pow, hlab]
    apply Multiplicative.toAdd.injective
    funext k
    simp only [toAdd_pow, toAdd_ofAdd, toAdd_one, Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
    have : ∀ x : ZMod 2, (2 : ZMod 2) * x = 0 := by decide
    push_cast
    exact this _
  have hEfix : ((g ^ 2 : GB) : Ghat) ∈ Efix := (mem_ker_genusLabelHom_iff (g ^ 2)).mp hsq_label
  have hEW : ((g ^ 2 : GB) : Ghat) ∈ EWfix := by
    have hker : (⟨_, hEfix⟩ : Efix) ∈ psiHom.ker := by
      rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      funext i
      rw [psiHom_apply]
      change (chiHom i (g ^ 2)).central = 0
      rw [map_pow, GroupModel.square_coordinates, chiHom_apply, bilD4_apply]
      have hb : (![aBit i g, bBit i g] : Fin 2 → ZMod 2) = phi1 i v := by
        funext c
        fin_cases c
        · simp [aBit, phi1_apply_zero, hlab]
        · simp [bBit, phi1_apply_one, hlab]
      rw [hb]
      exact hW i
    rw [ker_psiHom] at hker
    exact hker
  have hσ2 : ∀ x : 𝓞 EW, σ • σ • algebraMap (𝓞 EW) (𝓞 MW) x = algebraMap (𝓞 EW) (𝓞 MW) x := by
    intro x
    apply toOmega_injective
    rw [hact, hact]
    have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hEW _ (toOmega_algebraMap_mem x)
    have hgg : ((g ^ 2 : GB) : Ghat) = τ * τ := by
      rw [pow_two]
      rfl
    rw [hgg, AlgEquiv.mul_apply] at hfix
    exact hfix
  have : Q.LiesOver P.1.asIdeal := hQover
  have hres : ∀ x : 𝓞 EW, x ^ (p.val * p.val) - x ∈ P.1.asIdeal := by
    intro x
    have h1 := frob_iterate (MulSemiringAction.toRingHom Gal(MW/ℚ) (𝓞 MW) σ) Q p.val p.prop.pos
      hfrob (algebraMap (𝓞 EW) (𝓞 MW) x)
    change σ • σ • _ - _ ∈ Q at h1
    rw [hσ2] at h1
    rw [Ideal.over_def Q P.1.asIdeal]
    change algebraMap (𝓞 EW) (𝓞 MW) (x ^ _ - x) ∈ Q
    rw [map_sub, map_pow]
    have := Q.neg_mem h1
    simpa using this
  have hnorm : Ideal.absNorm P.1.asIdeal ≤ p.val ^ 2 := by
    rw [pow_two]
    exact absNorm_le_of_pow_sub_mem EW P.1.asIdeal (p.val * p.val)
      (by nlinarith [p.prop.two_le]) hres
  -- ramification
  have : Q.LiesOver (rationalPrimeIdeal p.val) := ⟨hQunder.symm⟩
  have hram : (rationalPrimeIdeal p.val).ramificationIdxIn (𝓞 MW) = 1 := by
    rw [← PrimeCompletion.inertiaRestriction_card p MW (jK MW)]
    have hb : (inertiaRestriction p MW (jK MW)).range = ⊥ := by
      apply le_antisymm _ bot_le
      rintro _ ⟨σ', rfl⟩
      rw [Subgroup.mem_bot, inertiaRestriction_eq, Local.inertia_killed p hpS σ', map_one]
    rw [hb, Subgroup.card_bot]
  have hQram : Q.ramificationIdx ℤ = 1 := by
    rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (rationalPrimeIdeal p.val) Q Gal(MW/ℚ)]
    exact hram
  have hPram : P.1.asIdeal.ramificationIdx ℤ ≤ 1 :=
    hQram ▸ Ideal.ramificationIdx_below_le (R := ℤ) P.1.asIdeal Q
  have hPramB : P.1.asIdeal.ramificationIdx (𝓞 B) ≤ 1 :=
    (Ideal.ramificationIdx_above_le (R := ℤ) (censusPlace p a ha).asIdeal P.1.asIdeal).trans hPram
  have hf : P.1.asIdeal.inertiaDeg (𝓞 B) ≤ 2 := by
    have h := Ideal.absNorm_pow_inertiaDeg (censusPlace p a ha).asIdeal P.1.asIdeal
    rw [absNorm_censusPlace] at h
    have : p.val ^ P.1.asIdeal.inertiaDeg (𝓞 B) ≤ p.val ^ 2 := h ▸ hnorm
    exact (Nat.pow_le_pow_iff_right p.prop.one_lt).mp this
  exact ⟨hnorm, by simpa using Nat.mul_le_mul hPramB hf⟩

/-! ### Census classes -/

theorem card_censusFiber_ge (p : Nat.Primes) (hpS : p.val ∉ ({2, 3, 5, 241} : Finset ℕ))
    (hodd : p.val % 2 = 1) (a : ZMod p.val) (ha : a * a = a + 60) (v : Fin 8 → ZMod 2)
    (hE : ∀ k, (((alphaCoords k).1 : ZMod p.val) + ((alphaCoords k).2 : ZMod p.val) * a) ^
        ((p.val - 1) / 2) = ((binarySignInteger (v k) : ℤ) : ZMod p.val))
    (hN : ∀ k, (2 : ZMod p.val) *
        (((alphaCoords k).1 : ZMod p.val) + ((alphaCoords k).2 : ZMod p.val) * a) ≠ 0)
    (hS : (241 : ZMod p.val) ^ ((p.val - 1) / 2) = 1) (h482 : (482 : ZMod p.val) ≠ 0)
    (hW : ∀ i : Fin 4, bilFormula i (phi1 i v) (phi1 i v) = 0) :
    ((1 / 4 : ℚ) : ℝ) * (Module.finrank ℚ EW : ℝ) ≤ Fintype.card (PrimeFiber B EW (censusPlace p a ha)) := by
  have h := finrank_le_card_mul B EW (censusPlace p a ha) 2 fun P =>
    (census_fiber_bound p hpS hodd a ha v hE hN hS h482 hW P).2
  rw [finrank_B_Carrier] at h
  rw [finrank_field]
  have : (2048 : ℝ) ≤ Fintype.card (PrimeFiber B EW (censusPlace p a ha)) := by
    exact_mod_cast (by omega : 2048 ≤ Fintype.card (PrimeFiber B EW (censusPlace p a ha)))
  norm_num
  linarith

/-- One good census place: contribution at least `φ(p²)/4`. -/
theorem censusOne_of_place (p : Nat.Primes) (hpS : p.val ∉ ({2, 3, 5, 241} : Finset ℕ))
    (hodd : p.val % 2 = 1) (a : ZMod p.val) (ha : a * a = a + 60) (v : Fin 8 → ZMod 2)
    (hE : ∀ k, (((alphaCoords k).1 : ZMod p.val) + ((alphaCoords k).2 : ZMod p.val) * a) ^
        ((p.val - 1) / 2) = ((binarySignInteger (v k) : ℤ) : ZMod p.val))
    (hN : ∀ k, (2 : ZMod p.val) *
        (((alphaCoords k).1 : ZMod p.val) + ((alphaCoords k).2 : ZMod p.val) * a) ≠ 0)
    (hS : (241 : ZMod p.val) ^ ((p.val - 1) / 2) = 1) (h482 : (482 : ZMod p.val) ≠ 0)
    (hW : ∀ i : Fin 4, bilFormula i (phi1 i v) (phi1 i v) = 0) :
    ContribLowerBound EW p [(1 / 4, 2)] := by
  have h := contribLowerBound_of_towerClasses B EW p [()] (fun _ => censusPlaceFiber p a ha)
    (fun _ => 1 / 4) (fun _ => 2) (List.nodup_singleton _) (by simp) (by simp)
    (fun _ _ P => (census_fiber_bound p hpS hodd a ha v hE hN hS h482 hW P).1)
    (fun _ _ => card_censusFiber_ge p hpS hodd a ha v hE hN hS h482 hW)
  simpa using h

theorem censusPlace_ne (p : Nat.Primes) (a a' : ZMod p.val) (ha : a * a = a + 60)
    (ha' : a' * a' = a' + 60) (hne : a ≠ a') :
    censusPlaceFiber p a ha ≠ censusPlaceFiber p a' ha' := by
  intro h
  have h1 : (censusPlace p a ha).asIdeal = (censusPlace p a' ha').asIdeal :=
    congrArg (fun x : PrimeFiber ℚ B (rationalPrimePlace p) => x.1.asIdeal) h
  have h2 : omega - ((a.val : ℕ) : 𝓞 B) ∈ (censusPlace p a ha).asIdeal := by
    rw [mem_censusPlace, map_sub, evalHom_omega, map_natCast, ZMod.natCast_zmod_val, sub_self]
  rw [h1, mem_censusPlace, map_sub, evalHom_omega, map_natCast, ZMod.natCast_zmod_val,
    sub_eq_zero] at h2
  exact hne h2.symm

/-- Two good census places: contribution at least `φ(p²)/2`. -/
theorem censusTwo_of_places (p : Nat.Primes) (hpS : p.val ∉ ({2, 3, 5, 241} : Finset ℕ))
    (hodd : p.val % 2 = 1) (hS : (241 : ZMod p.val) ^ ((p.val - 1) / 2) = 1)
    (h482 : (482 : ZMod p.val) ≠ 0)
    (a : ZMod p.val) (ha : a * a = a + 60) (v : Fin 8 → ZMod 2)
    (hE : ∀ k, (((alphaCoords k).1 : ZMod p.val) + ((alphaCoords k).2 : ZMod p.val) * a) ^
        ((p.val - 1) / 2) = ((binarySignInteger (v k) : ℤ) : ZMod p.val))
    (hN : ∀ k, (2 : ZMod p.val) *
        (((alphaCoords k).1 : ZMod p.val) + ((alphaCoords k).2 : ZMod p.val) * a) ≠ 0)
    (hW : ∀ i : Fin 4, bilFormula i (phi1 i v) (phi1 i v) = 0)
    (a' : ZMod p.val) (ha' : a' * a' = a' + 60) (v' : Fin 8 → ZMod 2)
    (hE' : ∀ k, (((alphaCoords k).1 : ZMod p.val) + ((alphaCoords k).2 : ZMod p.val) * a') ^
        ((p.val - 1) / 2) = ((binarySignInteger (v' k) : ℤ) : ZMod p.val))
    (hN' : ∀ k, (2 : ZMod p.val) *
        (((alphaCoords k).1 : ZMod p.val) + ((alphaCoords k).2 : ZMod p.val) * a') ≠ 0)
    (hW' : ∀ i : Fin 4, bilFormula i (phi1 i v') (phi1 i v') = 0) (hne : a ≠ a') :
    ContribLowerBound EW p [(1 / 2, 2)] := by
  have h := contribLowerBound_of_towerClasses B EW p [false, true]
    (fun b => if b then censusPlaceFiber p a' ha' else censusPlaceFiber p a ha)
    (fun _ => 1 / 4) (fun _ => 2) (by simp) (by
      intro i hi j hj hij
      fin_cases i <;> fin_cases j <;> simp_all [censusPlace_ne p a a' ha ha' hne,
        (censusPlace_ne p a a' ha ha' hne).symm]) (by simp)
    (by
      intro i _ P
      cases i
      · exact (census_fiber_bound p hpS hodd a ha v hE hN hS h482 hW P).1
      · exact (census_fiber_bound p hpS hodd a' ha' v' hE' hN' hS h482 hW' P).1)
    (by
      intro i _
      cases i
      · exact card_censusFiber_ge p hpS hodd a ha v hE hN hS h482 hW
      · exact card_censusFiber_ge p hpS hodd a' ha' v' hE' hN' hS h482 hW')
  have h2 := ContribLowerBound.merge (by simpa using h)
  norm_num at h2
  exact h2

end UnitDistance.Sqrt241.Wide
