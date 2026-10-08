module

public import UnitDistance.Sqrt241.Wide.Census
public import UnitDistance.RetainedDyadicDifferentInertia

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# The dyadic types of `E_W`

`M` has type `(e, f) = (8, 4)` at `2` (`Retained.M_types 0`), so every prime of `E_W` above `2`
has `e ≤ 8` and norm `≤ 16`. At the prime `𝔮*` of `B` below the normalized dyadic place `P = 1`
of `Local.dyadicLocal` the residue degree drops to `≤ 2`:

* at the chosen place `𝔔₀` of `M` above `2` the decomposition group is `dyadicK(D)`
  (`D` the order-32 local cut), and the image of `z²` acts nontrivially on the residue field
  `𝔽₁₆` (`D →` the cyclic residue Galois group of order `4`;
  `Dyadic.D.z_sq_not_ker_of_surjective_cyclic_card_four`);
* conjugating by the frame element moves `𝔔₀` to a prime `Q₁` above the place `P = 1`; the
  conjugated element is `dyadicLocal 1 ξ` with `localCut ξ = z²`, whose retained image is
  `dyadicMap 1 (z²)`, with trivial label and trivial D4 signs (`λ_i(2716) = 0`); so it fixes
  `E_W`;
* every prime of `M` above `𝔮*` is a `G_B`-conjugate of `Q₁` (a conjugate by an element moving
  `√241` would also move `𝔮*`), so it has an element of its decomposition group fixing `E_W`
  and acting nontrivially on its residue field `𝔽₁₆`; the residues of `𝓞 E_W` lie in the fixed
  field, of order `≤ 4`.

Counting with `[E_W : B] = 4096` gives `ContribLowerBound E_W 2 [(1/32, 2), (1/64, 4)]`
(`wide_two`).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Wide

open NumberField IsDedekindDomain UnitDistance.NumberFieldAnalysis UnitDistance.Sqrt241.Analytic
open CanonicalGenus CanonicalWide Base Tower Multiquadratic Retained ClassTwo Local
open UnitDistance.PrimeCompletion Presentation Cut GroupData
open scoped Pointwise

attribute [local instance] PrimeCompletion.primeFact PrimeCompletion.baseRationalAlgebra

local notation "EW" => CanonicalWide.Carrier

/-! ### Fixed points of a nontrivial automorphism of `𝔽₁₆` -/

/-- The fixed points of a nontrivial ring endomorphism of a field with `16` elements form a
field with at most `4` elements. -/
theorem card_fixed_le {k : Type*} [Field k] [Fintype k] (hk : Fintype.card k = 16) (φ : k →+* k)
    (hφ : ∃ y, φ y ≠ y) : Nat.card {u : k // φ u = u} ≤ 4 := by
  classical
  rw [Nat.card_eq_fintype_card]
  let S : Subfield k :=
    { carrier := {u | φ u = u}
      mul_mem' := fun {a b} (ha : φ a = a) (hb : φ b = b) => by
        change φ (a * b) = a * b
        rw [map_mul, ha, hb]
      one_mem' := map_one φ
      add_mem' := fun {a b} (ha : φ a = a) (hb : φ b = b) => by
        change φ (a + b) = a + b
        rw [map_add, ha, hb]
      zero_mem' := map_zero φ
      neg_mem' := fun {a} (ha : φ a = a) => by
        change φ (-a) = -a
        rw [map_neg, ha]
      inv_mem' := fun a (ha : φ a = a) => by
        change φ a⁻¹ = a⁻¹
        rw [map_inv₀, ha] }
  have hS : Fintype.card S = Fintype.card {u : k // φ u = u} := rfl
  have hlt : Fintype.card {u : k // φ u = u} < 16 := by
    obtain ⟨y, hy⟩ := hφ
    rw [← hk]
    exact Fintype.card_subtype_lt hy
  have h1 := Module.card_eq_pow_finrank (K := S) (V := k)
  rw [hk, hS] at h1
  set c := Fintype.card {u : k // φ u = u}
  have hc2 : 2 ≤ c := by
    have : 1 < c := by
      rw [← hS]
      exact Fintype.one_lt_card
    omega
  set d := Module.finrank S k
  rcases Nat.lt_or_ge d 2 with hd | hd
  · interval_cases d
    · simp at h1
    · simp at h1
      omega
  · have : c ^ 2 ≤ c ^ d := Nat.pow_le_pow_right (by omega) hd
    have h2 : c ^ 2 ≤ 16 := by omega
    nlinarith

/-- **Residues fixed by a residually nontrivial automorphism.** If `h` stabilizes `Q`, acts
nontrivially on `𝓞 M ⧸ Q ≅ 𝔽₁₆` and fixes `𝓞 E_W`, the prime of `E_W` below `Q` has norm `≤ 4`. -/
theorem card_quot_le_four (Q : Ideal (𝓞 MW)) [Q.IsMaximal] (hQ16 : Nat.card (𝓞 MW ⧸ Q) = 16)
    (h : Gal(MW/ℚ)) (hstab : ∀ y ∈ Q, h • y ∈ Q) (hnt : ∃ y, h • y - y ∉ Q)
    (hfix : ∀ x : 𝓞 EW, h • algebraMap (𝓞 EW) (𝓞 MW) x = algebraMap (𝓞 EW) (𝓞 MW) x)
    (P : Ideal (𝓞 EW)) (hP : P = Q.comap (algebraMap (𝓞 EW) (𝓞 MW))) :
    Nat.card (𝓞 EW ⧸ P) ≤ 4 := by
  subst hP
  letI := Ideal.Quotient.field Q
  haveI : Finite (𝓞 MW ⧸ Q) := Nat.finite_of_card_ne_zero (by rw [hQ16]; norm_num)
  letI := Fintype.ofFinite (𝓞 MW ⧸ Q)
  let φ : (𝓞 MW ⧸ Q) →+* (𝓞 MW ⧸ Q) :=
    Ideal.quotientMap Q (MulSemiringAction.toRingHom _ _ h) (fun y hy => hstab y hy)
  have hφ : ∃ u, φ u ≠ u := by
    obtain ⟨y, hy⟩ := hnt
    refine ⟨Ideal.Quotient.mk Q y, fun he => hy ?_⟩
    exact Ideal.Quotient.eq.mp he
  have hcard := card_fixed_le (by rw [← Nat.card_eq_fintype_card]; exact hQ16) φ hφ
  let ι := Ideal.quotientMap Q (algebraMap (𝓞 EW) (𝓞 MW)) le_rfl
  have hinj : Function.Injective ι := Ideal.quotientMap_injective
  let F : (𝓞 EW ⧸ Q.comap (algebraMap (𝓞 EW) (𝓞 MW))) → {u // φ u = u} := fun z =>
    ⟨ι z, by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
      change Ideal.Quotient.mk Q (h • algebraMap (𝓞 EW) (𝓞 MW) x) = _
      rw [hfix]
      rfl⟩
  exact (Nat.card_le_card_of_injective F (fun a b hab => hinj (congrArg Subtype.val hab))).trans
    hcard

/-! ### The chosen place above `2` -/

theorem hkerM : inputSym.kernelHat ≤ MW.fixingSubgroup :=
  inputSym_kernelHat_le.trans input.admissible_M.kernelHat_le

theorem hcoreM : MW.fixingSubgroup ≤ inputSym.core := by rw [inputSym_core, input.M_fixingSubgroup]

/-- The local dyadic group in `Gal(M/ℚ)`. -/
abbrev dK : Dyadic.D →* Gal(MW/ℚ) := dyadicK hkerM

theorem decompositionRestriction_dyadic :
    decompositionRestriction prime2 MW (jK MW) = dK.comp dyadicCutD := by
  rw [← decompositionMapB_factor _ _ (resB_dyadicLocal_factor hkerM),
    decompositionRestriction_eq_comp]
  rfl

/-- The chosen prime of `M` above `2`. -/
abbrev Q0 : HeightOneSpectrum (𝓞 MW) := restrictedAbsolutePrime MW prime2 (jK MW)

instance Q0_liesOver : Q0.asIdeal.LiesOver (rationalPrimeIdeal 2) :=
  restrictedAbsolutePrime_liesOver MW prime2 (jK MW)

theorem dK_mem_stabilizer (d : Dyadic.D) : dK d ∈ MulAction.stabilizer Gal(MW/ℚ) Q0.asIdeal := by
  rw [← decompositionRestriction_range MW prime2 (jK MW)]
  obtain ⟨a, rfl⟩ := dyadicCutD_surjective d
  exact ⟨a, by rw [decompositionRestriction_dyadic]; rfl⟩

theorem exists_dK_eq (g : MulAction.stabilizer Gal(MW/ℚ) Q0.asIdeal) : ∃ d, dK d = g.1 := by
  have hg : g.1 ∈ (decompositionRestriction prime2 MW (jK MW)).range := by
    rw [decompositionRestriction_range MW prime2 (jK MW)]
    exact g.2
  obtain ⟨a, ha⟩ := hg
  exact ⟨dyadicCutD a, by rw [← ha, decompositionRestriction_dyadic]; rfl⟩

/-- `M` has type `(8, 4)` at `2`. -/
theorem M_two : (rationalPrimeIdeal 2).ramificationIdxIn (𝓞 MW) = 8 ∧
    (rationalPrimeIdeal 2).inertiaDegIn (𝓞 MW) = 4 := by
  have h := image_cards_2 hkerM hcoreM
  exact ramification_residue_of_absolute_image_cards prime2 MW (jK MW) 8 4 (by norm_num) h.1 h.2

/-- `M` has residue field `𝔽₁₆` above `2`. -/
theorem card_quot_two (Q : Ideal (𝓞 MW)) [Q.IsPrime] [Q.LiesOver (rationalPrimeIdeal 2)] :
    Nat.card (𝓞 MW ⧸ Q) = 16 := by
  have h := Ideal.pow_inertiaDeg 2 Q
  rw [← Ideal.inertiaDegIn_eq_inertiaDeg (rationalPrimeIdeal 2) Q Gal(MW/ℚ),
    M_two.2] at h
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, ← h]
  rfl

/-- `e ≤ 8` above `2` in `M`. -/
theorem ramificationIdx_two (Q : Ideal (𝓞 MW)) [Q.IsPrime] [Q.LiesOver (rationalPrimeIdeal 2)] :
    Q.ramificationIdx ℤ = 8 := by
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (rationalPrimeIdeal 2) Q Gal(MW/ℚ)]
  exact M_two.1

/-- **`z²` acts nontrivially on the residue field at the chosen place.** -/
theorem dK_z_sq_nontrivial : ∃ y : 𝓞 MW, dK (Dyadic.D.z ^ 2) • y - y ∉ Q0.asIdeal := by
  haveI : Q0.asIdeal.IsMaximal := Q0.isPrime.isMaximal Q0.ne_bot
  haveI : (rationalPrimeIdeal 2).IsMaximal := inferInstance
  letI := Ideal.Quotient.field Q0.asIdeal
  letI := Ideal.Quotient.field (rationalPrimeIdeal 2)
  haveI : Finite (𝓞 MW ⧸ Q0.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient Q0.ne_bot
  let st := Ideal.Quotient.stabilizerHom Q0.asIdeal (rationalPrimeIdeal 2) Gal(MW/ℚ)
  let f := st.comp (dK.codRestrict _ dK_mem_stabilizer)
  have hf : Function.Surjective f := by
    intro τ
    obtain ⟨g, rfl⟩ := Ideal.Quotient.stabilizerHom_surjective Gal(MW/ℚ) (rationalPrimeIdeal 2)
      Q0.asIdeal τ
    obtain ⟨d, hd⟩ := exists_dK_eq g
    refine ⟨d, ?_⟩
    change st ⟨dK d, _⟩ = st g
    congr 1
    exact Subtype.ext hd
  have hcard : Nat.card ((𝓞 MW ⧸ Q0.asIdeal) ≃ₐ[ℤ ⧸ rationalPrimeIdeal 2] (𝓞 MW ⧸ Q0.asIdeal)) =
      4 := by
    rw [IsGalois.card_aut_eq_finrank, ← Ideal.inertiaDeg_eq_of_isMaximal (rationalPrimeIdeal 2),
      ← Ideal.inertiaDegIn_eq_inertiaDeg (rationalPrimeIdeal 2) Q0.asIdeal Gal(MW/ℚ),
      M_two.2]
  have hz := Dyadic.D.z_sq_not_ker_of_surjective_cyclic_card_four f hf hcard
  by_contra hall
  push Not at hall
  apply hz
  apply AlgEquiv.ext
  intro u
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective u
  change Ideal.Quotient.mk Q0.asIdeal (dK (Dyadic.D.z ^ 2) • y) = Ideal.Quotient.mk Q0.asIdeal y
  exact Ideal.Quotient.eq.mpr (hall y)

/-! ### The D4 signs through the retained quotient -/

theorem chiHom_eq_lambda (i : Fin 4) (g : GB) :
    chiHom i g = lambdaHom i (ell i) (input.retainedMap g) := by
  obtain ⟨s, rfl⟩ := freeMap_surjective g
  rw [input.retainedMap_freeMap]
  exact chi_freeMap i s

/-- An element of `G_B` whose retained image is central with trivial `λ`-values fixes `E_W`. -/
theorem mem_EWfix_of_retained (g : GB) (hbase : (input.retainedMap g).base = 0)
    (hc : ∀ i, lam i (input.retainedMap g).central = 0) : (g : Ghat) ∈ EWfix := by
  have hlab : genusLabel g = 1 := by
    apply Multiplicative.toAdd.injective
    rw [← input.retainedMap_base, hbase]
    rfl
  have hEfix : (g : Ghat) ∈ Efix := (mem_ker_genusLabelHom_iff g).mp hlab
  have hker : (⟨_, hEfix⟩ : Efix) ∈ psiHom.ker := by
    rw [MonoidHom.mem_ker]
    apply Multiplicative.toAdd.injective
    funext i
    rw [psiHom_apply]
    change (chiHom i g).central = 0
    rw [chiHom_eq_lambda, lambdaHom_apply]
    change lam i (input.retainedMap g).central + qq i (input.retainedMap g).base +
      ell i (input.retainedMap g).base = 0
    rw [hbase, qq_zero, map_zero, hc i]
    rfl
  rw [ker_psiHom] at hker
  exact hker

/-- Conjugation in `G_B` does not change a central retained image. -/
theorem retainedMap_conj (γ g : GB) (hbase : (input.retainedMap g).base = 0) :
    input.retainedMap (γ * g * γ⁻¹) = input.retainedMap g := by
  have hcomm : input.retainedMap γ * input.retainedMap g =
      input.retainedMap g * input.retainedMap γ := by
    apply GroupModel.ext
    · simp only [GroupModel.mul_base, hbase, add_zero, zero_add]
    · simp only [GroupModel.mul_central, hbase, map_zero, LinearMap.zero_apply, add_zero]
      abel
  rw [map_mul, map_mul, map_inv, hcomm, mul_inv_cancel_right]

/-- The retained image of the normalized dyadic map factors through the local cut. -/
theorem retainedMap_dyadicLocal (P : Fin 2) (g : PadicTwoMaximalProTwo.Group) :
    input.retainedMap (dyadicLocal P g) =
      Retained.dyadicMapOfLifts P (retainedFree (input.A.lifts.dyadicX P))
        (retainedFree (input.A.lifts.dyadicY P)) (retainedFree (input.A.lifts.dyadicZ P))
        (localCut g) := by
  have h : input.retainedMap.toMonoidHom.comp (dyadicLocal P).toMonoidHom =
      (Retained.dyadicMapOfLifts P (retainedFree (input.A.lifts.dyadicX P))
        (retainedFree (input.A.lifts.dyadicY P))
        (retainedFree (input.A.lifts.dyadicZ P))).comp localCut.toMonoidHom := by
    apply factor_through_localCut
    apply MonoidHom.ext
    intro s
    change input.retainedMap (dyadicLocal P (SigmaDyadic.localPresentation s)) = _
    rw [show dyadicLocal P (SigmaDyadic.localPresentation s) = freeMap (input.A.dyadic P s) from
      (LocalElements.freeMap_dyadicLift input.E P s).symm, input.retainedMap_freeMap]
    calc retainedFree (input.A.dyadic P s)
        = input.A.retained input.hL (input.A.projection (input.A.dyadic P s)) := rfl
      _ = input.A.retained input.hL (input.A.dyadicQuotientMap genuineRelation
            detector_genuineRelation input.hgen P (Dyadic.ArithmeticPresentation.model s)) := by
          rw [SourceLifts.dyadicQuotientMap_model]
      _ = _ := DFunLike.congr_fun (input.A.retained_dyadicQuotientMap genuineRelation
            detector_genuineRelation input.hgen input.hL P) _
  exact DFunLike.congr_fun h g

theorem dyadicMapFn_z_sq_base (P : Fin 2) :
    (Retained.dyadicMapFn P (Dyadic.D.z ^ 2)).base = 0 := by
  fin_cases P <;> decide +kernel

/-- At `z²` the central shear does nothing. -/
theorem dyadicMapOfLifts_z_sq (P : Fin 2) (a b c : Retained.Q) :
    Retained.dyadicMapOfLifts P a b c (Dyadic.D.z ^ 2) = Retained.dyadicMapFn P (Dyadic.D.z ^ 2) := by
  apply GroupModel.ext
  · rfl
  · change (Retained.dyadicMapFn P (Dyadic.D.z ^ 2)).central +
      Retained.dyadicAdjustment P a.central b.central c.central
        (Retained.dyadicMapFn P (Dyadic.D.z ^ 2)).base = _
    rw [dyadicMapFn_z_sq_base, map_zero, add_zero]

/-- **At `𝔭₂` the four `λ`'s vanish on `z²`** (central mask `2716`). -/
theorem lam_dyadic_z_sq (i : Fin 4) : lam i (Retained.dyadicMapFn 1 (Dyadic.D.z ^ 2)).central = 0 := by
  fin_cases i <;> decide +kernel

/-! ### The element and the prime at the place `P = 1` -/

theorem exists_sig0 : ∃ σ₀ : PadicTwoMaximalProTwo.AbsoluteGroup,
    dyadicCutD (PadicTwoGlobalMap.decomposition σ₀) = Dyadic.D.z ^ 2 := by
  obtain ⟨a, ha⟩ := dyadicCutD_surjective (Dyadic.D.z ^ 2)
  obtain ⟨σ₀, rfl⟩ := PadicTwoGlobalMap.decomposition_surjective a
  exact ⟨σ₀, ha⟩

/-- A local automorphism with cut image `z²`. -/
def sig0 : PadicTwoMaximalProTwo.AbsoluteGroup := exists_sig0.choose

theorem sig0_spec : dyadicCutD (PadicTwoGlobalMap.decomposition sig0) = Dyadic.D.z ^ 2 :=
  exists_sig0.choose_spec

/-- `h̃₁ = dyadicLocal 1 ξ` with `localCut ξ = z²`. -/
def hT : GB := dyadicLocal 1 (PadicTwoMaximalProTwo.projection sig0)

theorem hT_coe : (hT : Ghat) = frame dyadicPlace 1 *
    decompositionMap prime2 (PadicTwoGlobalMap.decomposition sig0) * (frame dyadicPlace 1)⁻¹ := by
  rw [hT, dyadicLocal_projection, coe_conjGB]
  rfl

theorem retainedMap_hT : input.retainedMap hT = Retained.dyadicMapFn 1 (Dyadic.D.z ^ 2) := by
  rw [hT, retainedMap_dyadicLocal, ← dyadicCutD_decomposition, sig0_spec, dyadicMapOfLifts_z_sq]

theorem retainedMap_hT_base : (input.retainedMap hT).base = 0 := by
  rw [retainedMap_hT, dyadicMapFn_z_sq_base]

theorem hT_mem_EWfix : (hT : Ghat) ∈ EWfix :=
  mem_EWfix_of_retained hT retainedMap_hT_base (fun i => by rw [retainedMap_hT]; exact lam_dyadic_z_sq i)

/-- The frame element in `Gal(M/ℚ)`. -/
def g1 : Gal(MW/ℚ) := Input.res MW (frame dyadicPlace 1)

/-- `h₁ = g₁ dK(z²) g₁⁻¹`. -/
def h1 : Gal(MW/ℚ) := g1 * dK (Dyadic.D.z ^ 2) * g1⁻¹

theorem res_hT : Input.res MW (hT : Ghat) = h1 := by
  rw [hT_coe, map_mul, map_mul, map_inv, h1, g1]
  congr 2
  rw [← decompositionRestriction_eq MW prime2, decompositionRestriction_dyadic, MonoidHom.comp_apply,
    sig0_spec]

/-- The prime `Q₁ = g₁ Q₀` of `M`. -/
def Q1 : Ideal (𝓞 MW) := g1 • Q0.asIdeal

instance Q1_isPrime : Q1.IsPrime := by
  rw [Q1, Ideal.pointwise_smul_eq_comap]
  exact Ideal.comap_isPrime _ _

theorem smul_two (g : Gal(MW/ℚ)) : g • (2 : 𝓞 MW) = 2 :=
  map_ofNat (MulSemiringAction.toRingHom Gal(MW/ℚ) (𝓞 MW) g) 2

theorem two_mem_of_liesOver (Q : Ideal (𝓞 MW)) [Q.LiesOver (rationalPrimeIdeal 2)] :
    (2 : 𝓞 MW) ∈ Q := by
  have h : (2 : ℤ) ∈ Q.under ℤ := by
    rw [← Ideal.over_def Q (rationalPrimeIdeal 2)]
    exact Ideal.subset_span (Set.mem_singleton _)
  simpa using h

theorem liesOver_two_of_mem (Q : Ideal (𝓞 MW)) [Q.IsPrime] (h : (2 : 𝓞 MW) ∈ Q) :
    Q.LiesOver (rationalPrimeIdeal 2) := by
  constructor
  apply Ideal.IsMaximal.eq_of_le (inferInstance : (rationalPrimeIdeal 2).IsMaximal)
    (Ideal.IsPrime.ne_top inferInstance)
  rw [Ideal.span_singleton_le_iff_mem]
  change algebraMap ℤ (𝓞 MW) _ ∈ Q
  simpa using h

theorem two_mem_Q1 : (2 : 𝓞 MW) ∈ Q1 := by
  rw [Q1, ← smul_two g1]
  exact Ideal.smul_mem_pointwise_smul _ _ _ (two_mem_of_liesOver Q0.asIdeal)

instance Q1_liesOver : Q1.LiesOver (rationalPrimeIdeal 2) := liesOver_two_of_mem Q1 two_mem_Q1

theorem conj_smul_ideal {G S : Type*} [Group G] [CommRing S] [MulSemiringAction G S] (g h : G)
    (I : Ideal S) (hI : h • I = I) : (g * h * g⁻¹) • (g • I) = g • I := by
  rw [mul_smul, mul_smul, inv_smul_smul, hI]

theorem conj_nontrivial {G S : Type*} [Group G] [CommRing S] [MulSemiringAction G S] (g h : G)
    (I : Ideal S) (y : S) (hy : h • y - y ∉ I) : (g * h * g⁻¹) • (g • y) - g • y ∉ g • I := by
  intro hmem
  apply hy
  have e : (g * h * g⁻¹) • (g • y) - g • y = g • (h • y - y) := by
    rw [smul_sub, mul_smul, mul_smul, inv_smul_smul]
  rw [e] at hmem
  exact Ideal.smul_mem_pointwise_smul_iff.mp hmem

theorem h1_stab : h1 • Q1 = Q1 :=
  conj_smul_ideal g1 _ Q0.asIdeal (MulAction.mem_stabilizer_iff.mp (dK_mem_stabilizer _))

theorem h1_nontrivial : ∃ y, h1 • y - y ∉ Q1 := by
  obtain ⟨y, hy⟩ := dK_z_sq_nontrivial
  exact ⟨g1 • y, conj_nontrivial g1 _ Q0.asIdeal y hy⟩

/-! ### The two primes of `B` above `2` -/

theorem two_ne_zero_B : (2 : 𝓞 B) ≠ 0 := two_ne_zero

/-- The prime of `B` below `Q₁`. -/
def qStar : HeightOneSpectrum (𝓞 B) where
  asIdeal := Q1.comap iotaB
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    have h2 : (2 : 𝓞 B) ∈ Q1.comap iotaB := by
      rw [Ideal.mem_comap, map_ofNat]
      exact two_mem_Q1
    rw [h, Ideal.mem_bot] at h2
    exact two_ne_zero_B h2

theorem two_mem_qStar : (2 : 𝓞 B) ∈ qStar.asIdeal := by
  change (2 : 𝓞 B) ∈ Q1.comap iotaB
  rw [Ideal.mem_comap, map_ofNat]
  exact two_mem_Q1

theorem under_eq_two (𝔮 : HeightOneSpectrum (𝓞 B)) (h2 : (2 : 𝓞 B) ∈ 𝔮.asIdeal) :
    𝔮.under (𝓞 ℚ) = rationalPrimePlace ⟨2, Nat.prime_two⟩ := by
  apply HeightOneSpectrum.ext
  symm
  apply Ideal.IsMaximal.eq_of_le ((rationalPrimePlace ⟨2, Nat.prime_two⟩).isPrime.isMaximal
    (rationalPrimePlace ⟨2, Nat.prime_two⟩).ne_bot) (Ideal.IsPrime.ne_top inferInstance)
  rw [rationalPrimePlace_asIdeal, Ideal.span_singleton_le_iff_mem]
  change algebraMap (𝓞 ℚ) (𝓞 B) ((2 : ℕ) : 𝓞 ℚ) ∈ 𝔮.asIdeal
  rw [map_natCast]
  exact_mod_cast h2

/-- `ω` or `1 - ω` lies in every prime of `B` above `2` (`ω (1 - ω) = -60`). -/
theorem omega_or_mem (𝔮 : HeightOneSpectrum (𝓞 B)) (h2 : (2 : 𝓞 B) ∈ 𝔮.asIdeal) :
    omega ∈ 𝔮.asIdeal ∨ 1 - omega ∈ 𝔮.asIdeal := by
  apply 𝔮.isPrime.mem_or_mem
  have e : omega * (1 - omega) = 2 * (-30) := by
    linear_combination -omega_mul_omega
  rw [e]
  exact 𝔮.asIdeal.mul_mem_right _ h2

theorem one_not_mem (𝔮 : HeightOneSpectrum (𝓞 B)) (h : omega ∈ 𝔮.asIdeal)
    (h' : 1 - omega ∈ 𝔮.asIdeal) : False := by
  apply 𝔮.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  simpa using 𝔮.asIdeal.add_mem h h'

theorem two_omega : 2 * omega = 1 + sqrt241Int := by
  rw [sqrt241Int]
  unfold Base.mk
  push_cast
  ring

/-- The conjugate prime of `B`. -/
def qStar' : HeightOneSpectrum (𝓞 B) where
  asIdeal := qStar.asIdeal.comap sigmaInt.toRingHom
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    have h2 : (2 : 𝓞 B) ∈ qStar.asIdeal.comap sigmaInt.toRingHom := by
      rw [Ideal.mem_comap, map_ofNat]
      exact two_mem_qStar
    rw [h, Ideal.mem_bot] at h2
    exact two_ne_zero_B h2

theorem two_mem_qStar' : (2 : 𝓞 B) ∈ qStar'.asIdeal := by
  change (2 : 𝓞 B) ∈ qStar.asIdeal.comap sigmaInt.toRingHom
  rw [Ideal.mem_comap, map_ofNat]
  exact two_mem_qStar

theorem sigmaInt_omega : sigmaInt omega = 1 - omega := by
  rw [← mk_zero_one, sigmaInt_mk]
  unfold Base.mk
  push_cast
  ring

theorem qStar_ne : qStar ≠ qStar' := by
  intro h
  have hσ : ∀ b, b ∈ qStar.asIdeal → sigmaInt b ∈ qStar.asIdeal := by
    intro b hb
    have : b ∈ qStar'.asIdeal := h ▸ hb
    exact this
  rcases omega_or_mem qStar two_mem_qStar with h0 | h0
  · have := hσ _ h0
    rw [sigmaInt_omega] at this
    exact one_not_mem qStar h0 this
  · have := hσ _ h0
    rw [map_sub, map_one, sigmaInt_omega, sub_sub_cancel] at this
    exact one_not_mem qStar this h0

/-- The two primes of `B` above `2` as elements of the fibre. -/
def qStarFiber : PrimeFiber ℚ B (rationalPrimePlace ⟨2, Nat.prime_two⟩) :=
  ⟨qStar, under_eq_two qStar two_mem_qStar⟩

def qStarFiber' : PrimeFiber ℚ B (rationalPrimePlace ⟨2, Nat.prime_two⟩) :=
  ⟨qStar', under_eq_two qStar' two_mem_qStar'⟩

/-! ### Fibre bounds -/

/-- A prime of `M` above a prime `P` of `E_W`. -/
theorem exists_prime_above (𝔮 : HeightOneSpectrum (𝓞 B)) (P : PrimeFiber B EW 𝔮) :
    ∃ Q : Ideal (𝓞 MW), Q.IsPrime ∧ Q.LiesOver P.1.asIdeal := by
  have := P.1.isPrime
  obtain ⟨⟨Q, hQ1, hQ2⟩⟩ := (inferInstance : Nonempty (P.1.asIdeal.primesOver (𝓞 MW)))
  exact ⟨Q, hQ1, hQ2⟩

/-- `e ≤ 8` and `N ≤ 16` for every prime of `E_W` above `2`. -/
theorem two_fiber_bound (𝔮 : HeightOneSpectrum (𝓞 B)) (h2 : (2 : 𝓞 B) ∈ 𝔮.asIdeal)
    (P : PrimeFiber B EW 𝔮) (Q : Ideal (𝓞 MW)) [Q.IsPrime] [Q.LiesOver P.1.asIdeal] :
    Q.LiesOver (rationalPrimeIdeal 2) ∧ P.1.asIdeal.ramificationIdx (𝓞 B) ≤ 8 ∧
      Nat.card (𝓞 EW ⧸ P.1.asIdeal) ≤ 16 := by
  have := P.1.isPrime
  have hPover : P.1.asIdeal.LiesOver 𝔮.asIdeal := primeFiber_liesOver B EW 𝔮 P
  have h2Q : (2 : 𝓞 MW) ∈ Q := by
    have := (iotaB_mem_iff 𝔮 P Q 2).mpr h2
    rwa [map_ofNat] at this
  have hQ2 := liesOver_two_of_mem Q h2Q
  refine ⟨hQ2, ?_, ?_⟩
  · have hQe := ramificationIdx_two Q
    have h1 : P.1.asIdeal.ramificationIdx ℤ ≤ 8 :=
      hQe ▸ Ideal.ramificationIdx_below_le (R := ℤ) P.1.asIdeal Q
    exact (Ideal.ramificationIdx_above_le (R := ℤ) 𝔮.asIdeal P.1.asIdeal).trans h1
  · have h16 := card_quot_two Q
    haveI : Finite (𝓞 MW ⧸ Q) := Nat.finite_of_card_ne_zero (by rw [h16]; norm_num)
    rw [← h16]
    have hP : P.1.asIdeal = Q.comap (algebraMap (𝓞 EW) (𝓞 MW)) := Ideal.over_def Q P.1.asIdeal
    rw [hP]
    exact Nat.card_le_card_of_injective _ (Ideal.quotientMap_injective (I := Q)
      (f := algebraMap (𝓞 EW) (𝓞 MW)))

/-- The residue degree from the norm. -/
theorem inertiaDeg_le_of_card (𝔮 : HeightOneSpectrum (𝓞 B)) (P : PrimeFiber B EW 𝔮) (n : ℕ)
    (h : Nat.card (𝓞 EW ⧸ P.1.asIdeal) ≤ 2 ^ n) : P.1.asIdeal.inertiaDeg (𝓞 B) ≤ n := by
  have := P.1.isPrime
  have hPover : P.1.asIdeal.LiesOver 𝔮.asIdeal := primeFiber_liesOver B EW 𝔮 P
  have hn := Ideal.absNorm_pow_inertiaDeg 𝔮.asIdeal P.1.asIdeal
  rw [Ideal.absNorm_apply P.1.asIdeal, Submodule.cardQuot_apply] at hn
  have hq : 2 ≤ Ideal.absNorm 𝔮.asIdeal := primeIdeal_absNorm_gt_one B 𝔮
  have : 2 ^ P.1.asIdeal.inertiaDeg (𝓞 B) ≤ 2 ^ n :=
    (Nat.pow_le_pow_left hq _).trans (hn ▸ h)
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this

/-- The good dyadic place: `N ≤ 4`. -/
theorem good_fiber_bound (P : PrimeFiber B EW qStar) :
    Nat.card (𝓞 EW ⧸ P.1.asIdeal) ≤ 4 ∧ P.1.asIdeal.ramificationIdx (𝓞 B) ≤ 8 := by
  have := P.1.isPrime
  obtain ⟨Q, hQprime, hQover⟩ := exists_prime_above qStar P
  obtain ⟨hQ2, he, -⟩ := two_fiber_bound qStar two_mem_qStar P Q
  refine ⟨?_, he⟩
  have hmem : ∀ b : 𝓞 B, iotaB b ∈ Q ↔ b ∈ qStar.asIdeal := fun b => iotaB_mem_iff qStar P Q b
  -- a Galois element moving `Q₁` to `Q`
  obtain ⟨γ, hγ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (rationalPrimeIdeal 2) Q1 Q Gal(MW/ℚ)
  obtain ⟨γt, hγt⟩ := GaloisEmbedding.restriction_surjective MW.val γ
  have hact : ∀ y : 𝓞 MW, toOmega (γ • y) = γt (toOmega y) := by
    intro y
    rw [← hγt]
    exact toOmega_smul γt y
  -- `γ` fixes `√241`
  have hγB : γt ∈ GB := by
    have hsq : (γ • sM) ^ 2 = sM ^ 2 := by
      rw [← smul_pow', sM_sq]
      exact map_ofNat (MulSemiringAction.toRingHom Gal(MW/ℚ) (𝓞 MW) γ) 241
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hs | hs
    · rw [mem_GB_iff]
      have := hact sM
      rw [hs, toOmega_sM] at this
      exact this.symm
    · exfalso
      have hω : γ • iotaB omega = iotaB (1 - omega) := by
        have e : (2 : 𝓞 B) * (1 - omega) = 1 - sqrt241Int := by
          rw [mul_sub, two_omega]
          ring
        have e1 : (2 : 𝓞 MW) * iotaB omega = 1 + sM := by
          rw [← map_ofNat iotaB 2, ← map_mul, two_omega, map_add, map_one]
          rfl
        have e2 : (2 : 𝓞 MW) * iotaB (1 - omega) = 1 - sM := by
          rw [← map_ofNat iotaB 2, ← map_mul, e, map_sub, map_one]
          rfl
        have e3 : (2 : 𝓞 MW) * (γ • iotaB omega) = γ • ((2 : 𝓞 MW) * iotaB omega) := by
          rw [smul_mul', smul_two]
        apply mul_left_cancel₀ (two_ne_zero : (2 : 𝓞 MW) ≠ 0)
        rw [e3, e1, smul_add, smul_one, hs, e2]
        ring
      have hQ1mem : ∀ b, b ∈ qStar.asIdeal → γ • iotaB b ∈ Q := by
        intro b hb
        rw [← hγ]
        exact Ideal.smul_mem_pointwise_smul _ _ _ hb
      rcases omega_or_mem qStar two_mem_qStar with h0 | h0
      · have := hQ1mem _ h0
        rw [hω, hmem] at this
        exact one_not_mem qStar h0 this
      · have := hQ1mem _ h0
        rw [map_sub, map_one, smul_sub, smul_one, hω, map_sub, map_one, sub_sub_cancel,
          hmem] at this
        exact one_not_mem qStar this h0
  -- the element `h = γ h₁ γ⁻¹`
  set g : GB := ⟨γt, hγB⟩
  have hfixT : ((g * hT * g⁻¹ : GB) : Ghat) ∈ EWfix :=
    mem_EWfix_of_retained _ (by rw [retainedMap_conj g hT retainedMap_hT_base]; exact retainedMap_hT_base)
      (fun i => by
        rw [retainedMap_conj g hT retainedMap_hT_base, retainedMap_hT]
        exact lam_dyadic_z_sq i)
  have hres : Input.res MW ((g * hT * g⁻¹ : GB) : Ghat) = γ * h1 * γ⁻¹ := by
    change Input.res MW (γt * (hT : Ghat) * γt⁻¹) = _
    rw [map_mul, map_mul, map_inv, res_hT, hγt]
  have hstab : (γ * h1 * γ⁻¹) • Q = Q := by
    rw [← hγ]
    exact conj_smul_ideal γ h1 Q1 h1_stab
  have hnt : ∃ y, (γ * h1 * γ⁻¹) • y - y ∉ Q := by
    obtain ⟨y, hy⟩ := h1_nontrivial
    refine ⟨γ • y, ?_⟩
    rw [← hγ]
    exact conj_nontrivial γ h1 Q1 y hy
  have hfix : ∀ x : 𝓞 EW, (γ * h1 * γ⁻¹) • algebraMap (𝓞 EW) (𝓞 MW) x =
      algebraMap (𝓞 EW) (𝓞 MW) x := by
    intro x
    apply toOmega_injective
    rw [← hres, toOmega_smul]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hfixT _ (toOmega_algebraMap_mem x)
  have hQmax : Q.IsMaximal := hQprime.isMaximal (by
    intro h
    have := two_mem_of_liesOver Q
    rw [h, Ideal.mem_bot] at this
    exact two_ne_zero this)
  exact card_quot_le_four Q (card_quot_two Q) _
    (fun y hy => by rw [← hstab]; exact Ideal.smul_mem_pointwise_smul _ _ _ hy) hnt hfix
    P.1.asIdeal (Ideal.over_def Q P.1.asIdeal)

/-! ### The dyadic contribution -/

theorem absNorm_eq_card (𝔮 : HeightOneSpectrum (𝓞 B)) (P : PrimeFiber B EW 𝔮) :
    Ideal.absNorm P.1.asIdeal = Nat.card (𝓞 EW ⧸ P.1.asIdeal) := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem card_good : ((1 / 32 : ℚ) : ℝ) * (Module.finrank ℚ EW : ℝ) ≤
    Fintype.card (PrimeFiber B EW qStar) := by
  have h := finrank_le_card_mul B EW qStar 16 fun P => by
    obtain ⟨h4, he⟩ := good_fiber_bound P
    have hf := inertiaDeg_le_of_card qStar P 2 (by simpa using h4)
    calc _ ≤ 8 * 2 := Nat.mul_le_mul he hf
      _ = 16 := rfl
  rw [finrank_B_Carrier] at h
  rw [finrank_field]
  have : (256 : ℝ) ≤ Fintype.card (PrimeFiber B EW qStar) := by
    exact_mod_cast (by omega : 256 ≤ Fintype.card (PrimeFiber B EW qStar))
  norm_num
  linarith

theorem card_bad : ((1 / 64 : ℚ) : ℝ) * (Module.finrank ℚ EW : ℝ) ≤
    Fintype.card (PrimeFiber B EW qStar') := by
  have h := finrank_le_card_mul B EW qStar' 32 fun P => by
    obtain ⟨Q, hQprime, hQover⟩ := exists_prime_above qStar' P
    obtain ⟨-, he, h16⟩ := two_fiber_bound qStar' two_mem_qStar' P Q
    have hf := inertiaDeg_le_of_card qStar' P 4 (by simpa using h16)
    calc _ ≤ 8 * 4 := Nat.mul_le_mul he hf
      _ = 32 := rfl
  rw [finrank_B_Carrier] at h
  rw [finrank_field]
  have : (128 : ℝ) ≤ Fintype.card (PrimeFiber B EW qStar') := by
    exact_mod_cast (by omega : 128 ≤ Fintype.card (PrimeFiber B EW qStar'))
  norm_num
  linarith

theorem qStarFiber_ne : qStarFiber ≠ qStarFiber' := fun h =>
  qStar_ne (congrArg Subtype.val h)

/-- **The dyadic part of `WideLocalTypes`.** -/
theorem wide_two : ContribLowerBound EW ⟨2, Nat.prime_two⟩ [(1 / 32, 2), (1 / 64, 4)] := by
  have h := contribLowerBound_of_towerClasses B EW ⟨2, Nat.prime_two⟩ [false, true]
    (fun b => if b then qStarFiber' else qStarFiber) (fun b => if b then 1 / 64 else 1 / 32)
    (fun b => if b then 4 else 2) (by simp) (by
      intro i hi j hj hij
      fin_cases i <;> fin_cases j <;> simp_all [qStarFiber_ne, qStarFiber_ne.symm]) (by
      intro i _
      cases i <;> simp)
    (by
      intro i _ P
      cases i
      · change Ideal.absNorm P.1.asIdeal ≤ 2 ^ 2
        rw [absNorm_eq_card]
        exact (good_fiber_bound P).1
      · change Ideal.absNorm P.1.asIdeal ≤ 2 ^ 4
        rw [absNorm_eq_card]
        obtain ⟨Q, hQprime, hQover⟩ := exists_prime_above qStar' P
        exact (two_fiber_bound qStar' two_mem_qStar' P Q).2.2)
    (by
      intro i _
      cases i
      · exact card_good
      · exact card_bad)
  simpa using h

end UnitDistance.Sqrt241.Wide
