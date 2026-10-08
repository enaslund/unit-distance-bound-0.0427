module

public import UnitDistance.Sqrt241.V2.Interface
public import UnitDistance.Sqrt241.V2.Signature
public import UnitDistance.Sqrt241.Numerics.Margin

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Version 2: the planar target from `V2.TowerData`

`V2.TowerData.target` is the analogue of version 1's `target_of_growing_galois_fields`
(`Geometry/FixedBaseBridge.lean`) for tower fields that need not be Galois over `ℚ`:

* the conjugation-fixed fields `F_j = K_j^{c_j}` and the quadratic extensions `K_j/F_j`
  are built without `IsGalois ℚ (Ks j)` (`fixedAut`, `quadratic`);
* the prime pairs are the conjugate pairs inside the **windows** of `V2.TowerData`
  (`windowPrimePairFamily`), and `window_count` gives the multiplicities;
* the signature bound comes from the Galois subfield `D` (`thetaMin_le_signatureRatio`);
* the fixed-base parameter is `ε = 1/4411`.

The planar construction itself is version 1's
`SIntegerCRT.target_of_witnessFields_of_residueCap`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

open NumberField NumberField.InfinitePlace IsDedekindDomain Filter

namespace UnitDistance.Sqrt241.V2

open UnitDistance.NumberFieldAnalysis UnitDistance.RelativeIdealCosets UnitDistance.RelativeUnits

/-! ### The conjugation-fixed field without `IsGalois ℚ K` -/

section Fixed

variable {K : Type} [Field K] [NumberField K]

/-- The conjugation, as an automorphism over its fixed field. -/
def fixedAut (c : K ≃ₐ[ℚ] K) : K ≃ₐ[GaloisConjugation.fixedField K c] K :=
  { c.toRingEquiv with
    commutes' := fun x => GaloisConjugation.generator_fixes c x }

theorem fixedAut_ne_one {c : K ≃ₐ[ℚ] K} (hc1 : c ≠ 1) : fixedAut c ≠ 1 := by
  intro he
  apply hc1
  ext x
  exact congrArg (fun e : K ≃ₐ[GaloisConjugation.fixedField K c] K => e x) he

/-- `K` is quadratic over the fixed field of a nontrivial complex conjugation. -/
theorem quadratic {φ : K →+* ℂ} {c : K ≃ₐ[ℚ] K} (hc : ComplexEmbedding.IsConj φ c)
    (hc1 : c ≠ 1) : Algebra.IsQuadraticExtension (GaloisConjugation.fixedField K c) K :=
  ⟨GaloisConjugation.relativeDegree_eq_two φ c hc hc1⟩

end Fixed

/-! ### Prime pairs inside the windows -/

section Windows

variable {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K]

instance windowFiber_finite (q : ℕ) (x : 𝓞 K) : Finite (WindowFiber K q x) :=
  Finite.of_injective (fun P : WindowFiber K q x => (⟨P.1, P.2.1⟩ : PrimeNormFiber K q))
    (fun P Q h => Subtype.ext (congrArg (fun y : PrimeNormFiber K q => y.1) h))

instance windowFiber_fintype (q : ℕ) (x : 𝓞 K) : Fintype (WindowFiber K q x) :=
  Fintype.ofFinite _

/-- Conjugation maps a window with a fixed element to itself. -/
def conjugateWindow (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (q : ℕ) (x : 𝓞 K)
    (hx : RingOfIntegers.mapRingHom ι.toRingHom x = x) (P : WindowFiber K q x) :
    WindowFiber K q x :=
  ⟨conjugatePrime ι hι P.1, (conjugateIdeal_absNorm ι P.1.asIdeal).trans P.2.1, by
    have hm := Ideal.mem_map_of_mem (RingOfIntegers.mapRingHom ι.toRingHom) P.2.2
    rw [hx] at hm
    exact hm⟩

theorem conjugateWindow_involutive (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (q : ℕ) (x : 𝓞 K)
    (hx : RingOfIntegers.mapRingHom ι.toRingHom x = x) :
    Function.Involutive (conjugateWindow ι hι q x hx) :=
  fun P => Subtype.ext (conjugatePrime_involutive ι hι P.1)

/-- One representative of each conjugate pair of window primes. -/
abbrev WindowPairIndex (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (q : ℕ) (x : 𝓞 K)
    (hx : RingOfIntegers.mapRingHom ι.toRingHom x = x) :=
  FreeInvolution.Representatives (conjugateWindow ι hι q x hx)

theorem windowPairIndex_card_mul_two (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (q : ℕ) (x : 𝓞 K)
    (hx : RingOfIntegers.mapRingHom ι.toRingHom x = x)
    (hfree : ∀ P : WindowFiber K q x, conjugateIdeal ι P.1.asIdeal ≠ P.1.asIdeal) :
    Fintype.card (WindowPairIndex ι hι q x hx) * 2 = Nat.card (WindowFiber K q x) := by
  rw [Nat.card_eq_fintype_card]
  apply FreeInvolution.card_representatives_mul_two _ (conjugateWindow_involutive ι hι q x hx)
  intro P he
  exact hfree P (congrArg (fun y : WindowFiber K q x => y.1.asIdeal) he)

/-- All window pairs, labelled by their witness index. -/
abbrev WindowPairs (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (x : Fin 5 → 𝓞 K)
    (hx : ∀ a, RingOfIntegers.mapRingHom ι.toRingHom (x a) = x a) :=
  Σ a : Fin 5, WindowPairIndex ι hι (Witness.primeNorm a) (x a) (hx a)

/-- The window pairs form a `PrimePairFamily`. -/
def windowPrimePairFamily (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (x : Fin 5 → 𝓞 K)
    (hx : ∀ a, RingOfIntegers.mapRingHom ι.toRingHom (x a) = x a) :
    PrimePairFamily ι (WindowPairs ι hι x hx) where
  prime s := (FreeInvolution.pair
    (conjugateWindow ι hι (Witness.primeNorm s.1.1) (x s.1.1) (hx s.1.1)) (s.1.2, s.2)).1
  partner s := rfl
  distinct := by
    rintro ⟨⟨a, y⟩, b⟩ ⟨⟨a', z⟩, c⟩ he
    have hn := congrArg Ideal.absNorm he
    have hna := (FreeInvolution.pair
      (conjugateWindow ι hι (Witness.primeNorm a) (x a) (hx a)) (y, b)).2.1
    have hnb := (FreeInvolution.pair
      (conjugateWindow ι hι (Witness.primeNorm a') (x a') (hx a')) (z, c)).2.1
    simp only at hn
    rw [hna, hnb] at hn
    have ha := Witness.primeNorm_injective hn
    subst a'
    have hp : FreeInvolution.pair (conjugateWindow ι hι (Witness.primeNorm a) (x a) (hx a)) (y, b) =
        FreeInvolution.pair (conjugateWindow ι hι (Witness.primeNorm a) (x a) (hx a)) (z, c) :=
      Subtype.ext (HeightOneSpectrum.ext he)
    have hyz := FreeInvolution.pair_injective _
      (conjugateWindow_involutive ι hι (Witness.primeNorm a) (x a) (hx a)) hp
    cases hyz
    rfl

theorem windowPrimePairFamily_norm (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (x : Fin 5 → 𝓞 K)
    (hx : ∀ a, RingOfIntegers.mapRingHom ι.toRingHom (x a) = x a) (s : WindowPairs ι hι x hx) :
    (Ideal.absNorm ((windowPrimePairFamily ι hι x hx).prime (s, false)).asIdeal : ℝ) =
      Witness.residueCard s.1 := by
  have h := (FreeInvolution.pair
    (conjugateWindow ι hι (Witness.primeNorm s.1) (x s.1) (hx s.1)) (s.2, false)).2.1
  change (Ideal.absNorm (FreeInvolution.pair
    (conjugateWindow ι hι (Witness.primeNorm s.1) (x s.1) (hx s.1)) (s.2, false)).1.asIdeal : ℝ) = _
  rw [h, Witness.primeNorm_cast]

/-- The label fiber is the set of representatives of that window. -/
def windowPairsFiberEquiv (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (x : Fin 5 → 𝓞 K)
    (hx : ∀ a, RingOfIntegers.mapRingHom ι.toRingHom (x a) = x a) (a : Fin 5) :
    {s : WindowPairs ι hι x hx // s.1 = a} ≃
      WindowPairIndex ι hι (Witness.primeNorm a) (x a) (hx a) where
  toFun s := s.2 ▸ s.1.2
  invFun y := ⟨⟨a, y⟩, rfl⟩
  left_inv s := by rcases s with ⟨⟨a', y⟩, h⟩; cases h; rfl
  right_inv y := rfl

theorem windowPrimePairFamily_multiplicity (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (x : Fin 5 → 𝓞 K)
    (hx : ∀ a, RingOfIntegers.mapRingHom ι.toRingHom (x a) = x a) (a : Fin 5)
    (hfree : ∀ P : WindowFiber K (Witness.primeNorm a) (x a),
      conjugateIdeal ι P.1.asIdeal ≠ P.1.asIdeal)
    (hcount : Nat.card (WindowFiber K (Witness.primeNorm a) (x a)) *
      (Witness.ramification a * Witness.residueDegree a) = Module.finrank ℚ K) :
    (Fintype.card {s : WindowPairs ι hι x hx // s.1 = a} : ℝ) *
      ((Witness.ramification a : ℝ) * Witness.residueDegree a) = Module.finrank ℚ F := by
  rw [Fintype.card_congr (windowPairsFiberEquiv ι hι x hx a)]
  have hpair := windowPairIndex_card_mul_two ι hι (Witness.primeNorm a) (x a) (hx a) hfree
  have hdegree : Module.finrank ℚ K = Module.finrank ℚ F * 2 := by
    rw [← Module.finrank_mul_finrank ℚ F K, Algebra.IsQuadraticExtension.finrank_eq_two F K]
  have h1 : (Fintype.card (WindowPairIndex ι hι (Witness.primeNorm a) (x a) (hx a)) : ℝ) * 2 =
      Nat.card (WindowFiber K (Witness.primeNorm a) (x a)) := by exact_mod_cast hpair
  have h2 : (Nat.card (WindowFiber K (Witness.primeNorm a) (x a)) : ℝ) *
      ((Witness.ramification a : ℝ) * Witness.residueDegree a) = Module.finrank ℚ K := by
    exact_mod_cast hcount
  have h3 : (Module.finrank ℚ K : ℝ) = Module.finrank ℚ F * 2 := by exact_mod_cast hdegree
  have h4 : ((Fintype.card (WindowPairIndex ι hι (Witness.primeNorm a) (x a) (hx a)) : ℝ) *
      ((Witness.ramification a : ℝ) * Witness.residueDegree a)) * 2 =
        (Module.finrank ℚ F : ℝ) * 2 := by
    rw [← h3, ← h2, ← h1]
    ring
  linarith

end Windows

/-! ### The planar target at `ε = 1/4411` -/

open UnitDistance.Sqrt241.SIntegerCRT in
/-- Version 1's `target_of_witnessFields_entire_fixedBase` with the fixed-base parameter
`ε = 1/4411`. -/
theorem target_of_witnessFields_entire_fixedBase_4411
    (hmargin : ∀ θ : ℝ, Witness.thetaMin ≤ θ →
      0 < Witness.margin θ - 4 * Witness.epsilon)
    (M : Type*) [Field M] [NumberField M]
    (Fs Ks : ℕ → Type) (Ss : ℕ → Type*)
    [∀ j, Field (Fs j)] [∀ j, Field (Ks j)]
    [∀ j, NumberField (Fs j)] [∀ j, NumberField (Ks j)]
    [∀ j, Algebra (Fs j) (Ks j)] [∀ j, Algebra M (Ks j)]
    [∀ j, Algebra.IsQuadraticExtension (Fs j) (Ks j)]
    [∀ j, IsTotallyComplex (Ks j)] [∀ j, Fintype (Ss j)]
    (ι : (j : ℕ) → Ks j ≃ₐ[Fs j] Ks j)
    (D : (j : ℕ) → PrimePairFamily (ι j) (Ss j)) (v : (j : ℕ) → Ss j → Fin 5)
    (hdegree : Tendsto (fun j => Module.finrank ℚ (Fs j)) atTop atTop)
    (hunr : ∀ᶠ j in atTop, FiniteUnramified (Fs j) (Ks j))
    (hι : ∀ᶠ j in atTop, ι j ≠ 1)
    (hb : ∀ᶠ j in atTop, 0 < nrRealPlaces (Fs j))
    (hQ : ∀ᶠ j in atTop, ∀ s,
      (Ideal.absNorm ((D j).prime (s, false)).asIdeal : ℝ) = Witness.residueCard (v j s))
    (hmultiplicity : ∀ᶠ j in atTop, ∀ a,
      (Fintype.card {s // v j s = a} : ℝ) *
        ((Witness.ramification a : ℝ) * Witness.residueDegree a) = Module.finrank ℚ (Fs j))
    (hdisc : ∀ᶠ j in atTop, Real.log (rootDiscriminant (Fs j)) ≤ Witness.logRD)
    (hentire : ∀ᶠ j in atTop, ∃ L : ℂ → ℂ, Differentiable ℂ L ∧
      ∀ z : ℂ, 1 < z.re →
        completedZetaRight (Ks j) z = completedZetaRight (Fs j) z * L z)
    (hfinite : fixedBaseResidueCeiling M Witness.logRD (1 / 4411) < Witness.ceiling)
    (hsignature : ∀ᶠ j in atTop, Witness.thetaMin ≤ signatureRatio (Fs j)) : Target := by
  have hquad : ∀ j, Module.finrank (Fs j) (Ks j) = 2 := fun j =>
    Algebra.IsQuadraticExtension.finrank_eq_two (Fs j) (Ks j)
  have hdegreeK : Tendsto (fun j => Module.finrank ℚ (Ks j)) atTop atTop := by
    apply tendsto_atTop_mono _ hdegree
    intro j
    have hd := Module.finrank_mul_finrank ℚ (Fs j) (Ks j)
    rw [hquad] at hd
    omega
  have hdiscK : ∀ᶠ j in atTop,
      Real.log (rootDiscriminant (Ks j)) ≤ Witness.logRD := by
    filter_upwards [hunr, hdisc] with j hu hd
    rwa [rootDiscriminant_eq_of_finiteUnramified (Fs j) (Ks j) hu]
  have hcomp : ∀ eta : ℝ, 0 < eta → ∀ᶠ j in atTop,
      relativeCompletedReal (Ks j) (Fs j) Witness.logRD 1 ≤
        relativeCompletedReal (Ks j) (Fs j) Witness.logRD (1 + eta) := by
    intro eta heta
    filter_upwards [hunr, hdisc, hentire] with j hu hd hL
    obtain ⟨L, hL, hfactor⟩ := hL
    exact relativeCompletedReal_monotoneOn_of_unramified_entire_factor
      (Ks j) (Fs j) (hquad j) hu hL hfactor hd
      (by simp) (by change 1 ≤ 1 + eta; linarith) (by linarith)
  let X : ℝ := fixedBaseResidueCeiling M Witness.logRD (1 / 4411)
  let U : ℝ := (X + Witness.ceiling) / 2
  have hXU : X < U := by dsimp only [X, U]; linarith
  have hUT : U < Witness.ceiling := by
    dsimp only [X, U] at hfinite ⊢
    linarith
  have hresidue := eventual_normalized_log_relativeResidue_lt_of_fixed_base
    M Ks Fs hquad hdegreeK
    (Eventually.of_forall fun j => IsTotallyComplex.nrRealPlaces_eq_zero (Ks j))
    (by norm_num : (0 : ℝ) < 1 / 4411) hdiscK hcomp hXU
  exact target_of_witnessFields_of_residueCap hmargin
    Fs Ks Ss ι D v hdegree hunr hι hb hQ hmultiplicity hdisc U
    (hresidue.mono fun _ h => h.le) hsignature hUT

/-- A square root of `-1` excludes every real place. -/
theorem isTotallyComplex_of_sqrt_neg_one {K : Type} [Field K] [NumberField K] (x : K)
    (hx : x ^ 2 = -1) : IsTotallyComplex K := by
  refine ⟨fun w => InfinitePlace.not_isReal_iff_isComplex.mp ?_⟩
  intro hw
  have hr : ComplexEmbedding.IsReal w.embedding := InfinitePlace.isReal_iff.mp hw
  have h1 : (w.embedding x) ^ 2 = -1 := by rw [← map_pow, hx, map_neg, map_one]
  have h2 : star (w.embedding x) = w.embedding x := RingHom.congr_fun hr x
  have h3 : (w.embedding x).im = 0 := by
    have := congrArg Complex.im h2
    simp only [Complex.star_def, Complex.conj_im] at this
    linarith
  have h4 : ((w.embedding x) ^ 2).re = ((w.embedding x).re) ^ 2 := by
    simp [sq, Complex.mul_re, h3]
  rw [h1] at h4
  simp at h4
  nlinarith [sq_nonneg (w.embedding x).re]

open UnitDistance.Sqrt241.QuadraticRoot in
/-- **Version 2 planar target** from the tower data, the root discriminant of `M` and the
fixed-base ceiling of `M` at `ε = 1/4411`. -/
theorem TowerData.target (T : TowerData)
    (hdiscM : Real.log (rootDiscriminant T.M) ≤ Witness.logRD)
    (hfinite : fixedBaseResidueCeiling T.M Witness.logRD (1 / 4411) < Witness.ceiling) :
    Target := by
  let Fs : ℕ → Type := fun j => GaloisConjugation.fixedField (T.Ks j) (T.c j)
  let : ∀ j, Algebra (Fs j) (T.Ks j) := fun _ => by
    dsimp only [Fs]
    infer_instance
  let : ∀ j, Algebra.IsQuadraticExtension (Fs j) (T.Ks j) := fun j =>
    quadratic (T.hc j) (T.hc1 j)
  have hi : ∀ j, (algebraMap T.M (T.Ks j) T.ii) ^ 2 = -1 := fun j => by
    rw [← map_pow, T.hii, map_neg, map_one]
  let : ∀ j, IsTotallyComplex (T.Ks j) := fun j => isTotallyComplex_of_sqrt_neg_one _ (hi j)
  let ι : ∀ j, T.Ks j ≃ₐ[Fs j] T.Ks j := fun j => fixedAut (T.c j)
  have hι : ∀ j, ι j ≠ 1 := fun j => fixedAut_ne_one (T.hc1 j)
  have hx : ∀ j a, RingOfIntegers.mapRingHom (ι j).toRingHom (T.window j a) = T.window j a :=
    fun j a => T.window_fixed j a
  let Ss : ℕ → Type := fun j => WindowPairs (ι j) (hι j) (T.window j) (hx j)
  let D : ∀ j, PrimePairFamily (ι j) (Ss j) := fun j =>
    windowPrimePairFamily (ι j) (hι j) (T.window j) (hx j)
  let v : ∀ j, Ss j → Fin 5 := fun _ s => s.1
  have hdegreeF : Tendsto (fun j => Module.finrank ℚ (Fs j)) atTop atTop := by
    have h := T.hdegree
    have he : ∀ j, Module.finrank ℚ (T.Ks j) = 2 * Module.finrank ℚ (Fs j) := fun j =>
      GaloisConjugation.absoluteDegree_eq_two_mul (T.φ j) (T.c j) (T.hc j) (T.hc1 j)
    rw [tendsto_atTop_atTop] at h ⊢
    intro b
    obtain ⟨i, hi⟩ := h (2 * b)
    exact ⟨i, fun j hj => by have := hi j hj; rw [he j] at this; omega⟩
  have h3 : ∀ j, (algebraMap T.M (T.Ks j) T.r3) ^ 2 = ((3 : ℕ) : T.Ks j) := fun j => by
    rw [← map_pow, T.hr3, map_ofNat]
    norm_num
  have hunr : ∀ j, FiniteUnramified (Fs j) (T.Ks j) := fun j =>
    ImaginaryRoot.finiteUnramified_of_real_place (Fs j) (T.Ks j)
      (fixedRoot (T.φ j) (T.c j) (T.hc j) (algebraMap T.M (T.Ks j) T.r3) (h3 j))
      (fixedRoot_sq (T.φ j) (T.c j) (T.hc j) (algebraMap T.M (T.Ks j) T.r3) (h3 j))
      (algebraMap T.M (T.Ks j) T.ii) (hi j)
      (GaloisConjugation.relativeDegree_eq_two (T.φ j) (T.c j) (T.hc j) (T.hc1 j))
      (GaloisConjugation.nrRealPlaces_pos (T.φ j) (T.c j) (T.hc j))
  have hb : ∀ j, 0 < nrRealPlaces (Fs j) := fun j =>
    GaloisConjugation.nrRealPlaces_pos (T.φ j) (T.c j) (T.hc j)
  have hQ : ∀ j s, (Ideal.absNorm ((D j).prime (s, false)).asIdeal : ℝ) =
      Witness.residueCard (v j s) := fun j s =>
    windowPrimePairFamily_norm (ι j) (hι j) (T.window j) (hx j) s
  have hmultiplicity : ∀ j a,
      (Fintype.card {s // v j s = a} : ℝ) *
        ((Witness.ramification a : ℝ) * Witness.residueDegree a) = Module.finrank ℚ (Fs j) :=
    fun j a => windowPrimePairFamily_multiplicity (ι j) (hι j) (T.window j) (hx j) a
      (fun P => T.window_free j a P) (T.window_count j a)
  have hdisc : ∀ j, Real.log (rootDiscriminant (Fs j)) ≤ Witness.logRD := fun j => by
    rw [← rootDiscriminant_eq_of_finiteUnramified (Fs j) (T.Ks j) (hunr j),
      rootDiscriminant_eq_of_finiteUnramified T.M (T.Ks j) (T.hunrM j)]
    exact hdiscM
  have hentire : ∀ j, ∃ L : ℂ → ℂ, Differentiable ℂ L ∧
      ∀ z : ℂ, 1 < z.re →
        completedZetaRight (T.Ks j) z = completedZetaRight (Fs j) z * L z := fun j => by
    obtain ⟨L, hL, hfactor⟩ :=
      NumberFieldAnalysis.exists_entire_relative_factor_of_imaginary_quadratic
        (Fs j) (T.Ks j)
        (fixedRoot (T.φ j) (T.c j) (T.hc j) (algebraMap T.M (T.Ks j) T.r3) (h3 j))
        (fixedRoot_sq (T.φ j) (T.c j) (T.hc j) (algebraMap T.M (T.Ks j) T.r3) (h3 j))
        (hb j) (algebraMap T.M (T.Ks j) T.ii) (hi j)
        (Algebra.IsQuadraticExtension.finrank_eq_two (Fs j) (T.Ks j)) (hunr j)
    exact ⟨L, hL, fun z hz =>
      rightHalfPlaneFactor_of_entireFactor (Fs j) (T.Ks j) hfactor hz⟩
  have hsignature : ∀ j, Witness.thetaMin ≤ signatureRatio (Fs j) := fun j =>
    thetaMin_le_signatureRatio (T.hc j) (T.hc1 j) (T.hcD j) T.hindexD
  have hmargin : ∀ θ : ℝ, Witness.thetaMin ≤ θ →
      0 < Witness.margin θ - 4 * Witness.epsilon := fun θ hθ =>
    lt_trans (by norm_num) (Witness.uniform_margin θ hθ)
  exact target_of_witnessFields_entire_fixedBase_4411 hmargin T.M Fs T.Ks Ss ι D v hdegreeF
    (Eventually.of_forall hunr) (Eventually.of_forall hι) (Eventually.of_forall hb)
    (Eventually.of_forall hQ) (Eventually.of_forall hmultiplicity)
    (Eventually.of_forall hdisc) (Eventually.of_forall hentire) hfinite
    (Eventually.of_forall hsignature)

end UnitDistance.Sqrt241.V2
