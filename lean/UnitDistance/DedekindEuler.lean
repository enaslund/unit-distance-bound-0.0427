/-
Copyright (c) 2026 Formal Frontier Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.Tactic
public import UnitDistance.RelativeZeta

@[expose] public section
set_option backward.privateInPublic true


/-!
# Dedekind ideal series and Euler-product foundations

Adapted from the ideal-series and Euler helper sections of
`DedekindZeta/Statements.lean`, sum_product commit
`80e4127a67742659d521466204c6d2d7e0ca2b3f` (Formal Frontier Team, Apache-2.0).
The license is retained in `third-party/sum_product/LICENSE`.

This port uses the proved summability in `RelativeZeta`, strengthens the
ideal-series statement to `HasSum`, and exposes the factorization helpers.
No theta-function or unproved completed-zeta assertion is imported.
Subsequent modifications are documented in `docs/NUMBER_FIELD_ANALYSIS.md`.
-/

open NumberField NumberField.InfinitePlace IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open Filter Finset Asymptotics Topology
open scoped Real nonZeroDivisors

namespace UnitDistance.DedekindEuler

variable (K : Type*) [Field K] [NumberField K]

noncomputable section

/-! ## Index sets -/

/-- The nonzero integral ideals of `𝓞 K`, as a subtype of `Ideal (𝓞 K)`. -/
abbrev NonzeroIdeal := {I : Ideal (𝓞 K) // I ≠ 0}


/-! ## The sum-over-ideals identity

For `Re s > 1`, Mathlib's `dedekindZeta` (the `LSeries` of
`n ↦ #{ideals of absNorm n}`) regroups into the sum over nonzero integral
ideals of `𝔑(𝔞)^{-s}`. -/
theorem dedekindZeta_hasSum_absNorm {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun 𝔞 : NonzeroIdeal K =>
      (Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℂ) ^ (-s))
      (NumberField.dedekindZeta K s) := by
  classical
  -- the ideal-counting coefficient
  set g : ℕ → ℂ := fun n ↦ (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ) with hg
  set φ : NonzeroIdeal K → ℕ := fun 𝔞 ↦ Ideal.absNorm (𝔞 : Ideal (𝓞 K)) with hφ
  set h : NonzeroIdeal K → ℂ := fun 𝔞 ↦ (φ 𝔞 : ℂ) ^ (-s) with hh
  set e := Equiv.sigmaFiberEquiv φ with he
  -- finiteness of fibres
  have hfin : ∀ n : ℕ, Finite {a : NonzeroIdeal K // φ a = n} := by
    intro n
    haveI : Finite {I : Ideal (𝓞 K) // Ideal.absNorm I = n} :=
      (Ideal.finite_setOf_absNorm_eq n).to_subtype
    apply Finite.of_injective
      (f := fun c : {a : NonzeroIdeal K // φ a = n} ↦
        (⟨(c.1 : Ideal (𝓞 K)), c.2⟩ : {I : Ideal (𝓞 K) // Ideal.absNorm I = n}))
    intro a b hab
    have : (a.1 : Ideal (𝓞 K)) = (b.1 : Ideal (𝓞 K)) := by
      simpa using congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext this)
  -- card of a fibre over nonzero ideals = card of all ideals of that norm (for n ≠ 0)
  have hcard : ∀ n : ℕ, n ≠ 0 →
      Nat.card {a : NonzeroIdeal K // φ a = n}
        = Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} := by
    intro n hn
    refine Nat.card_congr ?_
    refine
      { toFun := fun c ↦ ⟨(c.1 : Ideal (𝓞 K)), c.2⟩
        invFun := fun d ↦ ⟨⟨d.1, ?_⟩, d.2⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro hI0
      apply hn
      have : Ideal.absNorm d.1 = 0 := by rw [hI0]; simp
      rw [← d.2, this]
    · intro c; exact Subtype.ext (Subtype.ext rfl)
    · intro d; exact Subtype.ext rfl
  have hLS : LSeriesSummable g s :=
    NumberFieldAnalysis.dedekindZeta_summable K hs
  have hnorm : Summable (fun n : ℕ ↦ ‖LSeries.term g s n‖) := summable_norm_iff.mpr hLS
  -- constant tsum over a finite fibre
  have hconst : ∀ (n : ℕ), n ≠ 0 → ∀ z : ℂ,
      (∑' _y : {a : NonzeroIdeal K // φ a = n}, z)
        = (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} : ℂ) * z := by
    intro n hn z
    haveI := hfin n
    haveI : Fintype {a : NonzeroIdeal K // φ a = n} := Fintype.ofFinite _
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card, hcard n hn]
  -- the term-by-term identity
  have hterm : ∀ n : ℕ, (∑' y : {a : NonzeroIdeal K // φ a = n}, h (e ⟨n, y⟩))
      = LSeries.term g s n := by
    intro n
    by_cases hn : n = 0
    · subst hn
      haveI : IsEmpty {a : NonzeroIdeal K // φ a = 0} := by
        refine ⟨fun a ↦ ?_⟩
        have : Ideal.absNorm (a.1 : Ideal (𝓞 K)) = 0 := a.2
        exact a.1.2 ((Ideal.absNorm_eq_zero_iff).mp this)
      simp [tsum_empty, LSeries.term_zero]
    · have hval : ∀ y : {a : NonzeroIdeal K // φ a = n}, h (e ⟨n, y⟩) = (n : ℂ) ^ (-s) := by
        intro y
        have : e ⟨n, y⟩ = y.1 := rfl
        rw [this, hh]
        simp only
        rw [y.2]
      rw [tsum_congr hval, hconst n hn]
      rw [LSeries.term_of_ne_zero hn, hg]
      simp only
      rw [Complex.cpow_neg, div_eq_mul_inv]
  -- summability of h via the real majorant
  have hsumH : Summable h := by
    apply Summable.of_norm
    have hnormeq : ∀ 𝔞 : NonzeroIdeal K, ‖h 𝔞‖ = (φ 𝔞 : ℝ) ^ (-s.re) := by
      intro 𝔞
      have hpos : 0 < φ 𝔞 := by
        rw [hφ]; simp only
        exact Nat.pos_of_ne_zero (fun hz ↦ 𝔞.2 ((Ideal.absNorm_eq_zero_iff).mp hz))
      rw [hh]; simp only
      rw [Complex.norm_natCast_cpow_of_pos hpos, Complex.neg_re]
    rw [funext hnormeq]
    refine (Equiv.summable_iff e).mp ?_
    change Summable fun p : (Sigma fun n => {a : NonzeroIdeal K // φ a = n}) =>
      (φ (e p) : ℝ) ^ (-s.re)
    rw [summable_sigma_of_nonneg (fun p ↦ Real.rpow_nonneg (by positivity) _)]
    refine ⟨fun n ↦ ?_, ?_⟩
    · haveI := hfin n
      exact Summable.of_finite
    · refine hnorm.congr (fun n ↦ ?_)
      by_cases hn : n = 0
      · subst hn
        haveI : IsEmpty {a : NonzeroIdeal K // φ a = 0} := by
          refine ⟨fun a ↦ ?_⟩
          have : Ideal.absNorm (a.1 : Ideal (𝓞 K)) = 0 := a.2
          exact a.1.2 ((Ideal.absNorm_eq_zero_iff).mp this)
        simp [tsum_empty, LSeries.term_zero]
      · have hval : ∀ y : {a : NonzeroIdeal K // φ a = n},
            (fun p : (Sigma fun n => {a : NonzeroIdeal K // φ a = n}) =>
              (φ (e p) : ℝ) ^ (-s.re)) ⟨n, y⟩ = (n : ℝ) ^ (-s.re) := by
          intro y; simp only; rw [show e ⟨n, y⟩ = y.1 from rfl, y.2]
        rw [tsum_congr hval]
        haveI := hfin n
        haveI : Fintype {a : NonzeroIdeal K // φ a = n} := Fintype.ofFinite _
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ← Nat.card_eq_fintype_card, hcard n hn]
        rw [LSeries.norm_term_eq, if_neg hn, hg]
        simp only [Complex.norm_natCast, Real.rpow_neg (Nat.cast_nonneg _)]
        rw [div_eq_mul_inv]
  -- assemble
  have hsig : Summable (fun p : (Sigma fun n => {a : NonzeroIdeal K // φ a = n}) => h (e p)) :=
    (Equiv.summable_iff e).mpr hsumH
  have key : (∑' 𝔞 : NonzeroIdeal K, h 𝔞) = ∑' n, LSeries.term g s n := by
    rw [← Equiv.tsum_eq e h,
      hsig.tsum_sigma' (fun n => by haveI := hfin n; exact Summable.of_finite)]
    exact tsum_congr hterm
  rw [NumberField.dedekindZeta, LSeries, ← key]
  exact hsumH.hasSum

theorem dedekindZeta_eq_tsum_absNorm {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta K s =
      ∑' 𝔞 : NonzeroIdeal K, (Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℂ) ^ (-s) :=
  (dedekindZeta_hasSum_absNorm K hs).tsum_eq.symm

/-! ### Helper lemmas for the abstract geometric-series product identity

The theorem `hasProd_finsuppMonomial` is decomposed into three
self-contained analytic facts:

* `summable_norm_finsuppMonomial` — absolute summability of the monomials over
  finitely supported exponent vectors;
* `prod_geometric_eq_tsum_finsuppSupportedIn` — the finite-product expansion:
  the partial product over a finset `s` of the per-factor geometric series equals
  the sum of the monomials over exponent vectors supported in `s`;
* `hasProd_finsuppMonomial` — taking the limit over the directed family of
  finsets, the per-factor geometric series are multipliable with product equal to
  the sum over all exponent vectors.

The main theorem is then immediate from `hasProd_finsuppMonomial`. -/

open scoped NNReal ENNReal

/-- Finite-product distributivity in `ℝ≥0∞`: the sum, over exponent vectors
supported in a finite set `T`, of the monomials `∏_{i ∈ T} a i ^ f i`, factors as
the product over `T` of the per-factor geometric series. Proved by induction on
`T`; this is the engine behind `summable_norm_finsuppMonomial`. -/
theorem tsum_prod_finsuppSupported {ι : Type*} (a : ι → ℝ≥0∞) (T : Finset ι) :
    ∑' f : {f : ι →₀ ℕ // f.support ⊆ T}, ∏ i ∈ T, a i ^ ((f : ι →₀ ℕ) i)
      = ∏ i ∈ T, ∑' k : ℕ, a i ^ k := by
  classical
  induction T using Finset.induction with
  | empty =>
      have hsub : ∀ x : {f : ι →₀ ℕ // f.support ⊆ (∅ : Finset ι)},
          x = ⟨0, by simp⟩ := by
        rintro ⟨f, hf⟩
        simp only [Finset.subset_empty, Finsupp.support_eq_empty] at hf
        exact Subtype.ext hf
      rw [tsum_eq_single ⟨0, by simp⟩ (fun b hb => absurd (hsub b) hb)]
      simp
  | @insert j T' hj ih =>
      let e' : ℕ × {f : ι →₀ ℕ // f.support ⊆ T'} ≃
          {f : ι →₀ ℕ // f.support ⊆ insert j T'} :=
      { toFun := fun p => ⟨Finsupp.single j p.1 + (p.2 : ι →₀ ℕ), by
          intro i hi
          have hmem := Finsupp.support_add hi
          rw [Finset.mem_union] at hmem
          rcases hmem with h | h
          · exact Finset.mem_insert.mpr
              (Or.inl (Finset.mem_singleton.mp (Finsupp.support_single_subset h)))
          · exact Finset.mem_insert_of_mem (p.2.2 h)⟩
        invFun := fun f => (((f : ι →₀ ℕ) j),
          ⟨(f : ι →₀ ℕ).erase j, by
            intro i hi
            rw [Finsupp.support_erase, Finset.mem_erase] at hi
            have h2 := f.2 hi.2
            rw [Finset.mem_insert] at h2
            exact h2.resolve_left hi.1⟩)
        left_inv := by
          rintro ⟨k, f', hf'⟩
          have hj0 : f' j = 0 := by
            by_contra h
            exact hj (hf' (Finsupp.mem_support_iff.mpr h))
          have hje : Finsupp.erase j f' = f' :=
            Finsupp.erase_of_notMem_support (by simp [hj0])
          apply Prod.ext
          · simp [Finsupp.add_apply, hj0]
          · apply Subtype.ext
            simp only [Finsupp.erase_add, Finsupp.erase_single, zero_add, hje]
        right_inv := by
          rintro ⟨f, hf⟩
          apply Subtype.ext
          simp [Finsupp.single_add_erase] }
      have hterm : ∀ p : ℕ × {f : ι →₀ ℕ // f.support ⊆ T'},
          ∏ i ∈ insert j T', a i ^ ((e' p : ι →₀ ℕ) i)
            = a j ^ p.1 * ∏ i ∈ T', a i ^ ((p.2 : ι →₀ ℕ) i) := by
        rintro ⟨k, f', hf'⟩
        have hcoe : (e' (k, ⟨f', hf'⟩) : ι →₀ ℕ)
            = Finsupp.single j k + f' := rfl
        rw [hcoe, Finset.prod_insert hj]
        have hjval : (Finsupp.single j k + f') j = k := by
          have hj0 : f' j = 0 := by
            by_contra h
            exact hj (hf' (Finsupp.mem_support_iff.mpr h))
          simp [Finsupp.add_apply, hj0]
        rw [hjval]
        congr 1
        apply Finset.prod_congr rfl
        intro i hi
        have hij : i ≠ j := fun h => hj (h ▸ hi)
        have : (Finsupp.single j k + f') i = f' i := by
          rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hij), zero_add]
        rw [this]
      rw [Finset.prod_insert hj, ← ih, ← Equiv.tsum_eq e']
      simp_rw [hterm]
      rw [ENNReal.tsum_prod']
      simp_rw [ENNReal.tsum_mul_left]
      rw [ENNReal.tsum_mul_right]

/-- Absolute summability of the monomials
`∏ᶠ i, g i ^ f i` over finitely supported exponent vectors `f : ι →₀ ℕ`, for a
complex family with `‖g i‖ < 1` for all `i` and `Summable (‖g ·‖)`. -/
theorem summable_norm_finsuppMonomial {ι : Type*} {g : ι → ℂ}
    (hg : ∀ i, ‖g i‖ < 1) (hsum : Summable fun i ↦ ‖g i‖) :
    Summable fun f : ι →₀ ℕ ↦ ‖∏ᶠ i, g i ^ f i‖ := by
  classical
  set r : ι → ℝ := fun i => ‖g i‖ with hr
  have hr01 : ∀ i, r i < 1 := hg
  have hr0 : ∀ i, 0 ≤ r i := fun i => norm_nonneg _
  -- Multipliability in `ℝ` of the per-factor geometric values `(1 - r i)⁻¹`.
  have hb : Summable (fun i => r i * (1 - r i)⁻¹) := by
    refine Summable.mul_tendsto_const (c := (1 : ℝ)) (by simpa only [hr, norm_norm] using hsum) ?_
    have h0 : Tendsto r cofinite (𝓝 0) := by
      simpa only [hr] using hsum.tendsto_cofinite_zero
    have h1 : Tendsto (fun i => 1 - r i) cofinite (𝓝 (1 - 0)) := tendsto_const_nhds.sub h0
    simpa using h1.inv₀ (by norm_num)
  -- Summability of the logarithms of the geometric values.
  have hL : Summable (fun i => Real.log ((1 - r i)⁻¹)) := by
    refine (Real.summable_log_one_add_of_summable hb).congr (fun i => ?_)
    have hne : (1 : ℝ) - r i ≠ 0 := by have := hr01 i; linarith
    rw [show 1 + r i * (1 - r i)⁻¹ = (1 - r i)⁻¹ by field_simp; ring]
  have hLnonneg : ∀ i, 0 ≤ Real.log ((1 - r i)⁻¹) := by
    intro i
    have hpos : (0 : ℝ) < 1 - r i := by have := hr01 i; linarith
    have : (1 : ℝ) ≤ (1 - r i)⁻¹ := (one_le_inv₀ hpos).mpr (by have := hr0 i; linarith)
    exact Real.log_nonneg this
  set C : ℝ := Real.exp (∑' i, Real.log ((1 - r i)⁻¹)) with hC
  -- It suffices to show summability of the `ℝ≥0`-valued norms.
  have hsummN : Summable (fun f : ι →₀ ℕ => (‖∏ᶠ i, g i ^ f i‖₊ : ℝ≥0)) := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable]
    set a : ι → ℝ≥0∞ := fun i => (‖g i‖₊ : ℝ≥0∞) with ha
    have hcoe : ∀ f : ι →₀ ℕ,
        ((‖∏ᶠ i, g i ^ f i‖₊ : ℝ≥0) : ℝ≥0∞) = ∏ i ∈ f.support, a i ^ f i := by
      intro f
      have hms : Function.mulSupport (fun i => g i ^ f i) ⊆ ↑f.support := by
        intro i hi
        simp only [Function.mem_mulSupport] at hi
        rw [Finset.mem_coe, Finsupp.mem_support_iff]
        intro hf0
        exact hi (by rw [hf0, pow_zero])
      rw [finprod_eq_prod_of_mulSupport_subset _ hms, nnnorm_prod, ENNReal.ofNNReal_finsetProd]
      apply Finset.prod_congr rfl
      intro i _
      rw [nnnorm_pow, ENNReal.coe_pow]
    simp only [hcoe]
    -- The factor norms in `ℝ≥0∞`.
    have hfac : ∀ i, (1 - a i)⁻¹ = ENNReal.ofReal ((1 - r i)⁻¹) := by
      intro i
      have hai : a i = ENNReal.ofReal (r i) := by
        simp only [ha, hr, ← coe_nnnorm, ENNReal.ofReal_coe_nnreal]
      rw [hai, show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp,
        ← ENNReal.ofReal_sub 1 (hr0 i),
        ENNReal.ofReal_inv_of_pos (by have := hr01 i; linarith)]
    have hle : ∑' f : ι →₀ ℕ, ∏ i ∈ f.support, a i ^ f i ≤ ENNReal.ofReal C := by
      rw [ENNReal.tsum_eq_iSup_sum]
      refine iSup_le (fun s => ?_)
      set T : Finset ι := s.biUnion (fun f => f.support) with hT
      have hsubT : ∀ f ∈ s, f.support ⊆ T :=
        fun f hf => Finset.subset_biUnion_of_mem (fun f => f.support) hf
      have hstep : ∑ f ∈ s, ∏ i ∈ f.support, a i ^ f i
          = ∑ f ∈ s, ∏ i ∈ T, a i ^ f i := by
        refine Finset.sum_congr rfl (fun f hf => ?_)
        refine Finset.prod_subset (hsubT f hf) (fun i _ hi => ?_)
        rw [Finsupp.notMem_support_iff.mp hi, pow_zero]
      rw [hstep]
      have hfilter : ∑ x ∈ s.subtype (fun fn : ι →₀ ℕ => fn.support ⊆ T),
            ∏ i ∈ T, a i ^ ((x : ι →₀ ℕ) i)
          = ∑ f ∈ s, ∏ i ∈ T, a i ^ f i :=
        Finset.sum_subtype_of_mem (fun fn : ι →₀ ℕ => ∏ i ∈ T, a i ^ fn i) hsubT
      calc ∑ f ∈ s, ∏ i ∈ T, a i ^ f i
            = ∑ x ∈ s.subtype (fun fn : ι →₀ ℕ => fn.support ⊆ T),
                ∏ i ∈ T, a i ^ ((x : ι →₀ ℕ) i) := hfilter.symm
        _ ≤ ∑' x : {f : ι →₀ ℕ // f.support ⊆ T}, ∏ i ∈ T, a i ^ ((x : ι →₀ ℕ) i) :=
              ENNReal.sum_le_tsum _
        _ = ∏ i ∈ T, ∑' k : ℕ, a i ^ k := tsum_prod_finsuppSupported a T
        _ = ∏ i ∈ T, (1 - a i)⁻¹ := by
              simp_rw [ENNReal.tsum_geometric]
        _ = ∏ i ∈ T, ENNReal.ofReal ((1 - r i)⁻¹) := Finset.prod_congr rfl (fun i _ => hfac i)
        _ = ENNReal.ofReal (∏ i ∈ T, (1 - r i)⁻¹) :=
              (ENNReal.ofReal_prod_of_nonneg (fun i _ => by
                have hpos : (0 : ℝ) < 1 - r i := by have := hr01 i; linarith
                positivity)).symm
        _ ≤ ENNReal.ofReal C := by
              refine ENNReal.ofReal_le_ofReal ?_
              have hprodlog : ∏ i ∈ T, (1 - r i)⁻¹
                  = Real.exp (∑ i ∈ T, Real.log ((1 - r i)⁻¹)) := by
                rw [Real.exp_sum]
                refine Finset.prod_congr rfl (fun i _ => ?_)
                have hpos : (0 : ℝ) < 1 - r i := by have := hr01 i; linarith
                exact (Real.exp_log (by positivity)).symm
              rw [hprodlog, hC]
              exact Real.exp_le_exp.mpr (hL.sum_le_tsum T (fun i _ => hLnonneg i))
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  simpa only [coe_nnnorm] using NNReal.summable_coe.mpr hsummN

/-- Finite-product expansion. For a finset `s`, the partial
product of the per-factor geometric series `(1 - g i)⁻¹ = ∑' k, g i ^ k` equals
the sum of the monomials over the exponent vectors supported in `s`. -/
theorem prod_geometric_eq_tsum_finsuppSupportedIn {ι : Type*} {g : ι → ℂ}
    (hg : ∀ i, ‖g i‖ < 1) (hsum : Summable fun i ↦ ‖g i‖) (s : Finset ι) :
    ∏ i ∈ s, (1 - g i)⁻¹ =
      ∑' f : {f : ι →₀ ℕ // f.support ⊆ s}, ∏ᶠ i, g i ^ ((f : ι →₀ ℕ) i) := by
  classical
  -- Each monomial is supported on the (finite) support of its exponent vector.
  have hmulsupp : ∀ (h : ι →₀ ℕ) (S : Finset ι), h.support ⊆ S →
      Function.mulSupport (fun i ↦ g i ^ h i) ⊆ (S : Set ι) := by
    intro h S hS i hi
    simp only [Function.mem_mulSupport] at hi
    have : i ∈ h.support := by
      rw [Finsupp.mem_support_iff]
      intro h0
      exact hi (by rw [h0, pow_zero])
    exact_mod_cast hS this
  -- The monomial as a finite product over the support.
  have hmono : ∀ h : ι →₀ ℕ, (∏ᶠ i, g i ^ h i) = ∏ i ∈ h.support, g i ^ h i := by
    intro h
    exact finprod_eq_prod_of_mulSupport_subset _ (hmulsupp h h.support (Finset.Subset.refl _))
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty]
    have he : (∑' f : {f : ι →₀ ℕ // f.support ⊆ (∅ : Finset ι)},
          ∏ᶠ i, g i ^ ((f : ι →₀ ℕ) i))
        = ∏ᶠ i, g i ^ ((⟨0, by simp⟩ :
            {f : ι →₀ ℕ // f.support ⊆ (∅ : Finset ι)}) : ι →₀ ℕ) i := by
      apply tsum_eq_single
      intro b hb
      exact absurd
        (Subtype.ext (Finsupp.support_eq_empty.1 (Finset.subset_empty.1 b.2))) hb
    rw [he]
    simp
  | @insert a s ha ih =>
    -- Absolute summability facts needed to multiply the two series.
    have hga : Summable fun k : ℕ ↦ ‖g a ^ k‖ := by
      simp_rw [norm_pow]
      exact summable_geometric_of_norm_lt_one
        (by rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact hg a)
    have hMs : Summable fun f : {f : ι →₀ ℕ // f.support ⊆ s} ↦
        ‖∏ᶠ i, g i ^ ((f : ι →₀ ℕ) i)‖ :=
      (summable_norm_finsuppMonomial hg hsum).subtype _
    -- Splitting off the `a`-factor of a monomial.
    have key : ∀ (k : ℕ) (f : ι →₀ ℕ), f.support ⊆ s →
        (∏ᶠ i, g i ^ ((f + Finsupp.single a k) i))
          = g a ^ k * ∏ᶠ i, g i ^ (f i) := by
      intro k f hf
      have ha' : a ∉ f.support := fun h ↦ ha (hf h)
      have hfa : f a = 0 := Finsupp.notMem_support_iff.1 ha'
      have hsub : (f + Finsupp.single a k).support ⊆ insert a f.support := by
        intro i hi
        rcases Finset.mem_union.1 (Finsupp.support_add hi) with h1 | h1
        · exact Finset.mem_insert_of_mem h1
        · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset h1)]
          exact Finset.mem_insert_self _ _
      rw [finprod_eq_prod_of_mulSupport_subset _
            (hmulsupp _ _ hsub), hmono f]
      rw [Finset.prod_insert ha']
      have hxa : (f + Finsupp.single a k) a = k := by
        rw [Finsupp.add_apply, hfa, Finsupp.single_eq_same, zero_add]
      rw [hxa]
      congr 1
      refine Finset.prod_congr rfl ?_
      intro i hi
      have hne : i ≠ a := fun h ↦ ha' (h ▸ hi)
      rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hne, add_zero]
    -- The reindexing equivalence `ℕ × {supp ⊆ s} ≃ {supp ⊆ insert a s}`.
    let e : ℕ × {f : ι →₀ ℕ // f.support ⊆ s} ≃
        {f : ι →₀ ℕ // f.support ⊆ insert a s} :=
      { toFun := fun p ↦ ⟨p.2.1 + Finsupp.single a p.1, by
          intro i hi
          rcases Finset.mem_union.1 (Finsupp.support_add hi) with h1 | h1
          · exact Finset.mem_insert_of_mem (p.2.2 h1)
          · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset h1)]
            exact Finset.mem_insert_self _ _⟩
        invFun := fun h ↦ (h.1 a, ⟨h.1.erase a, by
          intro i hi
          rw [Finsupp.support_erase] at hi
          have hmem := Finset.mem_of_mem_erase hi
          have hne := Finset.ne_of_mem_erase hi
          rcases Finset.mem_insert.1 (h.2 hmem) with h1 | h1
          · exact absurd h1 hne
          · exact h1⟩)
        left_inv := by
          rintro ⟨k, f, hf⟩
          have hfa : f a = 0 := Finsupp.notMem_support_iff.1 (fun h ↦ ha (hf h))
          have e1 : (f + Finsupp.single a k) a = k := by
            rw [Finsupp.add_apply, hfa, Finsupp.single_eq_same, zero_add]
          have e2 : Finsupp.erase a (f + Finsupp.single a k) = f := by
            ext i
            by_cases h : i = a
            · subst h
              rw [Finsupp.erase_same, hfa]
            · rw [Finsupp.erase_ne h, Finsupp.add_apply,
                Finsupp.single_eq_of_ne h, add_zero]
          rw [Prod.ext_iff]
          exact ⟨e1, Subtype.ext e2⟩
        right_inv := by
          rintro ⟨h, hh⟩
          apply Subtype.ext
          ext i
          by_cases hi : i = a
          · subst hi
            rw [Finsupp.add_apply, Finsupp.erase_same, Finsupp.single_eq_same, zero_add]
          · rw [Finsupp.add_apply, Finsupp.erase_ne hi,
              Finsupp.single_eq_of_ne hi, add_zero] }
    rw [Finset.prod_insert ha, ← tsum_geometric_of_norm_lt_one (hg a), ih,
      tsum_mul_tsum_of_summable_norm hga hMs,
      ← Equiv.tsum_eq e (fun w ↦ ∏ᶠ i, g i ^ ((w : ι →₀ ℕ) i))]
    refine tsum_congr ?_
    rintro ⟨k, f, hf⟩
    exact (key k f hf).symm

/-- The per-factor geometric series are multipliable with
product equal to the sum of the monomials over all exponent vectors. This is the
limit over the directed family of finsets of
`prod_geometric_eq_tsum_finsuppSupportedIn`, controlled by the absolute
summability `summable_norm_finsuppMonomial`. -/
theorem hasProd_finsuppMonomial {ι : Type*} {g : ι → ℂ}
    (hg : ∀ i, ‖g i‖ < 1) (hsum : Summable fun i ↦ ‖g i‖) :
    HasProd (fun i ↦ (1 - g i)⁻¹) (∑' f : ι →₀ ℕ, ∏ᶠ i, g i ^ f i) := by
  classical
  set M : (ι →₀ ℕ) → ℂ := fun f ↦ ∏ᶠ i, g i ^ f i with hMdef
  have hu : Summable fun f ↦ ‖M f‖ := summable_norm_finsuppMonomial hg hsum
  have hMsum : Summable M := hu.of_norm
  set T : ℂ := ∑' f : ι →₀ ℕ, M f with hT
  rw [HasProd, SummationFilter.unconditional, Metric.tendsto_atTop]
  intro ε hε
  -- The tail of the absolutely convergent norm series vanishes as the finset grows.
  have htail : Tendsto (fun A : Finset (ι →₀ ℕ) ↦ ∑' f : {x // x ∉ A}, ‖M f‖)
      atTop (𝓝 0) := tendsto_tsum_compl_atTop_zero (fun f ↦ ‖M f‖)
  obtain ⟨A, hA⟩ := (Metric.tendsto_atTop.mp htail) ε hε
  -- All indices appearing in the support of some `f ∈ A`.
  refine ⟨A.biUnion (fun f ↦ f.support), fun s hs ↦ ?_⟩
  set Sset : Set (ι →₀ ℕ) := {f | f.support ⊆ s} with hSset
  -- Partial product over `s` is the sum of the monomials supported in `s`.
  have hpart : ∏ i ∈ s, (1 - g i)⁻¹ = ∑' f : Sset, M f :=
    prod_geometric_eq_tsum_finsuppSupportedIn hg hsum s
  -- Splitting the full sum into supported-in-`s` and the rest.
  have hdecomp : (∑' f : Sset, M f) + (∑' f : ↥Ssetᶜ, M f) = T := by
    rw [hT]; exact hMsum.tsum_subtype_add_tsum_subtype_compl Sset
  rw [dist_eq_norm, hpart]
  have heq : (∑' f : Sset, M f) - T = -(∑' f : ↥Ssetᶜ, M f) := by
    rw [← hdecomp]; ring
  rw [heq, norm_neg]
  -- Exponent vectors not supported in `s` were not in `A`.
  have hsub : Ssetᶜ ⊆ {x | x ∉ A} := by
    intro f hf hfA
    exact hf (fun i hi ↦ hs (Finset.mem_biUnion.mpr ⟨f, hfA, hi⟩))
  have hbound : (∑' f : ↥Ssetᶜ, ‖M f‖) ≤ ∑' f : {x // x ∉ A}, ‖M f‖ := by
    exact Summable.tsum_le_tsum_of_inj (Set.inclusion hsub) (Set.inclusion_injective hsub)
      (fun _ _ ↦ norm_nonneg _) (fun _ ↦ le_rfl) (hu.subtype _) (hu.subtype _)
  have hltε : (∑' f : {x // x ∉ A}, ‖M f‖) < ε := by
    have h := hA A le_rfl
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (tsum_nonneg fun _ ↦ norm_nonneg _)] at h
  calc ‖∑' f : ↥Ssetᶜ, M f‖
      ≤ ∑' f : ↥Ssetᶜ, ‖M f‖ := norm_tsum_le_tsum_norm (hu.subtype _)
    _ ≤ ∑' f : {x // x ∉ A}, ‖M f‖ := hbound
    _ < ε := hltε


section ReIndex

/-- The `v`-adic exponent in the factorization of a nonzero ideal `I`, packaged
as a natural number via `IsDedekindDomain.HeightOneSpectrum.count`. -/
noncomputable def idealExp (I : Ideal (𝓞 K)) (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  (FractionalIdeal.count K v (I : FractionalIdeal (𝓞 K)⁰ K)).toNat

lemma idealExp_eq {I : Ideal (𝓞 K)} (hI : I ≠ 0) (v : HeightOneSpectrum (𝓞 K)) :
    idealExp K I v = (Associates.mk v.asIdeal).count (Associates.mk I).factors := by
  rw [idealExp, FractionalIdeal.count_coe K v hI, Int.toNat_natCast]

lemma idealExp_ne_zero_iff {I : Ideal (𝓞 K)} (hI : I ≠ 0)
    (v : HeightOneSpectrum (𝓞 K)) : idealExp K I v ≠ 0 ↔ v.asIdeal ∣ I := by
  rw [idealExp_eq K hI, Associates.count_ne_zero_iff_dvd hI v.irreducible]

lemma finite_idealExp_support {I : Ideal (𝓞 K)} (hI : I ≠ 0) :
    {v : HeightOneSpectrum (𝓞 K) | idealExp K I v ≠ 0}.Finite := by
  apply (Ideal.finite_factors hI).subset
  intro v hv
  exact (idealExp_ne_zero_iff K hI v).mp hv

lemma finprod_asIdeal_pow_idealExp {I : Ideal (𝓞 K)} (hI : I ≠ 0) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 K), v.asIdeal ^ idealExp K I v = I := by
  conv_rhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI]
  refine finprod_congr (fun v => ?_)
  rw [IsDedekindDomain.HeightOneSpectrum.maxPowDividing, idealExp_eq K hI]

/-- The factorization bijection between nonzero ideals and finitely supported
exponent vectors on the height-one spectrum. -/
noncomputable def nonzeroIdealEquivFinsupp :
    NonzeroIdeal K ≃ (HeightOneSpectrum (𝓞 K) →₀ ℕ) where
  toFun I :=
    { support := (finite_idealExp_support K I.2).toFinset
      toFun := idealExp K I.1
      mem_support_toFun := fun v => by rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq] }
  invFun f := ⟨f.prod (fun v n => v.asIdeal ^ n), by
    rw [Finsupp.prod, Ne, Finset.prod_eq_zero_iff]
    rintro ⟨v, -, hv⟩
    exact pow_ne_zero _ (by simpa [Ideal.zero_eq_bot] using v.ne_bot) hv⟩
  left_inv := by
    rintro ⟨I, hI⟩
    apply Subtype.ext
    change (Finsupp.mk _ (idealExp K I) _).prod (fun v n => v.asIdeal ^ n) = I
    rw [Finsupp.prod]
    simp only [Finsupp.coe_mk]
    rw [← finprod_eq_prod_of_mulSupport_subset (fun v => v.asIdeal ^ idealExp K I v) ?_]
    · exact finprod_asIdeal_pow_idealExp K hI
    · intro v hv
      simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq,
        Function.mem_mulSupport] at *
      intro h
      exact hv (by rw [h, pow_zero])
  right_inv := by
    intro f
    ext v
    change idealExp K (f.prod (fun v n => v.asIdeal ^ n)) v = f v
    have hJ : f.prod (fun v n => v.asIdeal ^ n) ≠ 0 := by
      rw [Finsupp.prod, Ne, Finset.prod_eq_zero_iff]
      rintro ⟨w, -, hw⟩
      exact pow_ne_zero _ (by simpa [Ideal.zero_eq_bot] using w.ne_bot) hw
    rw [idealExp, ← Int.toNat_natCast (f v)]
    congr 1
    classical
    have hcoe : ((f.prod (fun v n => v.asIdeal ^ n) : Ideal (𝓞 K)) :
        FractionalIdeal (𝓞 K)⁰ K)
        = ∏ w ∈ f.support, ((w.asIdeal : FractionalIdeal (𝓞 K)⁰ K)) ^ (f w) := by
      rw [Finsupp.prod, ← FractionalIdeal.coeIdealHom_apply, map_prod]
      refine Finset.prod_congr rfl (fun w _ => ?_)
      rw [FractionalIdeal.coeIdealHom_apply, FractionalIdeal.coeIdeal_pow]
    rw [hcoe, FractionalIdeal.count_prod K v]
    · simp only [FractionalIdeal.count_pow, FractionalIdeal.count_maximal]
      rw [Finset.sum_congr rfl (fun w _ => by rw [mul_ite, mul_one, mul_zero])]
      rw [Finset.sum_ite_eq' f.support v]
      split_ifs with h
      · simp
      · simp only [Finsupp.mem_support_iff, not_not] at h
        simp [h]
    · exact fun w _ => pow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot)

/-- The complex monoid hom `n ↦ (n : ℂ) ^ (-s)` on `(ℕ, *)`. -/
noncomputable def cpowHom (s : ℂ) : ℕ →* ℂ where
  toFun n := (n : ℂ) ^ (-s)
  map_one' := by simp
  map_mul' m n := by
    push_cast
    rw [Complex.natCast_mul_natCast_cpow]

lemma absNorm_cpow_eq_finprod {I : Ideal (𝓞 K)} (hI : I ≠ 0) (s : ℂ) :
    (Ideal.absNorm I : ℂ) ^ (-s)
      = ∏ᶠ v : HeightOneSpectrum (𝓞 K),
          ((Ideal.absNorm v.asIdeal : ℂ) ^ (-s)) ^ idealExp K I v := by
  have hfin : Function.HasFiniteMulSupport (fun v : HeightOneSpectrum (𝓞 K) =>
      v.asIdeal ^ idealExp K I v) := by
    apply (finite_idealExp_support K hI).subset
    intro v hv
    simp only [Function.mem_mulSupport] at hv
    intro h
    exact hv (by rw [h, pow_zero])
  have hfin2 : Function.HasFiniteMulSupport (fun v : HeightOneSpectrum (𝓞 K) =>
      (Ideal.absNorm v.asIdeal) ^ idealExp K I v) := by
    apply (finite_idealExp_support K hI).subset
    intro v hv
    simp only [Function.mem_mulSupport] at hv
    intro h
    exact hv (by rw [h, pow_zero])
  have hN : Ideal.absNorm I
      = ∏ᶠ v : HeightOneSpectrum (𝓞 K), (Ideal.absNorm v.asIdeal) ^ idealExp K I v := by
    conv_lhs => rw [← finprod_asIdeal_pow_idealExp K hI]
    rw [map_finprod Ideal.absNorm hfin]
    refine finprod_congr (fun v => ?_)
    rw [map_pow]
  rw [show (Ideal.absNorm I : ℂ) ^ (-s) = cpowHom s (Ideal.absNorm I) from rfl, hN,
    map_finprod (cpowHom s) hfin2]
  refine finprod_congr (fun v => ?_)
  rw [map_pow]
  rfl

end ReIndex



set_option maxHeartbeats 800000 in
/-- The actual Euler product over all nonzero prime ideals. This assembles the
proved ideal-series identity and factorization bijection above; there is no
Euler-product hypothesis. -/
theorem dedekindZeta_eulerProduct {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun v : HeightOneSpectrum (𝓞 K) =>
      (1 - (Ideal.absNorm v.asIdeal : ℂ) ^ (-s))⁻¹)
      (NumberField.dedekindZeta K s) := by
  let g : HeightOneSpectrum (𝓞 K) → ℂ :=
    fun v => (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)
  have hinj : Function.Injective (fun v : HeightOneSpectrum (𝓞 K) =>
      (⟨v.asIdeal, v.ne_bot⟩ : NonzeroIdeal K)) := by
    intro v w h
    exact HeightOneSpectrum.ext (congrArg Subtype.val h)
  have hall : Summable (fun I : NonzeroIdeal K =>
      ‖(Ideal.absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s)‖) := by
    exact (dedekindZeta_hasSum_absNorm K hs).summable.norm
  have hsum : Summable fun v => ‖g v‖ := by
    have hcomp := hall.comp_injective (i := fun v : HeightOneSpectrum (𝓞 K) =>
      (⟨v.asIdeal, v.ne_bot⟩ : NonzeroIdeal K)) hinj
    exact hcomp
  have hg : ∀ v, ‖g v‖ < 1 := by
    intro v
    have hn0 : 0 < Ideal.absNorm v.asIdeal :=
      Nat.pos_of_ne_zero (fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h))
    have hn1 : 1 < Ideal.absNorm v.asIdeal := by
      have hne : Ideal.absNorm v.asIdeal ≠ 1 :=
        fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
      omega
    rw [show g v = (Ideal.absNorm v.asIdeal : ℂ) ^ (-s) from rfl,
      Complex.norm_natCast_cpow_of_pos hn0, Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hn1) (by linarith)
  have heq : (∑' f : HeightOneSpectrum (𝓞 K) →₀ ℕ, ∏ᶠ v, g v ^ f v) =
      NumberField.dedekindZeta K s := by
    rw [← Equiv.tsum_eq (nonzeroIdealEquivFinsupp K) (fun f => ∏ᶠ v, g v ^ f v),
      dedekindZeta_eq_tsum_absNorm K hs]
    apply tsum_congr
    intro I
    exact (absNorm_cpow_eq_finprod K I.2 s).symm
  exact heq ▸ hasProd_finsuppMonomial hg hsum

end
end UnitDistance.DedekindEuler
