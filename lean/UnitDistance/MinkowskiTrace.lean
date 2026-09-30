/-
Copyright (c) 2026 Formal Frontier Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Adapted by the GPT-6 Astra formalization run for Eric Naslund's manuscript.
Source: mathlib-initiative/sum_product, commit
80e4127a67742659d521466204c6d2d7e0ca2b3f,
DedekindZeta/Theta.lean. See third-party/sum_product/LICENSE.
-/
module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.Tactic

@[expose] public section
set_option backward.privateInPublic true


/-!
# The actual number-field trace dual in mixed archimedean space

The trace form counts each complex place twice. This is an algebraic trace
identity, not a change to the ordinary Euclidean metric used for planar sets.
Every mixed-space point integral against a nonzero ideal is proved to be the
embedding of an element of its actual inverse-different dual ideal. This
includes the rationality step for arbitrary real mixed-space points.
-/

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical
namespace UnitDistance.MinkowskiTrace
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

/-- The (inverse) different as a fractional ideal: `𝔡 = differentIdeal ℤ 𝓞_K`,
viewed in `FractionalIdeal (𝓞 K)⁰ K`. -/
abbrev differentFractionalIdeal : FractionalIdeal (𝓞 K)⁰ K :=
  (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)

/-- The fractional ideal `(𝔞𝔡)⁻¹` whose lattice `Λ((𝔞𝔡)⁻¹)` is dual to
`Λ(𝔞)` in `K_ℝ` (the standard treatment): the dual of the lattice of `𝔞` is
the lattice of `(𝔞𝔡)⁻¹`, where `𝔡` is the different. -/
def dualIdeal (𝔞 : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K :=
  ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) * differentFractionalIdeal K)⁻¹

/-- The `dualIdeal` is exactly Mathlib's trace-form dual fractional ideal
`FractionalIdeal.dual ℤ ℚ 𝔞` (the standard treatment: the trace dual of `𝔞` is
`(𝔞𝔡)⁻¹`, with `𝔡` the different). -/
theorem dualIdeal_eq_dual (𝔞 : Ideal (𝓞 K)) :
    FractionalIdeal.dual ℤ ℚ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) = dualIdeal K 𝔞 := by
  have hd1 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)
      = (differentFractionalIdeal K)⁻¹ := by
    have h := coeIdeal_differentIdeal (A := ℤ) (K := ℚ) (L := K) (B := 𝓞 K)
    rw [differentFractionalIdeal, h, inv_inv]
  rw [FractionalIdeal.dual_eq_mul_inv, hd1, dualIdeal, mul_inv, mul_comm]

/-- The symmetric trace pairing, including its exact complex-place multiplicity. -/
def traceForm (ξ : mixedSpace K) (a : K) : ℝ :=
  (∑ w : {w : InfinitePlace K // w.IsReal}, ξ.1 w * (mixedEmbedding K a).1 w) +
  2 * ∑ w : {w : InfinitePlace K // w.IsComplex},
      (ξ.2 w * (mixedEmbedding K a).2 w).re

/-- The sum over all complex embeddings `∑_{σ : K →+* ℂ} σ b · σ a` equals the
image of the `ℚ`-trace `Tr_{K/ℚ}(b·a)` under `algebraMap ℚ ℂ`
(`trace_eq_sum_embeddings`, reindexed from `K →ₐ[ℚ] ℂ` to `K →+* ℂ`). -/
theorem sum_embeddings_mul (b a : K) :
    (∑ σ : K →+* ℂ, σ b * σ a) = algebraMap ℚ ℂ (Algebra.trace ℚ K (b * a)) := by
  have hmul : ∀ σ : K →+* ℂ, σ b * σ a = σ (b * a) := fun σ => (map_mul σ b a).symm
  simp_rw [hmul]
  rw [trace_eq_sum_embeddings (E := ℂ)]
  exact Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun σ : K →+* ℂ => σ (b * a))
    (fun φ : K →ₐ[ℚ] ℂ => φ (b * a)) (fun σ => rfl)

/-- **Defining property of `T`**: on canonical-embedding images the trace form
is the `ℚ`-trace, `T(mixedEmbedding K b, a) = (algebraMap ℚ ℝ)(Tr_{K/ℚ}(b·a))`
(the standard treatment). -/
theorem traceForm_mixedEmbedding (b a : K) :
    traceForm K (mixedEmbedding K b) a
      = algebraMap ℚ ℝ (Algebra.trace ℚ K (b * a)) := by
  classical
  -- The `mk`-fiber over a place `w` is the conjugate pair (singleton when real).
  have hfib : ∀ w : InfinitePlace K,
      (Finset.univ.filter fun σ : K →+* ℂ => InfinitePlace.mk σ = w)
        = {InfinitePlace.embedding w,
            ComplexEmbedding.conjugate (InfinitePlace.embedding w)} := by
    intro w
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro h
      rcases InfinitePlace.mk_eq_iff.mp (h.trans (InfinitePlace.mk_embedding w).symm) with
        h1 | h1
      · exact Or.inl h1
      · exact Or.inr ((ComplexEmbedding.involutive_conjugate K).eq_iff.mp h1)
    · rintro (h1 | h1)
      · rw [h1, InfinitePlace.mk_embedding]
      · rw [h1, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  have hReal : ∀ w : {w : InfinitePlace K // w.IsReal},
      (∑ σ ∈ Finset.univ.filter fun σ : K →+* ℂ =>
            InfinitePlace.mk σ = (w : InfinitePlace K),
          (σ b * σ a).re)
        = (mixedEmbedding K b).1 w * (mixedEmbedding K a).1 w := by
    intro w
    rw [hfib w.1, InfinitePlace.conjugate_embedding_eq_of_isReal w.2,
      Finset.insert_eq_self.mpr (Finset.mem_singleton_self _), Finset.sum_singleton,
      mixedEmbedding_apply_isReal, mixedEmbedding_apply_isReal,
      ← InfinitePlace.embedding_of_isReal_apply w.2 b,
      ← InfinitePlace.embedding_of_isReal_apply w.2 a,
      ← Complex.ofReal_mul, Complex.ofReal_re]
  have hCplx : ∀ w : {w : InfinitePlace K // w.IsComplex},
      (∑ σ ∈ Finset.univ.filter fun σ : K →+* ℂ =>
            InfinitePlace.mk σ = (w : InfinitePlace K),
          (σ b * σ a).re)
        = 2 * ((mixedEmbedding K b).2 w * (mixedEmbedding K a).2 w).re := by
    intro w
    have hne : InfinitePlace.embedding (w : InfinitePlace K)
        ≠ ComplexEmbedding.conjugate (InfinitePlace.embedding (w : InfinitePlace K)) := by
      intro h
      refine (InfinitePlace.not_isReal_iff_isComplex.mpr w.2) ?_
      rw [InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
      exact h.symm
    rw [hfib w.1, Finset.sum_pair hne, mixedEmbedding_apply_isComplex,
      mixedEmbedding_apply_isComplex, ComplexEmbedding.conjugate_coe_eq,
      ComplexEmbedding.conjugate_coe_eq]
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have hsum : traceForm K (mixedEmbedding K b) a = (∑ σ : K →+* ℂ, σ b * σ a).re := by
    rw [traceForm, Complex.re_sum,
      ← Finset.sum_fiberwise Finset.univ (fun σ : K →+* ℂ => InfinitePlace.mk σ)
        (fun σ : K →+* ℂ => (σ b * σ a).re),
      InfinitePlace.sum_eq_sum_add_sum]
    rw [Finset.sum_congr rfl (fun w _ => hReal w),
      show (∑ w : {w : InfinitePlace K // w.IsComplex},
            ∑ σ ∈ Finset.univ.filter fun σ : K →+* ℂ =>
              InfinitePlace.mk σ = (w : InfinitePlace K),
            (σ b * σ a).re)
          = 2 * ∑ w : {w : InfinitePlace K // w.IsComplex},
              ((mixedEmbedding K b).2 w * (mixedEmbedding K a).2 w).re
        from by rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun w _ => hCplx w)]
  rw [hsum, sum_embeddings_mul, IsScalarTower.algebraMap_apply ℚ ℝ ℂ,
    Complex.coe_algebraMap, Complex.ofReal_re]

/-- Membership in the actual codifferent ideal is equivalent to integral
trace pairings for a field element. -/
theorem traceForm_mixedEmbedding_int_iff_mem_dualIdeal
    (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) (b : K) :
    (∀ a ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K), ∃ k : ℤ,
        traceForm K (mixedEmbedding K b) a = (k : ℝ)) ↔
      b ∈ (dualIdeal K 𝔞 : Submodule (𝓞 K) K) := by
  rw [FractionalIdeal.mem_coe, ← dualIdeal_eq_dual K 𝔞,
    FractionalIdeal.mem_dual (FractionalIdeal.coeIdeal_ne_zero.mpr hne)]
  refine forall₂_congr fun a ha => ?_
  rw [traceForm_mixedEmbedding, Algebra.traceForm_apply, RingHom.mem_range]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    apply FaithfulSMul.algebraMap_injective ℚ ℝ
    rw [hk, ← IsScalarTower.algebraMap_apply ℤ ℚ ℝ]
    simp
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← hk, ← IsScalarTower.algebraMap_apply ℤ ℚ ℝ]
    simp

/-- **The trace form as an `ℝ`-bilinear functional in its mixed-space argument.**
For fixed `η : K_ℝ`, `traceFormLin K η : K_ℝ →ₗ[ℝ] ℝ` is the `ℝ`-linear map
`χ ↦ ∑_{w real} η.1 w · χ.1 w + 2 ∑_{w cplx} Re(η.2 w · χ.2 w)`. It agrees with
`traceForm K η` after applying `mixedEmbedding` (`traceFormLin_mixedEmbedding`),
and is the bookkeeping device for the `ℚ`-rationality / nondegeneracy argument:
the underlying real symmetric form is nondegenerate, so a
point that pairs to `0` with every lattice basis vector is `0`. -/
def traceFormLin (η : mixedSpace K) : mixedSpace K →ₗ[ℝ] ℝ where
  toFun χ := (∑ w : {w : InfinitePlace K // w.IsReal}, η.1 w * χ.1 w) +
      2 * ∑ w : {w : InfinitePlace K // w.IsComplex}, (η.2 w * χ.2 w).re
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, Complex.add_re,
      Finset.sum_add_distrib]
    ring
  map_smul' c x := by
    have h1 : ∀ w : {w : InfinitePlace K // w.IsReal},
        η.1 w * (c • x).1 w = c * (η.1 w * x.1 w) := by
      intro w; show η.1 w * (c * x.1 w) = _; ring
    have h2 : ∀ w : {w : InfinitePlace K // w.IsComplex},
        (η.2 w * (c • x).2 w).re = c * (η.2 w * x.2 w).re := by
      intro w; show (η.2 w * (c • x.2 w)).re = _
      rw [mul_smul_comm, Complex.smul_re, smul_eq_mul]
    simp only [RingHom.id_apply, smul_eq_mul, h1, h2, ← Finset.mul_sum]
    ring

@[simp] theorem traceFormLin_apply (η χ : mixedSpace K) :
    traceFormLin K η χ =
      (∑ w : {w : InfinitePlace K // w.IsReal}, η.1 w * χ.1 w) +
        2 * ∑ w : {w : InfinitePlace K // w.IsComplex}, (η.2 w * χ.2 w).re := rfl

theorem traceFormLin_mixedEmbedding (η : mixedSpace K) (a : K) :
    traceFormLin K η (mixedEmbedding K a) = traceForm K η a := rfl

/-- `traceForm K η` is additive (here: respects subtraction) in its `K_ℝ`
argument. Used to compare `η` with `mixedEmbedding K b` in the fullness
argument. -/
theorem traceForm_sub_left (η η' : mixedSpace K) (a : K) :
    traceForm K (η - η') a = traceForm K η a - traceForm K η' a := by
  simp only [traceForm, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, sub_mul, Complex.sub_re,
    Finset.sum_sub_distrib]
  ring

/-- `traceForm K η` scales by a natural number under the corresponding scaling of
its field argument: `T(η, n·a) = n·T(η, a)`. (`traceForm` factors through the
ring hom `mixedEmbedding` and the `ℝ`-linear `traceFormLin`, both of which
respect `n • ·`.) -/
theorem traceForm_natCast_mul (η : mixedSpace K) (n : ℕ) (a : K) :
    traceForm K η ((n : K) * a) = n * traceForm K η a := by
  rw [← traceFormLin_mixedEmbedding, ← nsmul_eq_mul, map_nsmul, map_nsmul,
    traceFormLin_mixedEmbedding, nsmul_eq_mul]

/-- **Nondegeneracy of the real trace form** (the analytic input to the
fullness/ℚ-rationality argument). A point `ζ : K_ℝ` whose
trace-form pairing vanishes against every integral-basis element is `0`. Proof:
the pairings against `mixedEmbedding (integralBasis K i)` are the values of the
`ℝ`-linear functional `traceFormLin K ζ` on the `ℝ`-basis `latticeBasis K`, so
the functional vanishes identically; evaluating at the "conjugate" witness
`(ζ.1, conj ζ.2)` gives `∑ (ζ.1 w)² + 2 ∑ ‖ζ.2 w‖² = 0`, forcing `ζ = 0`. -/
theorem traceForm_eq_zero_of_forall_integralBasis (ζ : mixedSpace K)
    (hz : ∀ i, traceForm K ζ (integralBasis K i) = 0) : ζ = 0 := by
  have hlin : traceFormLin K ζ = 0 := by
    refine (latticeBasis K).ext (fun i => ?_)
    rw [latticeBasis_apply, traceFormLin_mixedEmbedding]
    simpa using hz i
  have hval : (∑ w : {w : InfinitePlace K // w.IsReal}, ζ.1 w * ζ.1 w) +
      2 * ∑ w : {w : InfinitePlace K // w.IsComplex}, Complex.normSq (ζ.2 w) = 0 := by
    have hv := LinearMap.congr_fun hlin
      (⟨ζ.1, fun w => starRingEnd ℂ (ζ.2 w)⟩ : mixedSpace K)
    rw [LinearMap.zero_apply, traceFormLin_apply] at hv
    rw [← hv]
    have hre : ∀ w : {w : InfinitePlace K // w.IsComplex},
        Complex.normSq (ζ.2 w) = (ζ.2 w * starRingEnd ℂ (ζ.2 w)).re := by
      intro w; rw [Complex.mul_conj, Complex.ofReal_re]
    simp_rw [hre]
  have hA : (0 : ℝ) ≤ ∑ w : {w : InfinitePlace K // w.IsReal}, ζ.1 w * ζ.1 w :=
    Finset.sum_nonneg (fun w _ => mul_self_nonneg _)
  have hB : (0 : ℝ) ≤ ∑ w : {w : InfinitePlace K // w.IsComplex}, Complex.normSq (ζ.2 w) :=
    Finset.sum_nonneg (fun w _ => Complex.normSq_nonneg _)
  have hA0 : (∑ w : {w : InfinitePlace K // w.IsReal}, ζ.1 w * ζ.1 w) = 0 := by linarith
  have hB0 : (∑ w : {w : InfinitePlace K // w.IsComplex}, Complex.normSq (ζ.2 w)) = 0 := by
    linarith
  have hreal : ∀ w : {w : InfinitePlace K // w.IsReal}, ζ.1 w = 0 := by
    intro w
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun w _ => mul_self_nonneg (ζ.1 w))).mp hA0 w
      (Finset.mem_univ w)
    exact mul_self_eq_zero.mp this
  have hcplx : ∀ w : {w : InfinitePlace K // w.IsComplex}, ζ.2 w = 0 := by
    intro w
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun w _ => Complex.normSq_nonneg (ζ.2 w))).mp hB0 w (Finset.mem_univ w)
    exact Complex.normSq_eq_zero.mp this
  ext w
  · exact hreal w
  · rw [Prod.snd_zero, Pi.zero_apply]; rw [hcplx w]

/-- Every real mixed-space point with integral ideal trace pairings is the
embedding of a field element in the inverse-different ideal. -/
theorem traceForm_int_iff_exists_dualIdeal
    (𝔞 : Ideal (𝓞 K)) (hne : 𝔞 ≠ 0) (η : mixedSpace K) :
    (∀ a ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K), ∃ k : ℤ, traceForm K η a = (k : ℝ)) ↔
      ∃ b ∈ (dualIdeal K 𝔞 : Submodule (𝓞 K) K), mixedEmbedding K b = η := by
  constructor
  · intro h
    classical
    -- A nonzero rational integer `m ∈ 𝔞` (the absolute norm), so that
    -- `m · (integral basis) ⊆ 𝔞` and we can extract rational pairings.
    set m : ℕ := Ideal.absNorm 𝔞 with hm
    have hm0 : (m : ℝ) ≠ 0 := by
      have : 𝔞 ≠ ⊥ := hne
      exact_mod_cast (Ideal.absNorm_eq_zero_iff (I := 𝔞)).not.mpr this
    have hmem : (m : 𝓞 K) ∈ 𝔞 := Ideal.absNorm_mem 𝔞
    -- Rationality: `T(η, integralBasis i) = algebraMap (q i)` for `q i ∈ ℚ`.
    have hq : ∀ i, ∃ q : ℚ, traceForm K η (integralBasis K i) = algebraMap ℚ ℝ q := by
      intro i
      have hmemf : ((m : K) * integralBasis K i) ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := by
        have he : ((m : K) * integralBasis K i)
            = algebraMap (𝓞 K) K ((m : 𝓞 K) * RingOfIntegers.basis K i) := by
          rw [map_mul, integralBasis_apply, map_natCast]
        rw [he]
        exact FractionalIdeal.mem_coeIdeal_of_mem (𝓞 K)⁰
          (Ideal.mul_mem_right (RingOfIntegers.basis K i) 𝔞 hmem)
      obtain ⟨k, hk⟩ := h _ hmemf
      refine ⟨(k : ℚ) / (m : ℚ), ?_⟩
      rw [traceForm_natCast_mul] at hk
      have : traceForm K η (integralBasis K i) = (k : ℝ) / (m : ℝ) := by
        field_simp at hk ⊢; linarith [hk]
      rw [this, map_div₀, map_intCast, map_natCast]
    choose q hqeq using hq
    -- Construct `b ∈ K` with the prescribed pairings via the trace-dual basis.
    set b : K := ∑ i, q i • (integralBasis K).traceDual i with hb
    have htr : ∀ j, Algebra.trace ℚ K (b * integralBasis K j) = q j := by
      intro j
      rw [hb, Finset.sum_mul, map_sum]
      have : ∀ i, Algebra.trace ℚ K ((q i • (integralBasis K).traceDual i) * integralBasis K j)
          = q i • (if j = i then (1 : ℚ) else 0) := by
        intro i
        rw [smul_mul_assoc, map_smul, (integralBasis K).trace_traceDual_mul]
      rw [Finset.sum_congr rfl (fun i _ => this i)]
      simp only [smul_eq_mul, mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq Finset.univ j q]
      simp
    -- `mixedEmbedding K b` and `η` have equal trace pairings against the basis.
    have hpair : ∀ j, traceForm K (mixedEmbedding K b) (integralBasis K j)
        = traceForm K η (integralBasis K j) := by
      intro j
      rw [traceForm_mixedEmbedding, ← Algebra.traceForm_apply, Algebra.traceForm_apply,
        htr j, hqeq j]
    -- Nondegeneracy forces `mixedEmbedding K b = η`.
    have hbη : mixedEmbedding K b = η := by
      have := traceForm_eq_zero_of_forall_integralBasis K (mixedEmbedding K b - η)
        (fun j => by rw [traceForm_sub_left, hpair j, sub_self])
      rwa [sub_eq_zero] at this
    refine ⟨b, ?_, hbη⟩
    -- `b ∈ dualIdeal K 𝔞` from the integrality hypothesis transported through `hbη`.
    refine (traceForm_mixedEmbedding_int_iff_mem_dualIdeal K 𝔞 hne b).mp ?_
    intro a ha
    rw [hbη]
    exact h a ha
  · rintro ⟨b, hb, rfl⟩
    exact (traceForm_mixedEmbedding_int_iff_mem_dualIdeal K 𝔞 hne b).mpr hb

end
end UnitDistance.MinkowskiTrace
