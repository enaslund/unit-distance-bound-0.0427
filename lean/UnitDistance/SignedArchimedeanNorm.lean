module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.Data.Sign.Basic
public import Mathlib.Tactic.NormNum

@[expose] public section
set_option backward.privateInPublic true


/-! The signed archimedean norm formula, before taking absolute values.
The embedding-fiber argument parallels Mathlib's
`InfinitePlace.prod_eq_abs_norm`; conjugate pairs contribute positive squares.
-/
noncomputable section
open NumberField NumberField.InfinitePlace
open scoped BigOperators Classical
namespace UnitDistance.NumberFieldAnalysis

variable (K : Type*) [Field K] [NumberField K]

/-- The product of signs at the actual real places. -/
def signedArchCharacter (y : K) : ℝ :=
  ∏ w : {w : InfinitePlace K // IsReal w},
    (SignType.sign (embedding_of_isReal w.2 y) : ℝ)

private theorem prod_embedding_fiber (w : InfinitePlace K) (y : K) :
    (∏ φ ∈ (Finset.univ.filter (fun φ : K →+* ℂ => InfinitePlace.mk φ = w)), φ y) =
      if h : IsReal w then (embedding_of_isReal h y : ℂ) else ((w y)^2 : ℝ) := by
  classical
  have hset : (Finset.univ.filter (fun φ : K →+* ℂ => InfinitePlace.mk φ = w)) =
      {embedding w, ComplexEmbedding.conjugate (embedding w)} := by
    ext φ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    conv_lhs => rw [← mk_embedding w, mk_eq_iff, ComplexEmbedding.conjugate,
      star_involutive.eq_iff]
  rw [hset]
  by_cases hw : IsReal w
  · rw [dif_pos hw, ComplexEmbedding.isReal_iff.mp (isReal_iff.mp hw)]
    simp only [Finset.insert_eq_of_mem, Finset.mem_singleton, Finset.prod_singleton]
    exact (embedding_of_isReal_apply hw y).symm
  · rw [dif_neg hw, Finset.prod_pair (by
      rwa [Ne, eq_comm, ← ComplexEmbedding.isReal_iff, ← isReal_iff])]
    change embedding w y * (starRingEnd ℂ) (embedding w y) = ((w y)^2 : ℝ)
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_embedding_eq]

/-- The ordinary signed field norm is the product of real values and the
positive squared absolute values at complex places. -/
theorem norm_eq_real_product_mul_complex_product (y : K) :
    (Algebra.norm ℚ y : ℝ) =
      (∏ w : {w : InfinitePlace K // IsReal w}, embedding_of_isReal w.2 y) *
      ∏ w : {w : InfinitePlace K // IsComplex w}, (w.1 y)^2 := by
  classical
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ y
  rw [← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ)
    (fun φ : K →+* ℂ => φ y) (fun φ => φ y)
      (fun _ => by simp [RingHom.equivRatAlgHom_apply])] at h
  rw [← Finset.prod_fiberwise Finset.univ InfinitePlace.mk (fun φ : K →+* ℂ => φ y)] at h
  simp_rw [prod_embedding_fiber K] at h
  rw [InfinitePlace.prod_eq_prod_mul_prod] at h
  simp only [dite_true, Subtype.property] at h
  have hcomplex : ∀ w : {w : InfinitePlace K // IsComplex w}, ¬IsReal w.1 :=
    fun w => not_isReal_iff_isComplex.mpr w.2
  simp only [hcomplex, dite_false] at h
  apply Complex.ofReal_injective
  simpa only [eq_ratCast, Complex.ofReal_ratCast, Complex.ofReal_mul,
    Complex.ofReal_prod, Complex.ofReal_pow] using h

/-- Away from zero, the positive complex-place factors leave precisely the
product of real signs. -/
theorem signedArchCharacter_eq_sign_norm {y : K} (hy : y ≠ 0) :
    signedArchCharacter K y = (SignType.sign (Algebra.norm ℚ y) : ℝ) := by
  classical
  have hc : 0 < ∏ w : {w : InfinitePlace K // IsComplex w}, (w.1 y)^2 := by
    apply Finset.prod_pos
    intro w _
    exact sq_pos_of_pos (pos_iff.mpr hy)
  have hnorm := norm_eq_real_product_mul_complex_product K y
  have hs := congrArg (fun x : ℝ => (SignType.sign x : ℝ)) hnorm
  rw [sign_mul, sign_pos hc, mul_one] at hs
  have hprod : (SignType.sign (∏ w : {w : InfinitePlace K // IsReal w},
      embedding_of_isReal w.2 y) : ℝ) = signedArchCharacter K y := by
    exact map_prod ((SignType.castHom : SignType →*₀ ℝ).comp (signHom : ℝ →*₀ SignType))
      (fun w : {w : InfinitePlace K // IsReal w} => embedding_of_isReal w.2 y) Finset.univ
  rw [hprod] at hs
  have hcast : SignType.sign ((Algebra.norm ℚ y : ℚ) : ℝ) =
      SignType.sign (Algebra.norm ℚ y) := by
    simp only [sign_apply, Rat.cast_pos, Rat.cast_lt_zero]
  simpa only [hcast] using hs.symm

end UnitDistance.NumberFieldAnalysis
