module

public import UnitDistance.HeckeSignedArithmetic
public import UnitDistance.HeckeSignedScaling

@[expose] public section
set_option backward.privateInPublic true


/-! The literal odd integral-norm support and its actual unit covariance.
This support is the finite-place restriction used by the signed theta series. -/
noncomputable section
open NumberField NumberField.InfinitePlace DedekindResidue MeasureTheory
open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped BigOperators Real Classical nonZeroDivisors NNReal ENNReal
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.NumberFieldAnalysis
variable (K : Type*) [Field K] [NumberField K]

/-- An actual embedded algebraic integer of odd signed (equivalently absolute) norm. -/
def oddNormPoint (x : EuclideanSpace ℝ (index K)) : Prop :=
  ∃ a : 𝓞 K, embeddingCoords K (a : K) = x ∧ Odd (Algebra.norm ℤ a)

theorem embeddingCoords_injective : Function.Injective (embeddingCoords K) := by
  intro x y h
  apply (mixedEmbedding K).injective
  have hx := euclidMixedEquiv_symm_mixedEmbedding K x
  have hy := euclidMixedEquiv_symm_mixedEmbedding K y
  exact (euclidMixedEquiv K).symm.injective (hx.trans (h.trans hy.symm))

@[simp] theorem oddNormPoint_embedding (a : 𝓞 K) :
    oddNormPoint K (embeddingCoords K (a : K)) ↔ Odd (Algebra.norm ℤ a) := by
  constructor
  · rintro ⟨b,hb,hodd⟩
    have he : b = a := RingOfIntegers.ext (embeddingCoords_injective K hb)
    simpa [he] using hodd
  · exact fun ha => ⟨a,rfl,ha⟩

@[simp] theorem not_oddNormPoint_zero : ¬ oddNormPoint K 0 := by
  have h := oddNormPoint_embedding K 0
  simpa [embeddingCoords] using h

theorem oddNormPoint_conePreimage (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) :
    oddNormPoint K (embeddingCoords K (conePreimage K J a)) ↔
      Odd (intNorm (idealSetMap K J a)) := by
  rw [conePreimage, oddNormPoint_embedding, intNorm, Int.natAbs_odd]

theorem oddNormPoint_unit_mul (r : K) (hr : r^2=7)
    (epsilon : (𝓞 K)ˣ) (y : K) :
    oddNormPoint K (embeddingCoords K (algebraMap (𝓞 K) K (epsilon : 𝓞 K)*y)) ↔
      oddNormPoint K (embeddingCoords K y) := by
  have hnorm (eps : (𝓞 K)ˣ) : Algebra.norm ℤ (eps : 𝓞 K) = 1 :=
    UnitDistance.QuadraticSeven.integer_norm_eq_one_of_isUnit_of_root r hr _ eps.isUnit
  constructor
  · rintro ⟨a,ha,hodd⟩
    refine ⟨(↑epsilon⁻¹ : 𝓞 K)*a, ?_, ?_⟩
    · have he := embeddingCoords_injective K ha
      congr 1
      push_cast
      change algebraMap (𝓞 K) K (↑epsilon⁻¹ : 𝓞 K) * algebraMap (𝓞 K) K a = y
      change algebraMap (𝓞 K) K a = _ at he
      rw [he, ← mul_assoc, ← map_mul]
      simp
    · simpa only [map_mul, hnorm, one_mul] using hodd
  · rintro ⟨a,ha,hodd⟩
    refine ⟨(epsilon : 𝓞 K)*a, ?_, ?_⟩
    · have he := embeddingCoords_injective K ha
      congr 1
      push_cast
      change algebraMap (𝓞 K) K (epsilon : 𝓞 K) * algebraMap (𝓞 K) K a = _
      change algebraMap (𝓞 K) K a = y at he
      rw [he]
    · simpa only [map_mul, hnorm, one_mul] using hodd

theorem signedArchCharacter_conePreimage_eq_chiFour (r : K) (hr : r^2=7)
    (J : (Ideal (𝓞 K))⁰) (a : idealSet K J)
    (ha : Odd (intNorm (idealSetMap K J a))) :
    signedArchCharacter K (conePreimage K J a) = chiFourReal (intNorm (idealSetMap K J a)) := by
  let x : (𝓞 K)⁰ := preimageOfMemIntegerSet (idealSetMap K J a)
  have hx : (x : 𝓞 K) ≠ 0 := nonZeroDivisors.coe_ne_zero x
  have hn : Odd (Algebra.norm ℤ (x : 𝓞 K)) := Int.natAbs_odd.mp ha
  have h := idealChiFour_principal_eq_signedArchCharacter K r hr (x : 𝓞 K) hx hn
  simpa only [idealChiFour, Ideal.absNorm_span_singleton, intNorm, conePreimage] using h.symm

/-- Signed Gaussian restricted to the actual odd-norm integral points. -/
def heckeOddSignedTerm (t : ℝ) (u : logSpace K)
    (x : EuclideanSpace ℝ (index K)) : ℝ :=
  if oddNormPoint K x then heckeSignedTerm K t u x else 0

@[simp] theorem heckeOddSignedTerm_zero (t : ℝ) (u : logSpace K) :
    heckeOddSignedTerm K t u 0 = 0 := by simp [heckeOddSignedTerm]

theorem continuous_heckeOddSignedTerm (x : EuclideanSpace ℝ (index K)) :
    Continuous (fun q : ℝ × logSpace K => heckeOddSignedTerm K q.1 q.2 x) := by
  by_cases hx : oddNormPoint K x
  · simpa [heckeOddSignedTerm, hx] using continuous_heckeSignedTerm K x
  · simpa [heckeOddSignedTerm, hx] using
      (continuous_const : Continuous (fun _ : ℝ × logSpace K => (0:ℝ)))

theorem heckeOddSignedTerm_unit_mul (r : K) (hr : r^2=7)
    (t : ℝ) (u : logSpace K) (epsilon : (𝓞 K)ˣ) (y : K) :
    heckeOddSignedTerm K t u (embeddingCoords K (algebraMap (𝓞 K) K (epsilon : 𝓞 K)*y)) =
      heckeOddSignedTerm K t (u+logEmbedding K (Additive.ofMul epsilon)) (embeddingCoords K y) := by
  unfold heckeOddSignedTerm
  rw [oddNormPoint_unit_mul K r hr, heckeSignedTerm_unit_mul_of_root_seven K r hr]

/-- Each actual cone generator contributes the ordinary character of its norm.
Even norms vanish before taking any integral. -/
theorem heckeOddSignedTerm_cone_norm_scaled (r : K) (hr : r^2=7)
    (J : (Ideal (𝓞 K))⁰) (a : idealSet K J) {t : ℝ} (ht : 0 < t) (u : logSpace K) :
    heckeOddSignedTerm K t u (embeddingCoords K (conePreimage K J a)) =
      chiFourReal (intNorm (idealSetMap K J a)) *
        heckeSignedTerm K ((intNorm (idealSetMap K J a) : ℝ)^2*t)
          (u+xShift K (conePreimage K J a)) (embeddingCoords K 1) := by
  unfold heckeOddSignedTerm
  rw [oddNormPoint_conePreimage]
  split_ifs with ha
  · rw [heckeSignedTerm_norm_scaled K (conePreimage_ne_zero K J a) ht.le,
      signedArchCharacter_conePreimage_eq_chiFour K r hr J a ha, abs_norm_conePreimage]
  · rw [chiFourReal_zero_of_even (Nat.not_odd_iff_even.mp ha), zero_mul]

end UnitDistance.NumberFieldAnalysis
