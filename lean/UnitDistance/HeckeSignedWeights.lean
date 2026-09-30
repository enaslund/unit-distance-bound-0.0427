module

public import UnitDistance.SignedArchimedeanNorm
public import UnitDistance.HeckeOddGaussian
public import UnitDistance.Upstream.AINTLIB.CompletedZeta.MellinAgreement

@[expose] public section
set_option backward.privateInPublic true


/-! Actual real-place parity weights and their unit covariance. These are
the signed kernels whose Mellin integrals give the norm-character series.
The ordinary Hecke coordinates, lattices and fundamental units are unchanged.
-/
noncomputable section
open NumberField NumberField.InfinitePlace DedekindResidue MeasureTheory
open NumberField.mixedEmbedding NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped BigOperators Real Classical
namespace UnitDistance.NumberFieldAnalysis

variable (K : Type*) [Field K] [NumberField K]

/-- Odd on each real embedding coordinate, even on both coordinates of
an actual complex place. -/
def heckeRealParity : index K → Bool := Sum.elim (fun _ => true) (fun _ => false)

/-- The real polynomial factor multiplying the ordinary lattice Gaussian. -/
def heckeSignedAmplitude (c : InfinitePlace K → ℝ) (x : EuclideanSpace ℝ (index K)) : ℝ :=
  ∏ w : {w : InfinitePlace K // IsReal w}, Real.sqrt (c w.1)*x (Sum.inl w)

/-- Literal signed term in ordinary Hecke coordinates. -/
def heckeSignedTerm (t : ℝ) (u : logSpace K) (x : EuclideanSpace ℝ (index K)) : ℝ :=
  heckeSignedAmplitude K (heckeWeights K t u) x * gaussTerm K t u x

theorem heckeParityKernel_eq_signedTerm (t : ℝ) (u : logSpace K)
    (x : EuclideanSpace ℝ (index K)) :
    heckeParityKernel (heckeRealParity K) (placeWeights K (heckeWeights K t u)) x =
      (heckeSignedTerm K t u x : ℂ) := by
  classical
  unfold heckeParityKernel heckeNormalizedGaussian
  simp_rw [heckeRealGaussian_ofReal]
  rw [Finset.prod_mul_distrib]
  have hgauss : (∏ i : index K,
      (Real.exp (-Real.pi*placeWeights K (heckeWeights K t u) i*x i^2) : ℂ)) =
      (gaussTerm K t u x : ℂ) := by
    rw [← Complex.ofReal_prod, ← Real.exp_sum]
    change (Real.exp (∑ i : index K,
      -Real.pi*placeWeights K (heckeWeights K t u) i*x i^2) : ℂ) =
      (Real.exp (-Real.pi*∑ i : index K,
        placeWeights K (heckeWeights K t u) i*x i^2) : ℂ)
    congr 2
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hamp : (∏ i : index K, ((if heckeRealParity K i then
        Real.sqrt (placeWeights K (heckeWeights K t u) i)*x i else 1 : ℝ) : ℂ)) =
      (heckeSignedAmplitude K (heckeWeights K t u) x : ℂ) := by
    rw [← Complex.ofReal_prod]
    congr 1
    rw [Fintype.prod_sum_type]
    simp only [heckeRealParity, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true,
      ↓reduceIte, Finset.prod_const_one, mul_one, placeWeights, heckeSignedAmplitude]
  rw [hamp, hgauss]
  exact (Complex.ofReal_mul _ _).symm

theorem heckeSignedAmplitude_embedding (c : InfinitePlace K → ℝ) (y : K) :
    heckeSignedAmplitude K c (embeddingCoords K y) =
      ∏ w : {w : InfinitePlace K // IsReal w}, Real.sqrt (c w.1)*embedding_of_isReal w.2 y := by
  simp only [heckeSignedAmplitude, embeddingCoords_isReal]

theorem heckeSignedAmplitude_unit_mul (t : ℝ) (u : logSpace K)
    (epsilon : (𝓞 K)ˣ) (y : K) :
    heckeSignedAmplitude K (heckeWeights K t u)
        (embeddingCoords K (algebraMap (𝓞 K) K (epsilon : 𝓞 K)*y)) =
      signedArchCharacter K (algebraMap (𝓞 K) K (epsilon : 𝓞 K)) *
        heckeSignedAmplitude K
          (heckeWeights K t (u+logEmbedding K (Additive.ofMul epsilon)))
          (embeddingCoords K y) := by
  classical
  rw [heckeSignedAmplitude_embedding, heckeSignedAmplitude_embedding,
    signedArchCharacter, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro w _
  rw [map_mul, heckeWeights_add_logEmbedding]
  have habs : w.1 (algebraMap (𝓞 K) K (epsilon : 𝓞 K)) =
      |embedding_of_isReal w.2 (algebraMap (𝓞 K) K (epsilon : 𝓞 K))| := by
    rw [← norm_embedding_of_isReal w.2, Real.norm_eq_abs]
  dsimp only []
  rw [habs, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_abs]
  calc
    _ = ((SignType.sign (embedding_of_isReal w.2 (algebraMap (𝓞 K) K (epsilon : 𝓞 K))) : ℝ) *
        |embedding_of_isReal w.2 (algebraMap (𝓞 K) K (epsilon : 𝓞 K))|) *
        Real.sqrt (heckeWeights K t u w.1)*embedding_of_isReal w.2 y := by
      rw [sign_mul_abs]
      ring
    _ = _ := by ring

theorem heckeSignedTerm_unit_mul (t : ℝ) (u : logSpace K)
    (epsilon : (𝓞 K)ˣ) (y : K) :
    heckeSignedTerm K t u (embeddingCoords K (algebraMap (𝓞 K) K (epsilon : 𝓞 K)*y)) =
      signedArchCharacter K (algebraMap (𝓞 K) K (epsilon : 𝓞 K)) *
        heckeSignedTerm K t (u+logEmbedding K (Additive.ofMul epsilon)) (embeddingCoords K y) := by
  have hg := gaussTerm_unit_smul K t u epsilon y
  have hsmul : epsilon • mixedEmbedding K y =
      mixedEmbedding K (algebraMap (𝓞 K) K (epsilon : 𝓞 K)*y) := by
    rw [unitSMul_smul, ← map_mul]
  rw [hsmul, euclidMixedEquiv_symm_mixedEmbedding] at hg
  unfold heckeSignedTerm
  rw [heckeSignedAmplitude_unit_mul, hg, mul_assoc]

/-- An actual unit of signed norm one has exact signed-kernel covariance,
with no assumed periodicity of the theta series. -/
theorem heckeSignedTerm_unit_mul_of_norm_one (t : ℝ) (u : logSpace K)
    (epsilon : (𝓞 K)ˣ)
    (hnorm : Algebra.norm ℚ (algebraMap (𝓞 K) K (epsilon : 𝓞 K)) = 1) (y : K) :
    heckeSignedTerm K t u (embeddingCoords K (algebraMap (𝓞 K) K (epsilon : 𝓞 K)*y)) =
      heckeSignedTerm K t (u+logEmbedding K (Additive.ofMul epsilon)) (embeddingCoords K y) := by
  rw [heckeSignedTerm_unit_mul, signedArchCharacter_eq_sign_norm K
    (by simpa only [ne_eq, RingOfIntegers.coe_eq_zero_iff] using Units.ne_zero epsilon), hnorm]
  simp

end UnitDistance.NumberFieldAnalysis
