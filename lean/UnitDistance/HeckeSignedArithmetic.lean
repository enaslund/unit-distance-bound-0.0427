module

public import UnitDistance.HeckeSignedWeights
public import UnitDistance.HeckeNormCharacter
public import UnitDistance.QuadraticSevenNormCongruence

@[expose] public section
set_option backward.privateInPublic true


/-! The actual root of seven discharges the signed unit covariance hypothesis
and identifies the finite character with the signed archimedean norm. -/
noncomputable section
open NumberField NumberField.InfinitePlace DedekindResidue MeasureTheory
open NumberField.mixedEmbedding NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped BigOperators Real Classical
namespace UnitDistance.NumberFieldAnalysis
variable (K : Type*) [Field K] [NumberField K]

theorem unit_rational_norm_eq_one_of_root_seven (r : K) (hr : r^2=7)
    (epsilon : (𝓞 K)ˣ) :
    Algebra.norm ℚ (algebraMap (𝓞 K) K (epsilon : 𝓞 K)) = 1 := by
  have h := UnitDistance.QuadraticSeven.integer_norm_eq_one_of_isUnit_of_root
    r hr (epsilon : 𝓞 K) epsilon.isUnit
  rw [← Algebra.coe_norm_int, h]
  norm_num

theorem heckeSignedTerm_unit_mul_of_root_seven (r : K) (hr : r^2=7)
    (t : ℝ) (u : logSpace K) (epsilon : (𝓞 K)ˣ) (y : K) :
    heckeSignedTerm K t u (embeddingCoords K (algebraMap (𝓞 K) K (epsilon : 𝓞 K)*y)) =
      heckeSignedTerm K t (u+logEmbedding K (Additive.ofMul epsilon)) (embeddingCoords K y) :=
  heckeSignedTerm_unit_mul_of_norm_one K t u epsilon
    (unit_rational_norm_eq_one_of_root_seven K r hr epsilon) y

theorem idealChiFour_principal_eq_signedArchCharacter (r : K) (hr : r^2=7)
    (x : 𝓞 K) (hx : x ≠ 0) (hodd : Odd (Algebra.norm ℤ x)) :
    idealChiFour K (Ideal.span {x}) = signedArchCharacter K (x : K) := by
  rw [idealChiFour, chiFourReal, Ideal.absNorm_span_singleton,
    UnitDistance.QuadraticSeven.integer_norm_chi4_eq_sign_of_root r hr x hodd,
    signedArchCharacter_eq_sign_norm K (by exact_mod_cast hx), ← Algebra.coe_norm_int,
    sign_intCast]
  simp only [Int.sign_eq_sign, SignType.intCast_cast]

end UnitDistance.NumberFieldAnalysis
