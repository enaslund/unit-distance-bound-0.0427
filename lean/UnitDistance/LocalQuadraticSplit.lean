module

public import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.Tactic

@[expose] public section
set_option backward.privateInPublic true


/-! # Split quadratic norm-one coordinates

The map `a + b i ↦ (a + ι b, a - ι b)` identifies the quadratic algebra
`K[i]` with `K × K` when `ι² = -1` and the field has characteristic different
from two. It sends the algebra norm to coordinate product, hence norm-one
elements to reciprocal coordinates. Its coefficient matrix has determinant
`-2ι`; no assertion about integral bases or Haar pushforward is made here.
-/

noncomputable section
open QuadraticAlgebra

namespace UnitDistance.Local.QuadraticSplit

variable {K : Type*} [Field K]

/-- The split coordinates of the actual quadratic algebra with `i² = -1`. -/
def coordinates (ι : K) (z : QuadraticAlgebra K (-1) 0) : K × K :=
  (z.re + ι * z.im, z.re - ι * z.im)

theorem root_ne_zero {ι : K} (hι : ι ^ 2 = -1) : ι ≠ 0 := by
  intro h
  rw [h, zero_pow (by decide)] at hι
  exact neg_ne_zero.mpr one_ne_zero hι.symm

theorem coordinates_add (ι : K) (z w : QuadraticAlgebra K (-1) 0) :
    coordinates ι (z + w) = coordinates ι z + coordinates ι w := by
  ext <;> simp [coordinates] <;> ring

theorem coordinates_mul {ι : K} (hι : ι ^ 2 = -1)
    (z w : QuadraticAlgebra K (-1) 0) :
    coordinates ι (z * w) = coordinates ι z * coordinates ι w := by
  ext <;> simp only [coordinates, QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul,
    Prod.fst_mul, Prod.snd_mul, zero_mul, add_zero]
  · linear_combination -z.im * w.im * hι
  · linear_combination -z.im * w.im * hι

/-- The explicit splitting algebra equivalence, with its inverse half-sum and
half-difference formulas. -/
def splitEquiv (ι : K) (hι : ι ^ 2 = -1) (htwo : (2 : K) ≠ 0) :
    QuadraticAlgebra K (-1) 0 ≃ₐ[K] K × K where
  toFun := coordinates ι
  invFun x := ⟨(x.1 + x.2) / 2, (x.1 - x.2) / (2 * ι)⟩
  left_inv z := by
    ext <;> simp only [coordinates]
    · field_simp
      ring
    · field_simp [htwo, root_ne_zero hι]
      ring
  right_inv x := by
    ext <;> simp only [coordinates]
    · field_simp [htwo, root_ne_zero hι]
      ring
    · field_simp [htwo, root_ne_zero hι]
      ring
  map_mul' := coordinates_mul hι
  map_add' := coordinates_add ι
  commutes' a := by
    ext <;> simp [coordinates]

theorem coordinates_bijective (ι : K) (hι : ι ^ 2 = -1) (htwo : (2 : K) ≠ 0) :
    Function.Bijective (coordinates ι) :=
  (splitEquiv ι hι htwo).bijective

/-- The quadratic norm becomes coordinate product under the split map. -/
theorem norm_eq_product {ι : K} (hι : ι ^ 2 = -1) (z : QuadraticAlgebra K (-1) 0) :
    z.norm = (coordinates ι z).1 * (coordinates ι z).2 := by
  simp only [QuadraticAlgebra.norm_def, coordinates, zero_mul, add_zero]
  linear_combination z.im ^ 2 * hι

/-- The determinant of multiplication, the ordinary algebra norm, is the
product of the two split coordinates. -/
theorem determinant_norm_eq_product {ι : K} (hι : ι ^ 2 = -1)
    (z : QuadraticAlgebra K (-1) 0) :
    (DistribSMul.toLinearMap K (QuadraticAlgebra K (-1) 0) z).det =
      (coordinates ι z).1 * (coordinates ι z).2 := by
  rw [QuadraticAlgebra.det_toLinearMap_eq_norm, norm_eq_product hι]

/-- The same identity for Mathlib's standard determinant-defined algebra norm. -/
theorem algebra_norm_eq_product {ι : K} (hι : ι ^ 2 = -1)
    (z : QuadraticAlgebra K (-1) 0) :
    Algebra.norm K z = (coordinates ι z).1 * (coordinates ι z).2 := by
  change (DistribSMul.toLinearMap K (QuadraticAlgebra K (-1) 0) z).det = _
  exact determinant_norm_eq_product hι z

/-- A norm-one element has a nonzero first coordinate, and its second
coordinate is exactly its inverse. -/
theorem norm_one_iff_reciprocal {ι : K} (hι : ι ^ 2 = -1)
    (z : QuadraticAlgebra K (-1) 0) :
    z.norm = 1 ↔ ∃ t : K, t ≠ 0 ∧ coordinates ι z = (t, t⁻¹) := by
  rw [norm_eq_product hι]
  constructor
  · intro h
    have ht : (coordinates ι z).1 ≠ 0 := by intro hz; simp [hz] at h
    refine ⟨(coordinates ι z).1, ht, Prod.ext rfl ?_⟩
    have hi := congrArg (fun y => (coordinates ι z).1⁻¹ * y) h
    simpa only [← mul_assoc, inv_mul_cancel₀ ht, one_mul, mul_one] using hi
  · rintro ⟨t, ht, h⟩
    rw [h]
    exact mul_inv_cancel₀ ht

/-- Quadratic conjugation exchanges the two split coordinates. -/
theorem coordinates_star (ι : K) (z : QuadraticAlgebra K (-1) 0) :
    coordinates ι (star z) = ((coordinates ι z).2, (coordinates ι z).1) := by
  ext <;> simp [coordinates]
  ring

/-- Every reciprocal local displacement is the split image of an actual
quadratic element of algebra norm one. -/
theorem exists_norm_one_reciprocal_preimage (ι : K) (hι : ι ^ 2 = -1) (htwo : (2 : K) ≠ 0)
    (π u : K) (hπ : π ≠ 0) (hu : u ≠ 0) (n : ℤ) :
    ∃ z : QuadraticAlgebra K (-1) 0, Algebra.norm K z = 1 ∧
      coordinates ι z = (π ^ n * u, π ^ (-n) * u⁻¹) := by
  let x : K × K := (π ^ n * u, π ^ (-n) * u⁻¹)
  refine ⟨(splitEquiv ι hι htwo).symm x, ?_, (splitEquiv ι hι htwo).apply_symm_apply x⟩
  rw [algebra_norm_eq_product hι]
  change ((splitEquiv ι hι htwo) ((splitEquiv ι hι htwo).symm x)).1 *
    ((splitEquiv ι hι htwo) ((splitEquiv ι hι htwo).symm x)).2 = 1
  rw [(splitEquiv ι hι htwo).apply_symm_apply]
  dsimp [x]
  rw [mul_mul_mul_comm, ← zpow_add₀ hπ, add_neg_cancel, zpow_zero,
    mul_inv_cancel₀ hu, one_mul]

/-- Determinant in coefficient coordinates; it must be accounted for if those
coordinates are used to compare additive measures or integral lattices. -/
theorem coordinate_matrix_det (ι : K) : Matrix.det !![1, ι; 1, -ι] = -(2 * ι) := by
  rw [Matrix.det_fin_two]
  change (1 : K) * (-ι) - ι * 1 = -(2 * ι)
  ring

end UnitDistance.Local.QuadraticSplit
