module

public import UnitDistance.RelativeUnitsDifference
public import UnitDistance.EuclideanIdealDeformation

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual compact and reciprocal archimedean coordinates

The single and paired complex coordinates are obtained from the actual
quadratic place fibers. Their reciprocal logarithmic scaling sums to zero,
so the previously proved ideal deformation has the actual unchanged volume.
-/

noncomputable section
open NumberField NumberField.InfinitePlace MeasureTheory
open scoped Classical
namespace UnitDistance.RelativeUnits

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K] [IsTotallyComplex K]

abbrev RealPlaceIndex (F : Type) [Field F] := {w : InfinitePlace F // IsReal w}
abbrev PairPlaceIndex (F : Type) [Field F] := {w : InfinitePlace F // IsComplex w}

/-- Label the two members of an actual pair in the same order as the profile. -/
def pairedSumIndexEquiv :
    (RealPlaceIndex F ⊕ (PairPlaceIndex F ⊕ PairPlaceIndex F)) ≃ PairedPlaceIndex F where
  toFun
    | .inl w => .inl w
    | .inr (.inl w) => .inr (w, false)
    | .inr (.inr w) => .inr (w, true)
  invFun
    | .inl w => .inl w
    | .inr (w, false) => .inr (.inl w)
    | .inr (w, true) => .inr (.inr w)
  left_inv x := by rcases x with w | (w | w) <;> rfl
  right_inv x := by rcases x with w | ⟨w, b⟩; rfl; cases b <;> rfl

/-- The actual all-complex signature identifies places with complex places. -/
def allComplexPlaceEquiv : InfinitePlace K ≃ EuclideanIdeal.ComplexPlace K where
  toFun w := ⟨w, IsTotallyComplex.isComplex w⟩
  invFun w := w.val
  left_inv _ := rfl
  right_inv _ := rfl

/-- Actual complex field places, grouped above the real and complex base places. -/
def relativeComplexPlaceEquiv (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    (RealPlaceIndex F ⊕ (PairPlaceIndex F ⊕ PairPlaceIndex F)) ≃
      EuclideanIdeal.ComplexPlace K :=
  pairedSumIndexEquiv.trans ((pairedPlaceEquiv ι hι).trans allComplexPlaceEquiv)

/-- The grouping input for the actual field tensor profile is derived from
the quadratic extension, with no coordinate-classification hypothesis. -/
def relativePlaceGrouping (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    EuclideanIdeal.ComplexPlace K ≃
      RealPlaceIndex F ⊕ (PairPlaceIndex F ⊕ PairPlaceIndex F) :=
  (relativeComplexPlaceEquiv ι hι).symm

/-- The paper's deformation: one at compact places and `exp(-h), exp(h)`
at the chosen first and second places above every complex base place. -/
def reciprocalLogScale (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (h : PairPlaceIndex F → ℝ) (w : EuclideanIdeal.ComplexPlace K) : ℝ :=
  match relativePlaceGrouping ι hι w with
  | .inl _ => 0
  | .inr (.inl v) => -h v
  | .inr (.inr v) => h v

@[simp] theorem reciprocalLogScale_compact (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (h : PairPlaceIndex F → ℝ) (w : RealPlaceIndex F) :
    reciprocalLogScale ι hι h (relativeComplexPlaceEquiv ι hι (.inl w)) = 0 := by
  simp [reciprocalLogScale, relativePlaceGrouping]

@[simp] theorem reciprocalLogScale_first (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (h : PairPlaceIndex F → ℝ) (w : PairPlaceIndex F) :
    reciprocalLogScale ι hι h (relativeComplexPlaceEquiv ι hι (.inr (.inl w))) = -h w := by
  simp [reciprocalLogScale, relativePlaceGrouping]

@[simp] theorem reciprocalLogScale_second (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (h : PairPlaceIndex F → ℝ) (w : PairPlaceIndex F) :
    reciprocalLogScale ι hι h (relativeComplexPlaceEquiv ι hι (.inr (.inr w))) = h w := by
  simp [reciprocalLogScale, relativePlaceGrouping]

theorem sum_reciprocalLogScale (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (h : PairPlaceIndex F → ℝ) : ∑ w, reciprocalLogScale ι hι h w = 0 := by
  rw [← (relativeComplexPlaceEquiv ι hι).sum_comp (reciprocalLogScale ι hι h)]
  simp [Fintype.sum_sum_type]

/-- Ordinary Lebesgue measure is unchanged for every actual relative parameter. -/
theorem reciprocalDeformation_measurePreserving (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (h : PairPlaceIndex F → ℝ) :
    MeasurePreserving (EuclideanIdeal.deformation K (reciprocalLogScale ι hι h))
      volume volume :=
  EuclideanIdeal.deformation_measurePreserving K _ (sum_reciprocalLogScale ι hι h)

/-- The same half-difference logarithm for field elements, including the
nonintegral norm-one reference generators used for the geometric cosets. -/
def elementDifferenceLog (ι : K ≃ₐ[F] K) (x : K) (w : PairPlaceIndex F) : ℝ :=
  (Real.log (chosenPlaceAbove (K := K) w.val x) -
    Real.log ((ι • chosenPlaceAbove (K := K) w.val) x)) / 2

theorem elementDifferenceLog_mul (ι : K ≃ₐ[F] K) {x y : K}
    (hx : x ≠ 0) (hy : y ≠ 0) :
    elementDifferenceLog ι (x*y) = elementDifferenceLog ι x + elementDifferenceLog ι y := by
  ext w
  simp only [elementDifferenceLog, map_mul, Pi.add_apply,
    Real.log_mul (InfinitePlace.pos_iff.mpr hx).ne' (InfinitePlace.pos_iff.mpr hy).ne']
  ring

theorem elementDifferenceLog_unit (ι : K ≃ₐ[F] K)
    (u : Additive (normOneUnits (F := F) (K := K))) :
    elementDifferenceLog ι (u.toMul.val : K) = relativeDifferenceLog ι u := rfl

theorem normOne_mul_involution (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    {x : K} (hx : Algebra.norm F x = 1) : x*ι x = 1 := by
  rw [← norm_eq_mul_involution ι hι, hx, map_one]

theorem normOne_ne_zero (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    {x : K} (hx : Algebra.norm F x = 1) : x ≠ 0 := by
  have h := normOne_mul_involution ι hι hx
  intro hz
  rw [hz, zero_mul] at h
  exact zero_ne_one h

theorem log_pair_sum_field_normOne (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    {x : K} (hx : Algebra.norm F x = 1) (v : InfinitePlace K) :
    Real.log (v x)+Real.log ((ι • v) x) = 0 := by
  have h : v x*(ι • v) x = 1 := by
    rw [← place_norm_eq_mul ι hι, hx, map_one]
  rw [← Real.log_mul (InfinitePlace.pos_iff.mpr (normOne_ne_zero ι hι hx)).ne'
    (InfinitePlace.pos_iff.mpr (normOne_ne_zero ι hι hx)).ne', h, Real.log_one]

theorem elementDifferenceLog_normOne (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    {x : K} (hx : Algebra.norm F x = 1) (w : PairPlaceIndex F) :
    elementDifferenceLog ι x w = Real.log (chosenPlaceAbove (K := K) w.val x) := by
  have h := log_pair_sum_field_normOne ι hι hx (chosenPlaceAbove w.val)
  unfold elementDifferenceLog
  linarith

/-- Every norm-one field displacement has modulus one at each compact place. -/
theorem compact_place_normOne (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    {x : K} (hx : Algebra.norm F x = 1) (w : RealPlaceIndex F) :
    chosenPlaceAbove (K := K) w.val x = 1 := by
  have h := log_pair_sum_field_normOne ι hι hx (chosenPlaceAbove w.val)
  rw [involution_smul_eq_of_real_comap ι hι _
    (by rw [chosenPlaceAbove_comap]; exact w.prop)] at h
  have he : Real.log (chosenPlaceAbove (K := K) w.val x) = 0 := by linarith
  rw [← Real.exp_log (InfinitePlace.pos_iff.mpr (normOne_ne_zero ι hι hx)), he,
    Real.exp_zero]

/-- The first actual modulus is the exponential of the unweighted log coordinate. -/
theorem first_place_normOne (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    {x : K} (hx : Algebra.norm F x = 1) (w : PairPlaceIndex F) :
    chosenPlaceAbove (K := K) w.val x = Real.exp (elementDifferenceLog ι x w) := by
  rw [elementDifferenceLog_normOne ι hι hx,
    Real.exp_log (InfinitePlace.pos_iff.mpr (normOne_ne_zero ι hι hx))]

/-- The partner modulus is the reciprocal exponential, without an assumed
coordinate compatibility or an integrality condition on the field element. -/
theorem second_place_normOne (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    {x : K} (hx : Algebra.norm F x = 1) (w : PairPlaceIndex F) :
    (ι • chosenPlaceAbove (K := K) w.val) x = Real.exp (-elementDifferenceLog ι x w) := by
  have h := log_pair_sum_field_normOne ι hι hx (chosenPlaceAbove w.val)
  rw [elementDifferenceLog_normOne ι hι hx]
  have he : Real.log ((ι • chosenPlaceAbove (K := K) w.val) x) =
      -Real.log (chosenPlaceAbove (K := K) w.val x) := by linarith
  rw [← he, Real.exp_log (InfinitePlace.pos_iff.mpr (normOne_ne_zero ι hι hx))]

theorem euclidean_embedding_coordinate_norm (x : K) (w : EuclideanIdeal.ComplexPlace K) :
    ‖(EuclideanIdeal.coordinates K (EuclideanIdeal.embedding K x)).2 w‖ = w.val x := by
  simp only [EuclideanIdeal.embedding, ContinuousLinearEquiv.apply_symm_apply]
  exact InfinitePlace.norm_embedding_eq w.val x

theorem deformed_embedding_coordinate_norm (h : EuclideanIdeal.ComplexPlace K → ℝ)
    (x : K) (w : EuclideanIdeal.ComplexPlace K) :
    ‖(EuclideanIdeal.coordinates K
      (EuclideanIdeal.deformation K h (EuclideanIdeal.embedding K x))).2 w‖ =
        Real.exp (h w)*w.val x := by
  rw [EuclideanIdeal.coordinates_deformation]
  change ‖Real.exp (h w) •
    (EuclideanIdeal.coordinates K (EuclideanIdeal.embedding K x)).2 w‖ = _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    euclidean_embedding_coordinate_norm]

theorem reciprocal_compact_modulus (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (h : PairPlaceIndex F → ℝ) {x : K} (hx : Algebra.norm F x = 1)
    (w : RealPlaceIndex F) :
    ‖(EuclideanIdeal.coordinates K (EuclideanIdeal.deformation K (reciprocalLogScale ι hι h)
      (EuclideanIdeal.embedding K x))).2 (relativeComplexPlaceEquiv ι hι (.inl w))‖ = 1 := by
  rw [deformed_embedding_coordinate_norm, reciprocalLogScale_compact, Real.exp_zero, one_mul]
  exact compact_place_normOne ι hι hx w

theorem reciprocal_first_modulus (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (h : PairPlaceIndex F → ℝ) {x : K} (hx : Algebra.norm F x = 1)
    (w : PairPlaceIndex F) :
    ‖(EuclideanIdeal.coordinates K (EuclideanIdeal.deformation K (reciprocalLogScale ι hι h)
      (EuclideanIdeal.embedding K x))).2 (relativeComplexPlaceEquiv ι hι (.inr (.inl w)))‖ =
        Real.exp (elementDifferenceLog ι x w-h w) := by
  rw [deformed_embedding_coordinate_norm, reciprocalLogScale_first]
  change Real.exp (-h w)*chosenPlaceAbove (K := K) w.val x = _
  rw [first_place_normOne ι hι hx, ← Real.exp_add]
  congr 1
  ring

theorem reciprocal_second_modulus (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (h : PairPlaceIndex F → ℝ) {x : K} (hx : Algebra.norm F x = 1)
    (w : PairPlaceIndex F) :
    ‖(EuclideanIdeal.coordinates K (EuclideanIdeal.deformation K (reciprocalLogScale ι hι h)
      (EuclideanIdeal.embedding K x))).2 (relativeComplexPlaceEquiv ι hι (.inr (.inr w)))‖ =
        Real.exp (-(elementDifferenceLog ι x w-h w)) := by
  rw [deformed_embedding_coordinate_norm, reciprocalLogScale_second]
  change Real.exp (h w)*(ι • chosenPlaceAbove (K := K) w.val) x = _
  rw [second_place_normOne ι hι hx, ← Real.exp_add]
  congr 1
  ring

end UnitDistance.RelativeUnits
