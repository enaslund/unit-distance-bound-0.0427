module

public import UnitDistance.RelativeUnitsLogCoordinates
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section
set_option backward.privateInPublic true


/-! # Volume-preserving coordinate reindexing and triangular shears -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Classical
open MeasureTheory

namespace UnitDistance.RelativeUnits

variable {I J : Type*} [Fintype I] [Fintype J]

/-- A relabeling of ordinary real coordinates. -/
def reindexCoordinates (e : J ≃ I) : (J → ℝ) ≃ₗ[ℝ] (I → ℝ) :=
  LinearEquiv.piCongrLeft ℝ (fun _ : I ↦ ℝ) e

theorem reindexCoordinates_measurePreserving (e : J ≃ I) :
    MeasurePreserving (reindexCoordinates e) volume volume :=
  volume_measurePreserving_piCongrLeft (fun _ : I ↦ ℝ) e

/-- The shear keeps the first block and adds a real linear function of it to
the second block. No integrality of the coordinate function is needed. -/
def coordinateShear (q : (I → ℝ) →ₗ[ℝ] (J → ℝ)) :
    (I ⊕ J → ℝ) ≃ₗ[ℝ] (I ⊕ J → ℝ) where
  toFun x := Sum.elim (fun i ↦ x (Sum.inl i))
    (fun j ↦ x (Sum.inr j) + q (fun i ↦ x (Sum.inl i)) j)
  invFun x := Sum.elim (fun i ↦ x (Sum.inl i))
    (fun j ↦ x (Sum.inr j) - q (fun i ↦ x (Sum.inl i)) j)
  left_inv x := by ext (i | j); rfl; simp
  right_inv x := by ext (i | j); rfl; simp
  map_add' x y := by
    ext (i | j)
    · rfl
    · change _ + q ((fun i ↦ x (Sum.inl i)) + (fun i ↦ y (Sum.inl i))) j = _
      rw [map_add]
      simp only [Pi.add_apply, Sum.elim_inr]
      ring
  map_smul' r x := by
    ext (i | j)
    · rfl
    · change r * _ + q (r • (fun i ↦ x (Sum.inl i))) j = _
      rw [map_smul]
      simp only [Pi.smul_apply, smul_eq_mul, Sum.elim_inr, RingHom.id_apply]
      ring

theorem coordinateShear_matrix (q : (I → ℝ) →ₗ[ℝ] (J → ℝ)) :
    LinearMap.toMatrix' (coordinateShear q).toLinearMap =
      Matrix.fromBlocks 1 0 (LinearMap.toMatrix' q) 1 := by
  ext (i | j) (i' | j')
  · simp [LinearMap.toMatrix'_apply, coordinateShear, Pi.single_apply, Matrix.one_apply]
  · simp [LinearMap.toMatrix'_apply, coordinateShear, Pi.single_apply]
  · simp only [LinearMap.toMatrix'_apply, coordinateShear, LinearMap.coe_mk,
      AddHom.coe_mk, Sum.elim_inr, Matrix.fromBlocks_apply₂₁, Pi.single_apply,
      Sum.inr_ne_inl, ↓reduceIte, zero_add, Sum.inl.injEq]
    have he : (fun i : I ↦ if i = i' then (1 : ℝ) else 0) = Pi.single i' 1 := by
      ext i
      simp [Pi.single_apply]
    rw [he]
  · simp [LinearMap.toMatrix'_apply, coordinateShear, Pi.single_apply, Matrix.one_apply,
      show (fun _ : I ↦ (0 : ℝ)) = 0 from rfl]

/-- Its ordinary determinant is exactly one in every dimension. -/
theorem coordinateShear_det (q : (I → ℝ) →ₗ[ℝ] (J → ℝ)) :
    LinearMap.det (coordinateShear q).toLinearMap = 1 := by
  rw [← LinearMap.det_toMatrix', coordinateShear_matrix, Matrix.det_fromBlocks_zero₁₂]
  simp

theorem coordinateShear_measurePreserving (q : (I → ℝ) →ₗ[ℝ] (J → ℝ)) :
    MeasurePreserving (coordinateShear q) volume volume where
  measurable := (coordinateShear q).continuous_of_finiteDimensional.measurable
  map_eq := by
    change MeasureTheory.Measure.map (coordinateShear q).toLinearMap volume = volume
    have h := Real.map_linearMap_volume_pi_eq_smul_volume_pi
      (show LinearMap.det (coordinateShear q).toLinearMap ≠ 0 by
        rw [coordinateShear_det]; norm_num)
    simpa only [coordinateShear_det, abs_one, inv_one, ENNReal.ofReal_one, one_smul] using h

/-- Doubling all real coordinates. -/
def doubleCoordinates : (I → ℝ) ≃ₗ[ℝ] (I → ℝ) where
  toFun x := (2 : ℝ) • x
  invFun x := (1 / 2 : ℝ) • x
  left_inv x := by simp [smul_smul]
  right_inv x := by simp [smul_smul]
  map_add' x y := smul_add _ _ _
  map_smul' r x := by simp [smul_smul, mul_comm]

/-- The independently specified lattice with every coordinate doubled. -/
abbrev doubledLattice (L : Submodule ℤ (I → ℝ)) :=
  ZLattice.comap ℝ L (doubleCoordinates (I := I)).symm.toLinearMap

instance doubledLattice_discrete (L : Submodule ℤ (I → ℝ)) [DiscreteTopology L] :
    DiscreteTopology (doubledLattice L) :=
  ZLattice.comap_discreteTopology ℝ L
    (doubleCoordinates (I := I)).symm.continuous_of_finiteDimensional
    (doubleCoordinates (I := I)).symm.injective

instance doubledLattice_isZLattice (L : Submodule ℤ (I → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] : IsZLattice ℝ (doubledLattice L) :=
  instIsZLatticeComap ℝ L (doubleCoordinates (I := I)).symm.toContinuousLinearEquiv

/-- Ordinary Lebesgue covolume has precisely the expected `2^dimension` factor. -/
theorem doubledLattice_covolume (L : Submodule ℤ (I → ℝ))
    [DiscreteTopology L] [IsZLattice ℝ L] :
    ZLattice.covolume (doubledLattice L) =
      (2 : ℝ) ^ Fintype.card I * ZLattice.covolume L := by
  let b := IsZLattice.basis L
  rw [ZLattice.covolume_eq_det _ (b.ofZLatticeComap ℝ L doubleCoordinates.symm),
    ZLattice.covolume_eq_det L b]
  have he : Matrix.of (fun i ↦ ((b.ofZLatticeComap ℝ L doubleCoordinates.symm i :
      doubledLattice L) : I → ℝ)) = (2 : ℝ) • Matrix.of (fun i ↦ ((b i : L) : I → ℝ)) := by
    ext i j
    simp only [Matrix.of_apply, Module.Basis.ofZLatticeComap_apply,
      LinearEquiv.symm_symm, Matrix.smul_apply, smul_eq_mul]
    rfl
  change |(Matrix.of (fun i ↦ ((b.ofZLatticeComap ℝ L doubleCoordinates.symm i :
    doubledLattice L) : I → ℝ))).det| = _
  rw [he, Matrix.det_smul, abs_mul, abs_pow]
  norm_num
  rfl

end UnitDistance.RelativeUnits
