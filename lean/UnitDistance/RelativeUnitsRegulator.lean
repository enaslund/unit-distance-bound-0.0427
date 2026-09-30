module

public import UnitDistance.RelativeUnitsRegulatorLattice
public import UnitDistance.RelativeUnitsDeletedNorm

@[expose] public section
set_option backward.privateInPublic true


/-!
# The actual relative regulator identity

The kernel and image in the coordinate exact sequence are identified with
the doubled actual unweighted relative lattice and the actual norm lattice.
There is no assumed regulator, covolume, or logarithmic exactness identity.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField Classical
open NumberField NumberField.InfinitePlace NumberField.Units
open UnitDistance.LatticeExactSequence

namespace UnitDistance.RelativeUnits

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K] [IsTotallyComplex K]

/-- The kernel in the manuscript's actual coordinates is equivalent to the
actual roots of unity, with norm one proved from the field signature. -/
def differenceLogKernelEquivTorsion (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (hb : 0 < nrRealPlaces F) :
    (relativeDifferenceLog ι).toIntLinearMap.ker ≃ torsion K where
  toFun u := ⟨u.val.toMul.val, (relativeDifferenceLog_eq_zero_iff ι hι u.val).mp u.prop⟩
  invFun ζ :=
    ⟨Additive.ofMul ⟨ζ.val, torsion_le_normOneUnits_of_totallyComplex ι hι hb ζ.prop⟩,
      (relativeDifferenceLog_eq_zero_iff ι hι _).mpr ζ.prop⟩
  left_inv u := by rfl
  right_inv ζ := by rfl

/-- There are exactly `w_K` units in the kernel of the actual relative
difference map, the multiplicity used in the geometric mass. -/
theorem relativeDifferenceLog_ker_card (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (hb : 0 < nrRealPlaces F) :
    Nat.card (relativeDifferenceLog ι).toIntLinearMap.ker = torsionOrder K := by
  rw [Nat.card_congr (differenceLogKernelEquivTorsion ι hι hb)]
  rfl

/-- Every point of the actual difference lattice has exactly `w_K` actual
relative-unit preimages, not only the zero point. -/
theorem relativeDifferenceLog_fiber_card (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (hb : 0 < nrRealPlaces F) (x : differenceLattice ι) :
    Nat.card {u : Additive (normOneUnits (F := F) (K := K)) |
      relativeDifferenceLog ι u = x.val} = torsionOrder K := by
  obtain ⟨u₀, hu₀⟩ := x.prop
  change relativeDifferenceLog ι u₀ = x.val at hu₀
  let e : {u : Additive (normOneUnits (F := F) (K := K)) |
      relativeDifferenceLog ι u = x.val} ≃ (relativeDifferenceLog ι).toIntLinearMap.ker :=
    { toFun := fun u ↦ ⟨u.val - u₀, by
        change relativeDifferenceLog ι (u.val - u₀) = 0
        rw [map_sub, u.prop, hu₀, sub_self]⟩
      invFun := fun u ↦ ⟨u.val + u₀, by
        have hu : relativeDifferenceLog ι u.val = 0 := u.prop
        change relativeDifferenceLog ι (u.val + u₀) = x.val
        rw [map_add, hu, hu₀, zero_add]⟩
      left_inv := fun u ↦ Subtype.ext (sub_add_cancel u.val u₀)
      right_inv := fun u ↦ Subtype.ext (add_sub_cancel_right u.val u₀) }
  rw [Nat.card_congr e]
  exact relativeDifferenceLog_ker_card ι hι hb

/-- Projection of the actual transformed full unit lattice is exactly the
actual norm-image lattice, in the specified deleted base coordinates. -/
theorem pairedUnitLattice_image (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (v : {w : InfinitePlace F // IsReal w}) :
    imageLattice (pairedUnitLattice ι hι v) = deletedNormImageLattice (K := K) v.val := by
  ext x
  rw [mem_deletedNormImageLattice]
  constructor
  · rintro ⟨y, hy, hyx⟩
    obtain ⟨u, rfl⟩ := (mem_pairedUnitLattice ι hι v y).mp hy
    exact ⟨u, hyx⟩
  · rintro ⟨u, rfl⟩
    exact ⟨pairedUnitLog v.val u, (mem_pairedUnitLattice ι hι v _).mpr ⟨u, rfl⟩, rfl⟩

/-- In the coordinate kernel, each first weighted place coordinate is twice
the manuscript's actual unweighted relative difference coordinate. -/
theorem pairedUnitLattice_kernel (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (v : {w : InfinitePlace F // IsReal w}) :
    kernelLattice (pairedUnitLattice ι hι v) = doubledLattice (differenceLattice ι) := by
  have hb : 0 < nrRealPlaces F := Fintype.card_pos_iff.mpr ⟨v⟩
  obtain ⟨ρ, σ, hbase, hconj⟩ := exists_complexifying_embeddings ι hι hb
  ext x
  change leftEmbed x ∈ pairedUnitLattice ι hι v ↔
    (1 / 2 : ℝ) • x ∈ differenceLattice ι
  rw [mem_pairedUnitLattice]
  constructor
  · rintro ⟨u, hu⟩
    have hn : deletedUnitLog F v.val ((unitNorm (F := F)).toAdditive u) = 0 := by
      ext w
      exact congrFun hu (Sum.inr w)
    have ht := (deletedUnitLog_eq_zero_iff F v.val _).mp hn
    have hnu : unitNorm (F := F) u.toMul = 1 :=
      norm_torsion_eq_one ι hι ρ σ hbase hconj u.toMul ht
    let t : Additive (normOneUnits (F := F) (K := K)) := Additive.ofMul ⟨u.toMul, hnu⟩
    refine ⟨t, ?_⟩
    ext w
    rw [AddMonoidHom.coe_toIntLinearMap, relativeDifferenceLog_apply ι hι]
    have hw := congrFun hu (Sum.inl w)
    change (2 : ℝ) * Real.log (chosenPlaceAbove (K := K) w.val u.toMul) = x w at hw
    change Real.log (chosenPlaceAbove (K := K) w.val u.toMul) = (1 / 2 : ℝ) * x w
    linarith
  · rintro ⟨u, hu⟩
    refine ⟨Additive.ofMul u.toMul.val, ?_⟩
    ext (w | w)
    · have hw := congrFun hu w
      change relativeDifferenceLog ι u w = (1 / 2 : ℝ) * x w at hw
      rw [relativeDifferenceLog_apply ι hι] at hw
      change (2 : ℝ) * Real.log (chosenPlaceAbove (K := K) w.val u.toMul.val) = x w
      linarith
    · change deletedUnitLog F v.val
        (Additive.ofMul (unitNorm (F := F) u.toMul.val)) w = 0
      rw [show unitNorm (F := F) u.toMul.val = 1 from u.toMul.prop]
      exact congrFun (map_zero (deletedUnitLog F v.val)) w

/-- The ordinary full regulator is the product of the actual kernel and norm
image covolumes. This version includes `c = 0` without truncated subtraction. -/
theorem regulator_eq_relativeRegulator_mul_normIndex
    (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (hb : 0 < nrRealPlaces F) :
    regulator K = (2 : ℝ) ^ nrComplexPlaces F * relativeRegulator ι *
      (((normUnitImage (F := F) (K := K)).index : ℝ) / 2 * regulator F) := by
  obtain ⟨v⟩ := Fintype.card_pos_iff.mp hb
  letI := differenceLattice_discrete ι hι
  letI := differenceLattice_isZLattice ι hι
  letI : DiscreteTopology (imageLattice (pairedUnitLattice ι hι v)) := by
    rw [pairedUnitLattice_image]
    infer_instance
  rw [← pairedUnitLattice_covolume ι hι v,
    covolume_eq_kernel_mul_image, pairedUnitLattice_kernel, pairedUnitLattice_image,
    doubledLattice_covolume, deletedNormImageLattice_covolume ι hι hb]
  rfl

/-- The manuscript's actual relative regulator identity, written as `2^c/2`
so that the zero-dimensional convention is included literally. -/
theorem regulator_div_regulator_eq
    (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (hb : 0 < nrRealPlaces F) :
    regulator K / regulator F = (2 : ℝ) ^ nrComplexPlaces F / 2 *
      ((normUnitImage (F := F) (K := K)).index : ℝ) * relativeRegulator ι := by
  rw [regulator_eq_relativeRegulator_mul_normIndex ι hι hb]
  field_simp [regulator_ne_zero F]

/-- The same identity with the literal integer exponent `c - 1`. -/
theorem regulator_div_regulator_eq_zpow
    (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (hb : 0 < nrRealPlaces F) :
    regulator K / regulator F = (2 : ℝ) ^ ((nrComplexPlaces F : ℤ) - 1) *
      ((normUnitImage (F := F) (K := K)).index : ℝ) * relativeRegulator ι := by
  rw [zpow_natCast_sub_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
  exact regulator_div_regulator_eq ι hι hb

end UnitDistance.RelativeUnits
