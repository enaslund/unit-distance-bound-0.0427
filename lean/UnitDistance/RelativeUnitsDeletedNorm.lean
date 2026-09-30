module

public import UnitDistance.RelativeUnitsLogCoordinates

@[expose] public section
set_option backward.privateInPublic true


/-! # The actual norm-image covolume with any base place deleted -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField Classical
open NumberField NumberField.InfinitePlace NumberField.Units
open NumberField.Units.dirichletUnitTheorem

namespace UnitDistance.RelativeUnits

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K]

/-- The actual norm-image lattice in a specified deleted-coordinate system. -/
abbrev deletedNormImageLattice (v : InfinitePlace F) :=
  ZLattice.comap ℝ (normImageLogLattice (F := F) (K := K))
    (deletedCoordinateEquiv (w₀ : InfinitePlace F) v).symm.toLinearMap

instance deletedNormImageLattice_discrete (v : InfinitePlace F) :
    DiscreteTopology (deletedNormImageLattice (K := K) v) :=
  ZLattice.comap_discreteTopology ℝ (normImageLogLattice (F := F) (K := K))
    (deletedCoordinateEquiv (w₀ : InfinitePlace F) v).symm.continuous_of_finiteDimensional
    (deletedCoordinateEquiv (w₀ : InfinitePlace F) v).symm.injective

instance deletedNormImageLattice_isZLattice (v : InfinitePlace F) :
    IsZLattice ℝ (deletedNormImageLattice (K := K) v) :=
  instIsZLatticeComap ℝ (normImageLogLattice (F := F) (K := K))
    (deletedCoordinateEquiv (w₀ : InfinitePlace F) v).symm.toContinuousLinearEquiv

theorem mem_deletedNormImageLattice (v : InfinitePlace F)
    (x : {w : InfinitePlace F // w ≠ v} → ℝ) :
    x ∈ deletedNormImageLattice (K := K) v ↔
      ∃ u : Additive (𝓞 K)ˣ, deletedUnitLog F v ((unitNorm (F := F)).toAdditive u) = x := by
  change (deletedCoordinateEquiv (w₀ : InfinitePlace F) v).symm x ∈
    (normImageLogLattice (F := F) (K := K)).toAddSubgroup ↔ _
  rw [normImageLogLattice_toAddSubgroup]
  constructor
  · rintro ⟨t, ⟨u, hu⟩, ht⟩
    refine ⟨Additive.ofMul u, ?_⟩
    rw [← deletedCoordinateEquiv_logEmbedding]
    have he : (unitNorm (F := F)).toAdditive (Additive.ofMul u) = t := hu
    rw [he, ht, LinearEquiv.apply_symm_apply]
  · rintro ⟨u, rfl⟩
    refine ⟨(unitNorm (F := F)).toAdditive u, ⟨u.toMul, rfl⟩, ?_⟩
    rw [← deletedCoordinateEquiv_logEmbedding, LinearEquiv.symm_apply_apply]

/-- Changing the deleted coordinate preserves the index ratio of the actual
norm lattice and the actual full unit lattice. -/
theorem deletedNormImageLattice_covolume_div_regulator (v : InfinitePlace F) :
    ZLattice.covolume (deletedNormImageLattice (K := K) v) / regulator F =
      (logarithmicNormIndex (F := F) (K := K) : ℝ) := by
  rw [← normImageLogLattice_covolume_div_regulator (F := F) (K := K)]
  conv_lhs => rw [← deletedUnitLattice_covolume F v]
  conv_rhs => rw [regulator]
  rw [ZLattice.covolume_div_covolume_eq_relIndex
      (deletedNormImageLattice (K := K) v) (deletedUnitLattice F v)
      (Submodule.comap_mono normImageLogLattice_le),
    ZLattice.covolume_div_covolume_eq_relIndex
      (normImageLogLattice (F := F) (K := K)) (unitLattice F) normImageLogLattice_le]
  congr 1
  change ((normImageLogLattice (F := F) (K := K)).toAddSubgroup.comap
      (deletedCoordinateEquiv (w₀ : InfinitePlace F) v).symm.toLinearMap.toAddMonoidHom).relIndex
    ((unitLattice F).toAddSubgroup.comap
      (deletedCoordinateEquiv (w₀ : InfinitePlace F) v).symm.toLinearMap.toAddMonoidHom) = _
  rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq]
  rw [AddMonoidHom.range_eq_top.mpr
    (deletedCoordinateEquiv (w₀ : InfinitePlace F) v).symm.surjective, top_inf_eq]

/-- The actual norm-image covolume `(I_U/2) R_F`, in any deleted-place coordinates. -/
theorem deletedNormImageLattice_covolume [IsTotallyComplex K]
    (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (hb : 0 < nrRealPlaces F) (v : InfinitePlace F) :
    ZLattice.covolume (deletedNormImageLattice (K := K) v) =
      ((normUnitImage (F := F) (K := K)).index : ℝ) / 2 * regulator F := by
  have h := deletedNormImageLattice_covolume_div_regulator (K := K) v
  obtain ⟨ρ, σ, hbase, hconj⟩ := exists_complexifying_embeddings ι hι hb
  have hi := unitNorm_index_eq_two_mul_logarithmicNormIndex ι hι ρ σ hbase hconj
  rw [hi, Nat.cast_mul, Nat.cast_ofNat]
  apply (div_eq_iff (regulator_pos F).ne').mp at h
  nlinarith

end UnitDistance.RelativeUnits
