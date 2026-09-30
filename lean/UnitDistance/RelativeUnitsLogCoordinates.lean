module

public import UnitDistance.RelativeUnitsDifferenceLattice
public import UnitDistance.LatticeExactSequence

@[expose] public section
set_option backward.privateInPublic true


/-!
# Changing the deleted coordinate of the ordinary unit logarithm

The weighted product formula supplies the deleted coordinate. Thus deletion
at any actual infinite place gives the same ordinary regulator.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField Classical
open NumberField NumberField.InfinitePlace NumberField.Units
open NumberField.Units.dirichletUnitTheorem

namespace UnitDistance.RelativeUnits

section Coordinates

variable {A : Type*} [Fintype A]

/-- Fill the deleted coordinate so that the total coordinate sum is zero. -/
def fillDeleted (a : A) : ({x : A // x ≠ a} → ℝ) →ₗ[ℝ] (A → ℝ) where
  toFun f x := if h : x = a then -∑ y, f y else f ⟨x, h⟩
  map_add' f g := by
    ext x
    by_cases h : x = a <;> simp [h, Finset.sum_add_distrib, add_comm]
  map_smul' r f := by
    ext x
    by_cases h : x = a <;> simp [h, Finset.mul_sum]

@[simp] theorem fillDeleted_apply_ne (a : A) (f : {x : A // x ≠ a} → ℝ)
    (x : {x : A // x ≠ a}) : fillDeleted a f x.val = f x := by
  simp [fillDeleted, x.prop]

@[simp] theorem sum_fillDeleted (a : A) (f : {x : A // x ≠ a} → ℝ) :
    ∑ x, fillDeleted a f x = 0 := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ a]
  simp only [fillDeleted_apply_ne]
  simp [fillDeleted]

/-- A zero-sum vector is recovered from all but any one of its coordinates. -/
theorem fillDeleted_restrict (a : A) (f : A → ℝ) (hf : ∑ x, f x = 0) :
    fillDeleted a (fun x ↦ f x.val) = f := by
  ext x
  by_cases hx : x = a
  · subst x
    have h := Fintype.sum_eq_add_sum_subtype_ne f a
    rw [hf] at h
    simp only [fillDeleted, LinearMap.coe_mk, AddHom.coe_mk]
    split_ifs <;> linarith
  · simp [fillDeleted, hx]

/-- The canonical real linear change between two deleted-coordinate spaces. -/
def deletedCoordinateEquiv (a b : A) :
    ({x : A // x ≠ a} → ℝ) ≃ₗ[ℝ] ({x : A // x ≠ b} → ℝ) where
  toFun f x := fillDeleted a f x.val
  invFun f x := fillDeleted b f x.val
  left_inv f := by
    have h := fillDeleted_restrict b (fillDeleted a f) (sum_fillDeleted a f)
    ext x
    exact (congrFun h x.val).trans (fillDeleted_apply_ne a f x)
  right_inv f := by
    have h := fillDeleted_restrict a (fillDeleted b f) (sum_fillDeleted b f)
    ext x
    exact (congrFun h x.val).trans (fillDeleted_apply_ne b f x)
  map_add' f g := by ext x; exact congrFun (map_add (fillDeleted a) f g) x.val
  map_smul' r f := by ext x; exact congrFun (map_smul (fillDeleted a) r f) x.val

end Coordinates

variable (K : Type) [Field K] [NumberField K]

/-- The actual weighted unit logarithm, with an arbitrary actual place deleted. -/
def deletedUnitLog (v : InfinitePlace K) :
    Additive (𝓞 K)ˣ →+ ({w : InfinitePlace K // w ≠ v} → ℝ) where
  toFun u w := (mult w.val : ℝ) * Real.log (w.val u.toMul)
  map_zero' := by ext w; simp
  map_add' u t := by
    ext w
    simp [Real.log_mul (Units.pos_at_place _ _).ne' (Units.pos_at_place _ _).ne', mul_add]

theorem fillDeleted_logEmbedding (u : Additive (𝓞 K)ˣ) :
    fillDeleted (w₀ : InfinitePlace K) (logEmbedding K u) =
      fun w : InfinitePlace K ↦ (mult w : ℝ) * Real.log (w (u.toMul : K)) := by
  exact fillDeleted_restrict _ _ (Units.sum_mult_mul_log u.toMul)

@[simp] theorem deletedCoordinateEquiv_logEmbedding (v : InfinitePlace K)
    (u : Additive (𝓞 K)ˣ) :
    deletedCoordinateEquiv (w₀ : InfinitePlace K) v (logEmbedding K u) =
      deletedUnitLog K v u := by
  ext w
  exact congrFun (fillDeleted_logEmbedding K u) w.val

@[simp] theorem deletedUnitLog_eq_zero_iff (v : InfinitePlace K)
    (u : Additive (𝓞 K)ˣ) : deletedUnitLog K v u = 0 ↔ u.toMul ∈ torsion K := by
  rw [← deletedCoordinateEquiv_logEmbedding, LinearEquiv.map_eq_zero_iff]
  exact dirichletUnitTheorem.logEmbedding_eq_zero_iff

/-- The ordinary unit lattice, written after deleting the specified place. -/
abbrev deletedUnitLattice (v : InfinitePlace K) :
    Submodule ℤ ({w : InfinitePlace K // w ≠ v} → ℝ) :=
  ZLattice.comap ℝ (unitLattice K)
    (deletedCoordinateEquiv (w₀ : InfinitePlace K) v).symm.toLinearMap

instance deletedUnitLattice_discrete (v : InfinitePlace K) :
    DiscreteTopology (deletedUnitLattice K v) := by
  exact ZLattice.comap_discreteTopology ℝ (unitLattice K)
    (deletedCoordinateEquiv (w₀ : InfinitePlace K) v).symm.continuous_of_finiteDimensional
    (deletedCoordinateEquiv (w₀ : InfinitePlace K) v).symm.injective

instance deletedUnitLattice_isZLattice (v : InfinitePlace K) :
    IsZLattice ℝ (deletedUnitLattice K v) := by
  exact instIsZLatticeComap ℝ (unitLattice K)
    (deletedCoordinateEquiv (w₀ : InfinitePlace K) v).symm.toContinuousLinearEquiv

theorem mem_deletedUnitLattice (v : InfinitePlace K)
    (x : {w : InfinitePlace K // w ≠ v} → ℝ) :
    x ∈ deletedUnitLattice K v ↔ ∃ u, deletedUnitLog K v u = x := by
  constructor
  · rintro ⟨u, _, hu⟩
    change logEmbedding K u = (deletedCoordinateEquiv (w₀ : InfinitePlace K) v).symm x at hu
    refine ⟨u, ?_⟩
    rw [← deletedCoordinateEquiv_logEmbedding, hu, LinearEquiv.apply_symm_apply]
  · rintro ⟨u, rfl⟩
    change (deletedCoordinateEquiv (w₀ : InfinitePlace K) v).symm
      (deletedUnitLog K v u) ∈ unitLattice K
    rw [← deletedCoordinateEquiv_logEmbedding, LinearEquiv.symm_apply_apply]
    exact ⟨u, Submodule.mem_top, rfl⟩

/-- The actual ordinary regulator is unchanged by the choice of deleted place. -/
theorem deletedUnitLattice_covolume (v : InfinitePlace K) :
    ZLattice.covolume (deletedUnitLattice K v) = regulator K := by
  let e : {w : InfinitePlace K // w ≠ v} ≃ Fin (rank K) :=
    Fintype.equivOfCardEq (by
      rw [Fintype.card_fin, rank, Fintype.card_subtype_compl, Fintype.card_subtype_eq])
  let b := ((basisUnitLattice K).ofZLatticeComap ℝ (unitLattice K)
    (deletedCoordinateEquiv (w₀ : InfinitePlace K) v).symm).reindex e.symm
  rw [ZLattice.covolume_eq_det (deletedUnitLattice K v) b, regulator_eq_det K v e]
  congr 2
  ext i w
  simp only [b, Matrix.of_apply, Function.comp_apply, Module.Basis.reindex_apply,
    Equiv.symm_symm]
  rw [Module.Basis.ofZLatticeComap_apply, LinearEquiv.symm_symm,
    ← logEmbedding_fundSystem, deletedCoordinateEquiv_logEmbedding]
  rfl

end UnitDistance.RelativeUnits
