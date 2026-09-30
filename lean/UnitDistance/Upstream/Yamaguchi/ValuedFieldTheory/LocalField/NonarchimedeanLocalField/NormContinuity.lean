/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NormUnits
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Instances.Matrix

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Continuity of finite field norms

This module records the analytic input used by the topological finite local
reciprocity law: on a finite-dimensional normed algebra, the field norm is a
determinant and is therefore continuous.  It also bundles the corresponding
statements for field units and valuation-ring units.
-/

noncomputable section

universe u v

namespace LocalFieldTheory

open scoped ValuativeRel
open _root_.LocalFieldTheory.IsNonarchimedeanLocalField

/-- The field norm of a finite-dimensional normed algebra over a complete
nontrivially normed field is continuous. -/
theorem algebraNorm_continuous_of_finiteDimensional
    (K : Type u) (L : Type v)
    [NontriviallyNormedField K] [NormedField L]
    [Algebra K L] [FiniteDimensional K L] [CompleteSpace K]
    [ContinuousSMul K L] :
    Continuous (Algebra.norm K : L → K) := by
  classical
  let b := Module.Free.chooseBasis K L
  rw [show (Algebra.norm K : L → K) =
      fun x => (Algebra.leftMulMatrix b x).det by
    funext x
    exact Algebra.norm_eq_matrix_det b x]
  apply Continuous.matrix_det
  exact (Algebra.leftMulMatrix b).toLinearMap.continuous_of_finiteDimensional

/-- The field norm induced on unit groups is continuous. -/
theorem normUnits_continuous_of_finiteDimensional
    (K : Type u) (L : Type v)
    [NontriviallyNormedField K] [NormedField L]
    [Algebra K L] [FiniteDimensional K L] [CompleteSpace K]
    [ContinuousSMul K L] :
    Continuous (normUnits K L) := by
  unfold normUnits
  exact Continuous.units_map (Algebra.norm K : L →* K)
    (algebraNorm_continuous_of_finiteDimensional K L)

/-- The canonical inclusion from valuation-ring units to field units is
continuous for the subtype topologies. -/
theorem integerUnitsToFieldUnits_continuous
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] :
    Continuous (integerUnitsToFieldUnits K) := by
  unfold IsNonarchimedeanLocalField.integerUnitsToFieldUnits
  exact Continuous.units_map
    ((algebraMap 𝒪[K] K).toMonoidHom) continuous_subtype_val

end LocalFieldTheory
