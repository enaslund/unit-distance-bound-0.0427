/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch. The Mathlib
4.35 Denumerable import relocation is recorded in
third-party/yamaguchi/lean-v4.35-migration.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.Valuation.DiscreteValuationField.Extensions
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.RingTheory.RamificationInertia.Basic

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Defectlessness from a finite extension of valuation rings

The local Dedekind fundamental identity only needs discretely valued fields.
Completeness and Henselianity play no role once the target valuation ring is a
finite module over the base valuation ring.
-/

noncomputable section

namespace ValuationTheory.DiscreteValuationField.ValuedExtension

universe u v w x

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]

/-- A valued extension of discretely valued fields is defectless when its
target valuation ring is finite over the base valuation ring. -/
theorem isDefectless_of_moduleFinite
    (base : DVF.{u, v} K) (target : DVF.{w, x} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    [IsScalarTower base.valuationSubring target.valuationSubring L] :
    IsDefectless base target := by
  classical
  let : FaithfulSMul base.valuationSubring target.valuationSubring :=
    FaithfulSMul.of_field_isFractionRing
      base.valuationSubring target.valuationSubring K L
  have hprimes :=
    IsLocalRing.primesOver_eq target.valuationSubring base.maximalIdeal_ne_bot
  have hq : target.maximalIdeal ∈ base.maximalIdeal.primesOver target.valuationSubring := by
    rw [hprimes]
    exact Set.mem_singleton target.maximalIdeal
  let : target.maximalIdeal.LiesOver base.maximalIdeal := hq.2
  let : Subsingleton (base.maximalIdeal.primesOver target.valuationSubring) :=
    Set.Subsingleton.coe_sort (by
      rw [hprimes]
      exact Set.subsingleton_singleton)
  have hsum :=
    Ideal.sum_ramification_inertia_eq_finrank base.maximalIdeal target.valuationSubring
  rw [Fintype.sum_subsingleton _ ⟨target.maximalIdeal, hq⟩] at hsum
  unfold IsDefectless degree ramificationIndex residueDegree
  rw [Ideal.ramificationIdx'_eq_ramificationIdx
    base.maximalIdeal target.maximalIdeal base.maximalIdeal_ne_bot]
  rw [Algebra.IsAlgebraic.finrank_of_isFractionRing
    base.valuationSubring K target.valuationSubring L]
  exact hsum.symm

end ValuationTheory.DiscreteValuationField.ValuedExtension

end
