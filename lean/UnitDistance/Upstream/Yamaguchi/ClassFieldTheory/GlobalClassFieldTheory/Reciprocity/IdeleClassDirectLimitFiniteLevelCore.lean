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

public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitCore
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerBaseChange
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.Ramification.GaloisValuation.ClosedFixingSubgroup
public import Mathlib.GroupTheory.QuotientGroup.Defs

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Finite levels of the rational idele-class direct limit

Normal closures, finite-level scalar extension, tower base change, and the
canonical embeddings into the rational idele-class direct limit.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open CyclicCohomology

attribute [local instance]
  relativeAdeleRingIntermediateAlgebra

local instance rationalIntermediateNumberField
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] : NumberField K :=
  NumberField.of_module_finite ℚ K

instance rationalTowerClassGroupCommGroup
    (K N : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ N]
    [Algebra K N] [IsScalarTower ℚ K N] [FiniteDimensional K N] :
    CommGroup (TowerRelativeIdeleGroup.ClassGroup ℚ K N) := by
  letI : CommGroup (TowerRelativeIdeleGroup ℚ K N) := inferInstance
  exact
    QuotientGroup.Quotient.commGroup
      (TowerRelativeIdeleGroup.principalSubgroup ℚ K N)

instance rationalTowerClassGroupMul
    (K N : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ N]
    [Algebra K N] [IsScalarTower ℚ K N] [FiniteDimensional K N] :
    Mul (TowerRelativeIdeleGroup.ClassGroup ℚ K N) := by
  letI : CommGroup (TowerRelativeIdeleGroup ℚ K N) := inferInstance
  exact
    (QuotientGroup.Quotient.commGroup
      (TowerRelativeIdeleGroup.principalSubgroup ℚ K N)).toMul

/-- The canonical finite Galois closure, inside `SeparableClosure ℚ`,
of a finite rational intermediate field. -/
noncomputable def rationalNormalClosure
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] :
    FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ) :=
  { IntermediateField.normalClosure
      ℚ K (SeparableClosure ℚ) with
    finiteDimensional :=
      normalClosure.is_finiteDimensional
        ℚ K (SeparableClosure ℚ)
    isGalois :=
      IsGalois.normalClosure ℚ K (SeparableClosure ℚ) }

/-- Absolute left cosets fixing a finite rational intermediate field,
identified with its embeddings into the canonical normal closure. -/
noncomputable def
    rationalBaseFixingCosetEquivNormalClosure
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] :
    ((RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ)
          (⊥ : IntermediateField ℚ (SeparableClosure ℚ))).toSubgroup ⧸
      extensionSubgroup
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ)
          (⊥ : IntermediateField ℚ (SeparableClosure ℚ)))
        (RamificationTheory.closedFixingSubgroup
          ℚ (SeparableClosure ℚ) K)
        (LocalClassFieldTheory.fixingSubgroupLeBase
          ℚ (SeparableClosure ℚ) K)) ≃
      (K →ₐ[ℚ] rationalNormalClosure K) :=
  (LocalClassFieldTheory.baseFixingCosetEquivAlgHom
      ℚ (SeparableClosure ℚ) K).trans
    (normalClosure.algHomEquiv
      (F := ℚ) (K := K) (L := SeparableClosure ℚ)).symm

/-- Embed the actual idele class group of a finite rational
intermediate field into the relative presentation at its canonical
finite Galois closure. -/
noncomputable def rationalIntermediateIdeleClassToNormalClosure
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] :
    IdeleClassGroup K →*
      RelativeIdeleGroup.ClassGroup ℚ (rationalNormalClosure K) :=
  (RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion (IntermediateField.le_normalClosure K))).comp
    (_root_.relativeIdeleClassBaseChangeMulEquiv
      (K := ℚ) (L := K)).symm.toMonoidHom

/-- The canonical map from the actual idele class group of a finite
rational intermediate field to the absolute idele-class direct limit. -/
noncomputable def rationalIntermediateIdeleClassToDirectLimit
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K] :
    IdeleClassGroup K →* rationalIdeleClassDirectLimit :=
  (rationalRelativeIdeleClassToDirectLimit
      (rationalNormalClosure K)).comp
    (rationalIntermediateIdeleClassToNormalClosure K)

/-- Passing from the relative presentation of a finite rational
intermediate field to its ordinary idele class group commutes with the
canonical map to the absolute direct limit. -/
theorem
    rationalIntermediateIdeleClassToDirectLimit_baseChange
    (K : IntermediateField ℚ (SeparableClosure ℚ))
    [FiniteDimensional ℚ K]
    (c : RelativeIdeleGroup.ClassGroup ℚ K) :
    rationalIntermediateIdeleClassToDirectLimit K
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := K) c) =
      rationalRelativeIdeleClassToDirectLimit
        (rationalNormalClosure K)
        (RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion (IntermediateField.le_normalClosure K)) c) := by
  simp only [rationalIntermediateIdeleClassToDirectLimit,
    rationalIntermediateIdeleClassToNormalClosure]
  change
    rationalRelativeIdeleClassToDirectLimit
        (rationalNormalClosure K)
        (RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion (IntermediateField.le_normalClosure K))
          ((_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := ℚ) (L := K)).symm
            (_root_.relativeIdeleClassBaseChangeMulEquiv
              (K := ℚ) (L := K) c))) =
      rationalRelativeIdeleClassToDirectLimit
        (rationalNormalClosure K)
        (RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion (IntermediateField.le_normalClosure K)) c)
  rw [(_root_.relativeIdeleClassBaseChangeMulEquiv
    (K := ℚ) (L := K)).symm_apply_apply]

/-- At a finite Galois rational intermediate field, the ordinary
idele-class comparison followed by the absolute direct-limit map is the
canonical finite-level map itself. -/
theorem
    rationalFiniteGaloisIdeleClassToDirectLimit_baseChange
    (E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ))
    (c : RelativeIdeleGroup.ClassGroup ℚ E) :
    rationalIntermediateIdeleClassToDirectLimit
        (E : IntermediateField ℚ (SeparableClosure ℚ))
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := E) c) =
      rationalRelativeIdeleClassToDirectLimit E c := by
  rw [rationalIntermediateIdeleClassToDirectLimit_baseChange]
  exact rationalIdeleClassDirectLimit_mk_apply c
    (IntermediateField.le_normalClosure
      (E : IntermediateField ℚ (SeparableClosure ℚ)))

set_option maxHeartbeats 1000000 in
/-- The canonical maps from nested rational intermediate fields to the
idele-class direct limit agree after scalar extension. -/
theorem
    rationalIntermediateIdeleClassToDirectLimit_extension
    {F E : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ F] [FiniteDimensional ℚ E]
    (hFE : F ≤ E)
    (c : RelativeIdeleGroup.ClassGroup ℚ F) :
    rationalIntermediateIdeleClassToDirectLimit E
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := E)
          (RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion hFE) c)) =
    rationalIntermediateIdeleClassToDirectLimit F
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := ℚ) (L := F) c) := by
  let hFN :
      F ≤ (rationalNormalClosure F :
        IntermediateField ℚ (SeparableClosure ℚ)) :=
    IntermediateField.le_normalClosure F
  let hEN :
      E ≤ (rationalNormalClosure E :
        IntermediateField ℚ (SeparableClosure ℚ)) :=
    IntermediateField.le_normalClosure E
  let hN : rationalNormalClosure F ≤ rationalNormalClosure E := by
    change IntermediateField.normalClosure ℚ F (SeparableClosure ℚ) ≤
      IntermediateField.normalClosure ℚ E (SeparableClosure ℚ)
    exact IntermediateField.normalClosure_mono (F := ℚ) (K := F) (K' := E)
      (L := SeparableClosure ℚ) hFE
  rw [
    rationalIntermediateIdeleClassToDirectLimit_baseChange E
      (RelativeIdeleGroup.classEmbedding
        (IntermediateField.inclusion hFE) c),
    rationalIntermediateIdeleClassToDirectLimit_baseChange F c]
  have hcomp :
      RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion hEN)
          (RelativeIdeleGroup.classEmbedding
            (IntermediateField.inclusion hFE) c) =
        RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion hN)
          (RelativeIdeleGroup.classEmbedding
            (IntermediateField.inclusion hFN) c) := by
    calc
      _ = RelativeIdeleGroup.classEmbedding
          (IntermediateField.inclusion (hFE.trans hEN)) c :=
        rationalRelativeIdeleClassEmbedding_comp hFE hEN c
      _ = RelativeIdeleGroup.classEmbedding
          (IntermediateField.inclusion (hFN.trans hN)) c := by
        congr 1
      _ = _ :=
        (rationalRelativeIdeleClassEmbedding_comp hFN hN c).symm
  erw [hcomp]
  exact rationalIdeleClassDirectLimit_mk_apply
    (RelativeIdeleGroup.classEmbedding
      (IntermediateField.inclusion hFN) c) hN


end Reciprocity
end GlobalClassFieldTheory
