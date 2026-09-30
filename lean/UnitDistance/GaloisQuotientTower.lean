/-
Copyright (c) 2026 The Erdős unit-distance formalization contributors.
Released under Apache 2.0 license as described in third-party/erdos-unit-distance/LICENSE.

Selected proof adaptation from logical-intelligence/erdos-unit-distance,
commit b6493074dd103ca32ea4f5e9b0bc9cb3a0379f2e,
ErdosUnitDistance/Internal/ClassFieldTheory/Witness.lean.
Local modifications: namespace/import port, separation from arithmetic
maximal-extension assumptions, and explicit actual-field family packaging.
See third-party/erdos-unit-distance/README.md for scope and provenance.
-/
module

public import UnitDistance.ProfiniteQuotientTower
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.Galois.Profinite

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual growing Galois fields from an infinite profinite quotient

Starting with an actual Galois extension and a continuous surjective map
from its actual automorphism group to an infinite profinite group, the
construction takes fixed fields of pulled-back open normal subgroups.
The resulting finite Galois field degrees tend to infinity. Arithmetic
realization, local ramification, splitting, and CM signatures are separate.

Adapted from the field-construction part of `cft_D2_infiniteQuotientTower`
in upstream `ErdosUnitDistance/Internal/ClassFieldTheory/Witness.lean`.
-/

noncomputable section
namespace UnitDistance.GaloisQuotient

variable (k K : Type*) [Field k] [Field K] [Algebra k K]
variable (Q : Type*) [Group Q]

/-- An actual nested sequence of finite Galois intermediate fields whose
fixing subgroups contain the kernel of the specified actual quotient map. -/
structure Family (φ : Gal(K/k) →* Q) where
  level : ℕ → IntermediateField k K
  finite : ∀ j, Module.Finite k (level j)
  galois : ∀ j, IsGalois k (level j)
  increasing : ∀ j, level j ≤ level (j+1)
  kernel_fixes : ∀ j, φ.ker ≤ (level j).fixingSubgroup
  degree_tendsto : Filter.Tendsto (fun j => Module.finrank k (level j)) Filter.atTop Filter.atTop


/-- Adjoining an independently given finite Galois retained field preserves
the actual growing family whenever the quotient kernel fixes that field. -/
def Family.adjoinRetained {φ : Gal(K/k) →* Q} (T : Family k K Q φ)
    (R : IntermediateField k K) [Module.Finite k R] [IsGalois k R]
    (hR : φ.ker ≤ R.fixingSubgroup) : Family k K Q φ where
  level j := T.level j ⊔ R
  finite j := by
    letI : Module.Finite k (T.level j) := T.finite j
    exact IntermediateField.finiteDimensional_sup (E1 := T.level j) (E2 := R)
  galois j := by
    letI : IsGalois k (T.level j) := T.galois j
    infer_instance
  increasing j := sup_le_sup_right (T.increasing j) R
  kernel_fixes j := by
    rw [IntermediateField.fixingSubgroup_sup]
    exact le_inf (T.kernel_fixes j) hR
  degree_tendsto := by
    apply Filter.tendsto_atTop_mono (f := fun j => Module.finrank k (T.level j))
    · intro j
      letI : Module.Finite k (T.level j) := T.finite j
      letI : Module.Finite k (T.level j ⊔ R : IntermediateField k K) :=
        IntermediateField.finiteDimensional_sup (E1 := T.level j) (E2 := R)
      exact IntermediateField.finrank_le_of_le_right (F := T.level j) (E := T.level j ⊔ R) le_sup_left
    · exact T.degree_tendsto

/-- Every field of the constructed retained family contains the actual
specified retained intermediate field. -/
theorem Family.retained_le {φ : Gal(K/k) →* Q} (T : Family k K Q φ)
    (R : IntermediateField k K) [Module.Finite k R] [IsGalois k R]
    (hR : φ.ker ≤ R.fixingSubgroup) (j : ℕ) :
    R ≤ (Family.adjoinRetained k K Q T R hR).level j := le_sup_right

variable [IsGalois k K]
variable [TopologicalSpace Q] [IsTopologicalGroup Q] [T2Space Q] [CompactSpace Q]
  [TotallyDisconnectedSpace Q] [Infinite Q]

/-- This supplies actual fields, rather than an assigned sequence of
extension degrees, from the independently stated profinite quotient data. -/
theorem exists_family (φ : Gal(K/k) →* Q)
    (hφ : Function.Surjective φ) (hcontinuous : Continuous φ) :
    Nonempty (Family k K Q φ) := by
  classical
  obtain ⟨U,hU0,hUmono,hUtendsto⟩ := ProfiniteQuotient.openNormalChain Q
  let N : ℕ → Subgroup (Gal(K/k)) := fun j => (U j).toSubgroup.comap φ
  have hNnormal : ∀ j, (N j).Normal := by intro j; dsimp [N]; infer_instance
  have hNopen : ∀ j, IsOpen (N j : Set (Gal(K/k))) := by
    intro j
    let V : OpenSubgroup (Gal(K/k)) := OpenSubgroup.comap φ hcontinuous (U j).toOpenSubgroup
    simpa [N,V,OpenSubgroup.toSubgroup_comap] using V.isOpen
  let H : ℕ → ClosedSubgroup (Gal(K/k)) := fun j =>
    { toSubgroup := N j
      isClosed' := Subgroup.isClosed_of_isOpen (N j) (hNopen j) }
  let L : ℕ → IntermediateField k K := fun j => IntermediateField.fixedField (H j).toSubgroup
  have hLfix : ∀ j, (L j).fixingSubgroup = N j := by
    intro j
    simpa [L,H] using InfiniteGalois.fixingSubgroup_fixedField (k := k) (K := K) (H j)
  have hLfin_gal : ∀ j, Module.Finite k (L j) ∧ IsGalois k (L j) := by
    intro j
    have hopen : IsOpen ((L j).fixingSubgroup : Set (Gal(K/k))) := by
      rw [hLfix]; exact hNopen j
    have hnormal : (L j).fixingSubgroup.Normal := by
      rw [hLfix]; exact hNnormal j
    exact (InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois
      (k := k) (K := K) (L := L j)).mp ⟨hopen,hnormal⟩
  have hφsurj : ∀ j, Function.Surjective ((QuotientGroup.mk' (U j).toSubgroup).comp φ) := by
    intro j q
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (U j).toSubgroup q
    obtain ⟨g,rfl⟩ := hφ x
    exact ⟨g,rfl⟩
  have hNker : ∀ j, N j = ((QuotientGroup.mk' (U j).toSubgroup).comp φ).ker := by
    intro j
    change (U j).toSubgroup.comap φ = ((QuotientGroup.mk' (U j).toSubgroup).comp φ).ker
    rw [← MonoidHom.comap_ker,QuotientGroup.ker_mk']
  let quotientEquiv (j : ℕ) : (Q ⧸ (U j).toSubgroup) ≃* (Gal(K/k) ⧸ N j) :=
    (QuotientGroup.liftEquiv (N j) (hφsurj j) (hNker j)).symm
  let quotientAutEquiv (j : ℕ) : (Q ⧸ (U j).toSubgroup) ≃* Gal(L j/k) := by
    haveI : (H j).Normal := hNnormal j
    exact (quotientEquiv j).trans (InfiniteGalois.normalAutEquivQuotient (k := k) (K := K) (H j))
  have hcard (j : ℕ) : Nat.card (Q ⧸ (U j).toSubgroup) = Module.finrank k (L j) := by
    letI : Module.Finite k (L j) := (hLfin_gal j).1
    letI : IsGalois k (L j) := (hLfin_gal j).2
    rw [Nat.card_congr (quotientAutEquiv j).toEquiv]
    exact IsGalois.card_aut_eq_finrank k (L j)
  refine ⟨{ level := L
            finite := fun j => (hLfin_gal j).1
            galois := fun j => (hLfin_gal j).2
            increasing := ?_
            kernel_fixes := ?_
            degree_tendsto := ?_ }⟩
  · intro j
    apply IntermediateField.fixedField_le
    exact Subgroup.comap_mono (hUmono j)
  · intro j g hg
    rw [hLfix]
    change φ g ∈ (U j).toSubgroup
    rw [MonoidHom.mem_ker.mp hg]
    exact Subgroup.one_mem _
  · simpa only [hcard] using hUtendsto

end UnitDistance.GaloisQuotient
