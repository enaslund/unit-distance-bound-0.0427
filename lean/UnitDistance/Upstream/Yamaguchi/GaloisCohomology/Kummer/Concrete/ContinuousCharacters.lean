/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Finite-stage factorization of continuous Galois characters

A continuous character from an infinite Galois group to a discrete group
factors through the Galois group of a finite Galois intermediate field.
-/

noncomputable section

namespace KummerTheory

open scoped Topology

variable {K Ω A : Type*}
  [Field K] [Field Ω] [Algebra K Ω]
  [Group A] [TopologicalSpace A] [DiscreteTopology A]

private theorem continuousCharacterIsOpenKer (χ : Gal(Ω/K) →ₜ* A) :
    IsOpen (χ.toMonoidHom.ker : Set Gal(Ω/K)) := by
  rw [MonoidHom.coe_ker]
  exact (isOpen_discrete ({1} : Set A)).preimage χ.continuous

variable [IsGalois K Ω]

private theorem continuousCharacterExistsFiniteGaloisFixingSubgroupLeKer
    (χ : Gal(Ω/K) →ₜ* A) :
    ∃ E : FiniteGaloisIntermediateField K Ω,
      E.fixingSubgroup ≤ χ.toMonoidHom.ker := by
  have hnhds : (χ.toMonoidHom.ker : Set Gal(Ω/K)) ∈ 𝓝 1 :=
    (continuousCharacterIsOpenKer χ).mem_nhds (by simp)
  obtain ⟨E, hE⟩ :=
    (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois
      (k := K) (K := Ω) (χ.toMonoidHom.ker : Set Gal(Ω/K))).1 hnhds
  exact ⟨E, hE⟩

/-- Every continuous character of an infinite Galois group into a discrete
group factors through the Galois group of a finite Galois intermediate
field. -/
theorem continuousCharacter_factors_through_finiteGalois
    (χ : Gal(Ω/K) →ₜ* A) :
    ∃ (E : FiniteGaloisIntermediateField K Ω) (χE : Gal(E/K) →* A),
      χE.comp (AlgEquiv.restrictNormalHom E) = χ.toMonoidHom := by
  obtain ⟨E, hE⟩ :=
    continuousCharacterExistsFiniteGaloisFixingSubgroupLeKer χ
  have hker : (AlgEquiv.restrictNormalHom E).ker ≤ χ.toMonoidHom.ker := by
    rw [IntermediateField.restrictNormalHom_ker]
    exact hE
  let χE : Gal(E/K) →* A :=
    (AlgEquiv.restrictNormalHom E).liftOfSurjective
      (AlgEquiv.restrictNormalHom_surjective Ω) ⟨χ.toMonoidHom, hker⟩
  refine ⟨E, χE, ?_⟩
  simp [χE]

end KummerTheory
