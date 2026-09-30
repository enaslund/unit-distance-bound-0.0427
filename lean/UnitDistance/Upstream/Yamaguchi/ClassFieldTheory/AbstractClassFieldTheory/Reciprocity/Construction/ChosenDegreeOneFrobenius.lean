/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.Universal

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

universe u

namespace ClassFormation

open CyclicCohomology

/-!
# The chosen degree-one Frobenius element

Surjectivity of the normalized degree supplies a Frobenius-semigroup element
of exponent one.  The chosen object and its specification are kept together
here so the multiplicativity proof can consume a named choice boundary.
-/

noncomputable section

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- A chosen degree-one element of `G(\widetilde L/K)`, packaged as an
element of the Frobenius semigroup. -/
noncomputable def chosenDegreeOneFrobeniusElement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal] :
    D.FrobeniusElements K L hLK := by
  let hsurj := D.extensionNormalizedDegreeContinuous_surjective K L hLK
    (Multiplicative.ofAdd (1 : ZHat))
  refine ⟨Classical.choose hsurj, 1, Nat.one_pos, ?_⟩
  rw [pow_one, ← D.extensionNormalizedDegreeContinuous_apply]
  exact Classical.choose_spec hsurj

/--
Establishes the identity `D.frobeniusExponent K L hLK (D.chosenDegreeOneFrobeniusElement K L hLK)
= 1`.
-/
@[simp]
theorem frobeniusExponent_chosenDegreeOneFrobeniusElement (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (extensionSubgroup K.field L hLK).Normal] :
    D.frobeniusExponent K L hLK
        (D.chosenDegreeOneFrobeniusElement K L hLK) = 1 := by
  apply proCIntegerOne_pow_nat_injective
  calc
    (Multiplicative.ofAdd (1 : ZHat)) ^
        D.frobeniusExponent K L hLK
          (D.chosenDegreeOneFrobeniusElement K L hLK) =
      D.extensionNormalizedDegree K L hLK
        (D.chosenDegreeOneFrobeniusElement K L hLK).1 :=
      (D.extensionNormalizedDegree_frobenius_eq_pow K L hLK
        (D.chosenDegreeOneFrobeniusElement K L hLK)).symm
    _ = Multiplicative.ofAdd (1 : ZHat) := by
      rw [← D.extensionNormalizedDegreeContinuous_apply]
      change D.extensionNormalizedDegreeContinuous K L hLK
        (Classical.choose
          (D.extensionNormalizedDegreeContinuous_surjective K L hLK
            (Multiplicative.ofAdd (1 : ZHat)))) =
          Multiplicative.ofAdd (1 : ZHat)
      exact Classical.choose_spec
        (D.extensionNormalizedDegreeContinuous_surjective K L hLK
          (Multiplicative.ofAdd (1 : ZHat)))
    _ = (Multiplicative.ofAdd (1 : ZHat)) ^ (1 : ℕ) := by simp

end DegreeData

end

end ClassFormation
