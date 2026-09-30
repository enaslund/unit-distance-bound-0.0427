module

public import UnitDistance.HeckeSignedArithmetic

@[expose] public section
set_option backward.privateInPublic true


/-! Norm-only cone weights and their actual principal-ideal regrouping.
The norm-fiber argument is adapted from Chris Birkbeck's AINTLIB
MellinAgreement (2026, Apache-2.0); the arbitrary nonnegative norm weight
allows the odd restriction and both signs of the mod-four character. -/
noncomputable section
open NumberField NumberField.InfinitePlace DedekindResidue MeasureTheory
open NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
open NumberField.Units NumberField.Units.dirichletUnitTheorem
open scoped BigOperators Real Classical nonZeroDivisors NNReal ENNReal
namespace UnitDistance.NumberFieldAnalysis
variable (K : Type*) [Field K] [NumberField K]

/-- Actual generators modulo free units leave exactly the torsion multiplicity
in the sum over principal ideals, for any weight depending on the ordinary norm. -/
theorem tsum_idealSet_norm_weight (J : (Ideal (𝓞 K))⁰) (H : ℕ → ℝ≥0∞) :
    (∑' a : idealSet K J, H (intNorm (idealSetMap K J a))) =
      (torsionOrder K) *
        ∑' I : {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K))
          ∧ Submodule.IsPrincipal ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))},
            H (Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))) := by
  -- fiber the cone side over the integer norm
  rw [← Equiv.tsum_eq (Equiv.sigmaFiberEquiv (fun a : idealSet K J =>
    intNorm (idealSetMap K J a))) (fun a =>
      H (intNorm (idealSetMap K J a))),
    ENNReal.tsum_sigma']
  -- fiber the ideal side over the norm
  have hidealfiber : (∑' I : {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K))
        ∧ Submodule.IsPrincipal ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))},
        H (Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))))
      = ∑' n : ℕ, ∑' _I : {I : {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K))
          ∧ Submodule.IsPrincipal ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))} //
            Ideal.absNorm ((I.val : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = n},
          H n := by
    rw [← Equiv.tsum_eq (Equiv.sigmaFiberEquiv
      (fun I : {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K))
        ∧ Submodule.IsPrincipal ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))} =>
          Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))))
      (fun I => H (Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) :
        Ideal (𝓞 K))))]
    rw [ENNReal.tsum_sigma']
    refine tsum_congr (fun n => tsum_congr (fun I => ?_))
    show H (Ideal.absNorm ((I.val : (Ideal (𝓞 K))⁰) :
      Ideal (𝓞 K))) = _
    rw [I.2]
  rw [hidealfiber]
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr (fun n => ?_)
  -- reduce the cone fiber to a constant sum
  have hconst : (∑' b : {a : idealSet K J // intNorm (idealSetMap K J a) = n},
      H (intNorm (idealSetMap K J ((Equiv.sigmaFiberEquiv
        (fun a : idealSet K J => intNorm (idealSetMap K J a))) ⟨n, b⟩))))
      = ∑' _b : {a : idealSet K J // intNorm (idealSetMap K J a) = n},
          H n := by
    refine tsum_congr (fun b => ?_)
    show H (intNorm (idealSetMap K J b.val)) = _
    rw [b.2]
  rw [hconst]
  -- reindex the cone fiber to the mathlib norm-fiber, then to ideals × torsion
  have hfib1 : {a : idealSet K J // intNorm (idealSetMap K J a) = n}
      ≃ {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) = (n : ℝ)} := by
    refine Equiv.subtypeEquivRight (fun a => ?_)
    constructor
    · intro h
      rw [← h, intNorm_coe,
        show ((idealSetMap K J a : integerSet K) : mixedSpace K) = (a : mixedSpace K)
          from idealSetMap_apply K J a]
    · intro h
      have h2 : (intNorm (idealSetMap K J a) : ℝ) = (n : ℝ) := by
        rw [intNorm_coe, show ((idealSetMap K J a : integerSet K) : mixedSpace K)
          = (a : mixedSpace K) from idealSetMap_apply K J a]
        exact h
      exact_mod_cast h2
  rw [show (∑' _b : {a : idealSet K J // intNorm (idealSetMap K J a) = n},
      H n)
    = ∑' _b : {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) = (n : ℝ)},
        H n from
    (Equiv.tsum_eq hfib1.symm (fun _ => H n)).symm]
  rw [show (∑' _b : {a : idealSet K J // mixedEmbedding.norm (a : mixedSpace K) = (n : ℝ)},
      H n)
    = ∑' _p : {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K))
        ∧ Submodule.IsPrincipal ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))
        ∧ Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = n} × (torsion K),
        H n from
    (Equiv.tsum_eq (idealSetEquivNorm K J n).symm
      (fun _ => H n)).symm]
  rw [ENNReal.tsum_prod']
  have hinner : ∀ I : {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K))
      ∧ Submodule.IsPrincipal ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))
      ∧ Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = n},
      (∑' _ζ : torsion K, H n)
        = (torsionOrder K) * H n := by
    intro I
    letI := Fintype.ofFinite (torsion K)
    rw [tsum_fintype, Finset.sum_const, nsmul_eq_mul, Units.torsionOrder,
      Nat.card_eq_fintype_card]
    norm_cast
  rw [tsum_congr hinner, ENNReal.tsum_mul_left]
  congr 1
  have hfibeq : {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K))
      ∧ Submodule.IsPrincipal ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))
      ∧ Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = n}
      ≃ {I : {I : (Ideal (𝓞 K))⁰ // (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K))
          ∧ Submodule.IsPrincipal ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K))} //
            Ideal.absNorm ((I.val : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = n} := by
    refine (Equiv.subtypeEquivRight (fun I => ?_)).trans
      (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun I : (Ideal (𝓞 K))⁰ => (J : Ideal (𝓞 K)) ∣ (I : Ideal (𝓞 K))
          ∧ Submodule.IsPrincipal ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)))
        (fun I => Ideal.absNorm ((I : (Ideal (𝓞 K))⁰) : Ideal (𝓞 K)) = n)).symm
    rw [and_assoc]
  exact (Equiv.tsum_eq hfibeq.symm
    (fun _ => H n)).symm

end UnitDistance.NumberFieldAnalysis
