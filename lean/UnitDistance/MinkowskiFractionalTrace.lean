module

public import UnitDistance.MinkowskiTrace

@[expose] public section
set_option backward.privateInPublic true


/-! The trace-dual identification for all nonzero fractional ideals. -/
noncomputable section
open NumberField NumberField.mixedEmbedding
open scoped nonZeroDivisors
namespace UnitDistance.MinkowskiTrace
variable (K : Type*) [Field K] [NumberField K]

def dualFractionalIdeal (I : FractionalIdeal (𝓞 K)⁰ K) : FractionalIdeal (𝓞 K)⁰ K :=
  (I * differentFractionalIdeal K)⁻¹

theorem dualFractionalIdeal_eq_dual (I : FractionalIdeal (𝓞 K)⁰ K) :
    FractionalIdeal.dual ℤ ℚ I = dualFractionalIdeal K I := by
  have hd1 : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)
      = (differentFractionalIdeal K)⁻¹ := by
    have h := coeIdeal_differentIdeal (A := ℤ) (K := ℚ) (L := K) (B := 𝓞 K)
    rw [differentFractionalIdeal, h, inv_inv]
  rw [FractionalIdeal.dual_eq_mul_inv, hd1, dualFractionalIdeal, mul_inv, mul_comm]

theorem traceForm_mixedEmbedding_int_iff_mem_dualFractionalIdeal
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) (b : K) :
    (∀ a ∈ I, ∃ k : ℤ, traceForm K (mixedEmbedding K b) a = k) ↔
      b ∈ dualFractionalIdeal K I := by
  rw [← dualFractionalIdeal_eq_dual K I, FractionalIdeal.mem_dual hI]
  refine forall₂_congr fun a ha => ?_
  rw [traceForm_mixedEmbedding, Algebra.traceForm_apply, RingHom.mem_range]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    apply FaithfulSMul.algebraMap_injective ℚ ℝ
    rw [hk, ← IsScalarTower.algebraMap_apply ℤ ℚ ℝ]
    simp
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [← hk, ← IsScalarTower.algebraMap_apply ℤ ℚ ℝ]
    simp

/-- Rationality for a fractional ideal follows by restricting to its actual
nonzero integral numerator, then testing the recovered field element on the
whole fractional ideal. No choice of rational coordinates is assumed. -/
theorem traceForm_int_iff_exists_dualFractionalIdeal
    (I : FractionalIdeal (𝓞 K)⁰ K) (hI : I ≠ 0) (η : mixedSpace K) :
    (∀ a ∈ I, ∃ k : ℤ, traceForm K η a = k) ↔
      ∃ b ∈ dualFractionalIdeal K I, mixedEmbedding K b = η := by
  constructor
  · intro h
    have hn : I.num ≠ 0 := by
      intro hz
      exact hI (FractionalIdeal.zero_of_num_eq_bot zero_notMem_nonZeroDivisors hz)
    have hnum : ∀ a ∈ (I.num : FractionalIdeal (𝓞 K)⁰ K),
        ∃ k : ℤ, traceForm K η a = k := fun a ha => h a (I.num_le ha)
    obtain ⟨b, _, hb⟩ := (traceForm_int_iff_exists_dualIdeal K I.num hn η).mp hnum
    refine ⟨b, (traceForm_mixedEmbedding_int_iff_mem_dualFractionalIdeal K I hI b).mp ?_, hb⟩
    simpa only [hb] using h
  · rintro ⟨b, hb, rfl⟩
    exact (traceForm_mixedEmbedding_int_iff_mem_dualFractionalIdeal K I hI b).mpr hb

end UnitDistance.MinkowskiTrace
