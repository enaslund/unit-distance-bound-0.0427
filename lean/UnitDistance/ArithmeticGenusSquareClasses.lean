module

public import UnitDistance.ArithmeticChosenGenusField
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas

@[expose] public section
set_option backward.privateInPublic true


/-! The actual genus field contains square roots of every signed squarefree
integer supported at 2, 3, 5, 7, 11 and 13. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.ArithmeticChosenGenus
open scoped BigOperators

abbrev finitePrimeSupport : Finset ℕ := {2, 3, 5, 7, 11, 13}

variable (K : Type*) [Field K] [Algebra GenusField K]

theorem isSquare_minus_one : IsSquare (-1 : K) := by
  refine ⟨algebraMap GenusField K (roots 0), ?_⟩
  have h := congrArg (algebraMap GenusField K) (roots_sq 0)
  norm_num [radicands, map_pow, pow_two] at h ⊢
  exact h.symm

theorem isSquare_supported_prime (p : ℕ) (hp : p ∈ finitePrimeSupport) :
    IsSquare (p : K) := by
  have h : ∃ i : Fin 7, radicands i = (p : ℚ) := by
    simp only [finitePrimeSupport, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
    · exact ⟨6, rfl⟩
  obtain ⟨i, hi⟩ := h
  refine ⟨algebraMap GenusField K (roots i), ?_⟩
  have hs := congrArg (algebraMap GenusField K) (roots_sq i)
  rw [hi] at hs
  simpa only [map_pow, map_ratCast, Rat.cast_natCast, map_natCast, pow_two, map_mul] using hs.symm

/-- Signed supported squarefree radicands are actual squares in every
extension of the seven-root genus field. -/
theorem isSquare_int_of_support (d : ℤ) (hd : Squarefree d.natAbs)
    (hs : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ d → p ∈ finitePrimeSupport) :
    IsSquare (d : K) := by
  have ha : IsSquare (d.natAbs : K) := by
    rw [← Nat.prod_primeFactors_of_squarefree hd, Nat.cast_prod]
    apply Finset.isSquare_prod
    intro p hp
    apply isSquare_supported_prime K p
    exact hs p (Nat.prime_of_mem_primeFactors hp)
      (Int.natCast_dvd.mpr (Nat.dvd_of_mem_primeFactors hp))
  by_cases hnonneg : 0 ≤ d
  · have he : (d.natAbs : ℤ) = d := Int.natAbs_of_nonneg hnonneg
    have hc : (d.natAbs : K) = (d : K) := by
      simpa only [Int.cast_natCast] using congrArg (fun z : ℤ ↦ (z : K)) he
    rw [hc] at ha
    exact ha
  · have he : (d.natAbs : ℤ) = -d := by
      rw [Int.natCast_natAbs, abs_of_neg (lt_of_not_ge hnonneg)]
    have hc : (d.natAbs : K) = -(d : K) := by
      simpa only [Int.cast_natCast, Int.cast_neg] using congrArg (fun z : ℤ ↦ (z : K)) he
    have hh := (isSquare_minus_one K).mul ha
    simpa only [hc, neg_mul_neg, one_mul] using hh

/-- Any actual ambient root of a supported signed squarefree radicand
belongs to a subfield containing the actual genus field. -/
theorem root_mem_of_supported (C : Type*) [Field C] [Algebra ℚ C]
    (M : IntermediateField ℚ C) [Algebra GenusField M]
    (d : ℤ) (hd : Squarefree d.natAbs)
    (hs : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ d → p ∈ finitePrimeSupport)
    (r : C) (hr : r ^ 2 = (d : C)) : r ∈ M := by
  obtain ⟨s, hsquare⟩ := isSquare_int_of_support M d hd hs
  have he : (s : C) ^ 2 = (d : C) := by
    have h := congrArg (fun z : M ↦ (z : C)) hsquare.symm
    change (s : C) * (s : C) = (d : C) at h
    simpa only [pow_two] using h
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hr.trans he.symm) with h | h
  · rw [h]
    exact s.property
  · rw [h]
    exact M.neg_mem s.property

end UnitDistance.ArithmeticChosenGenus
