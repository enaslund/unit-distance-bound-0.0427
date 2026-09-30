module

public import UnitDistance.Sqrt241.Base.Primes
public import Mathlib.NumberTheory.NumberField.ClassNumber

@[expose] public section
set_option backward.privateInPublic true

/-!
# Class number one for `B = ℚ(√241)`

The Minkowski bound of `B` is `(1/2)√241 < 8`. Every prime ideal above
`2, 3, 5` is principal (`(π₂), (π₂'), …`) and `7` is inert, so `𝓞 B` is a
principal ideal domain (`isPrincipalIdealRing`) and `classNumber B = 1`.
-/

noncomputable section

namespace UnitDistance.Sqrt241.Base

open NumberField Ideal Module

theorem minkowskiBound_lt_eight :
    (4 / Real.pi) ^ InfinitePlace.nrComplexPlaces B *
      ((finrank ℚ B).factorial / (finrank ℚ B : ℝ) ^ (finrank ℚ B) * √|(discr B : ℝ)|) < 8 := by
  rw [nrComplexPlaces_eq_zero, finrank_eq_two, discr_eq]
  have h : √(241 : ℝ) < 16 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  norm_num
  linarith

/-- `𝓞 B` is a principal ideal domain. -/
theorem isPrincipalIdealRing : IsPrincipalIdealRing (𝓞 B) := by
  apply RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
  intro p hp hprime P hP _
  have hle : p ≤ 7 := by
    have h1 := (Finset.mem_Icc.mp hp).2
    have h2 := (Nat.floor_lt' (n := 8) (by norm_num)).mpr
      (minkowskiBound_lt_eight.trans_eq (by norm_num))
    omega
  obtain ⟨hPprime, hPlies⟩ := hP
  have hmem : (p : 𝓞 B) ∈ P := natCast_mem_of_liesOver P p
  have hp1 := hprime.two_le
  interval_cases p
  · rcases eq_P2_or_P2' (by simpa using hmem) with rfl | rfl
    · exact ⟨⟨pi2, rfl⟩⟩
    · exact ⟨⟨pi2', rfl⟩⟩
  · rcases eq_P3_or_P3' (by simpa using hmem) with rfl | rfl
    · exact ⟨⟨pi3, rfl⟩⟩
    · exact ⟨⟨pi3', rfl⟩⟩
  · exact absurd hprime (by norm_num)
  · rcases eq_P5_or_P5' (by simpa using hmem) with rfl | rfl
    · exact ⟨⟨pi5, rfl⟩⟩
    · exact ⟨⟨pi5', rfl⟩⟩
  · exact absurd hprime (by norm_num)
  · obtain rfl := eq_P7 (P := P) (by simpa using hmem)
    exact ⟨⟨7, rfl⟩⟩

instance : IsPrincipalIdealRing (𝓞 B) := isPrincipalIdealRing

/-- The class number of `ℚ(√241)` is one. -/
theorem classNumber_eq_one : classNumber B = 1 :=
  classNumber_eq_one_iff.mpr isPrincipalIdealRing

end UnitDistance.Sqrt241.Base
