module

public import UnitDistance.SIntegerCRTApproximation
public import UnitDistance.SIntegerPeriodIdeal

@[expose] public section
set_option backward.privateInPublic true


/-! # Every actual rectangular finite coset contains an S-integer

The denominator is produced from the finite ordinary class group. After it
clears the finitely many local targets, ordinary ideal CRT gives the desired
precision. Surjectivity is the conclusion of the construction.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField nonZeroDivisors Classical
open NumberField IsDedekindDomain WithZero

namespace UnitDistance.SIntegerCRT

variable {K : Type} [Field K] [NumberField K]
  {T : Type*} [Fintype T]

def clearingExponent (P : T → HeightOneSpectrum (𝓞 K)) (x : LocalProduct P) : ℕ :=
  ∑ t, (WithZero.log (Valued.v (x t))).toNat

theorem local_value_le_clearingExponent (P : T → HeightOneSpectrum (𝓞 K))
    (x : LocalProduct P) (t : T) :
    Valued.v (x t) ≤ WithZero.exp (clearingExponent P x : ℤ) := by
  by_cases hx : Valued.v (x t) = (0 : ℤᵐ⁰)
  · simp [hx]
  have hn : (WithZero.log (Valued.v (x t))).toNat ≤ clearingExponent P x :=
    Finset.single_le_sum (f := fun t ↦ (WithZero.log (Valued.v (x t))).toNat)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ t)
  rw [← WithZero.exp_log hx, WithZero.exp_le_exp]
  exact (Int.self_le_toNat _).trans (Int.ofNat_le.mpr hn)

theorem denominator_power_valuation (P : T → HeightOneSpectrum (𝓞 K))
    (hP : Function.Injective P) (N : ℕ) (t : T) :
    (P t).valuation K ((supportDenominator P : K) ^ N) =
      WithZero.exp (-((classNumber K : ℤ) * N)) := by
  rw [map_pow, supportDenominator_valuation_selected P hP, ← WithZero.exp_nsmul]
  congr 1
  simp only [nsmul_eq_mul]
  ring

/-- Every actual finite-component coset of every rectangular valuation
period has an actual S-integer representative. -/
theorem exists_sInteger_in_finitePeriod_coset (P : T → HeightOneSpectrum (𝓞 K))
    (hP : Function.Injective P) (a : T → ℤ) (x : LocalProduct P) :
    ∃ y : (Set.range P).integer K, localEmbedding P (y : K) - x ∈ finitePeriod P a := by
  let N := clearingExponent P x
  let H : ℤ := (classNumber K : ℤ) * N
  let d : K := (supportDenominator P : K) ^ N
  have hd : d ≠ 0 := pow_ne_zero _ (RingOfIntegers.coe_injective.ne (supportDenominator_ne_zero P))
  have hN : (N : ℤ) ≤ H := by
    have hh : (1 : ℤ) ≤ classNumber K := by exact_mod_cast Nat.succ_le_iff.mpr (classNumber_pos K)
    dsimp [H]
    nlinarith [Int.natCast_nonneg N]
  have hvd (t : T) : (Valued.v : Valuation ((P t).adicCompletion K) ℤᵐ⁰)
      (algebraMap K ((P t).adicCompletion K) d) = WithZero.exp (-H) := by
    rw [valued_field]
    exact denominator_power_valuation P hP N t
  let z : LocalProduct P := fun t ↦ algebraMap K ((P t).adicCompletion K) d * x t
  have hz (t : T) : Valued.v (z t) ≤ (1 : ℤᵐ⁰) := by
    change Valued.v (algebraMap K ((P t).adicCompletion K) d * x t) ≤ 1
    rw [map_mul, hvd]
    calc
      _ ≤ WithZero.exp (-H) * WithZero.exp (N : ℤ) := by
        gcongr
        exact local_value_le_clearingExponent P x t
      _ = WithZero.exp (-H + N) := (WithZero.exp_add _ _).symm
      _ ≤ 1 := by rw [← WithZero.exp_zero, WithZero.exp_le_exp]; omega
  let n : T → ℕ := fun t ↦ (a t + H).toNat
  obtain ⟨c, hc⟩ := exists_simultaneous_integer_approximation P hP z hz n
  let y : K := (c : K) / d
  have hy : y ∈ (Set.range P).integer K := by
    intro v hv
    have hdo : v.valuation K d = 1 := by
      rw [show d = (supportDenominator P : K) ^ N from rfl, map_pow,
        supportDenominator_valuation_outside P v hv, one_pow]
    change v.valuation K ((c : K) / d) ≤ 1
    rw [map_div₀, hdo, div_one]
    exact v.valuation_le_one c
  refine ⟨⟨y, hy⟩, fun t ↦ ?_⟩
  change Valued.v (algebraMap K ((P t).adicCompletion K) ((c : K) / d) - x t) ≤
    WithZero.exp (-a t)
  have hdt : algebraMap K ((P t).adicCompletion K) d ≠ 0 :=
    (algebraMap K ((P t).adicCompletion K)).injective.ne hd
  rw [map_div₀]
  have hid : algebraMap K ((P t).adicCompletion K) (c : K) /
      algebraMap K ((P t).adicCompletion K) d - x t =
        (algebraMap (𝓞 K) ((P t).adicCompletion K) c - z t) /
          algebraMap K ((P t).adicCompletion K) d := by
    rw [IsScalarTower.algebraMap_apply (𝓞 K) K ((P t).adicCompletion K)]
    dsimp [z]
    field_simp
  rw [hid, map_div₀, hvd]
  calc
    _ ≤ WithZero.exp (-(n t : ℤ)) / WithZero.exp (-H) :=
      div_le_div_of_nonneg_right (hc t) zero_le
    _ = WithZero.exp (-(n t : ℤ) - -H) := (WithZero.exp_sub _ _).symm
    _ ≤ WithZero.exp (-a t) := by
      rw [WithZero.exp_le_exp]
      have hn : a t + H ≤ (n t : ℤ) := Int.self_le_toNat _
      omega

/-- The actual diagonal S-integer map to the finite local quotient is surjective. -/
theorem sInteger_finiteQuotient_surjective (P : T → HeightOneSpectrum (𝓞 K))
    (hP : Function.Injective P) (a : T → ℤ) :
    Function.Surjective (fun y : (Set.range P).integer K ↦
      (QuotientAddGroup.mk (s := finitePeriod P a) (localEmbedding P (y : K)))) := by
  intro c
  obtain ⟨x, rfl⟩ := Quotient.exists_rep c
  obtain ⟨y, hy⟩ := exists_sInteger_in_finitePeriod_coset P hP a x
  exact ⟨y, QuotientAddGroup.eq_iff_sub_mem.mpr hy⟩

end UnitDistance.SIntegerCRT
