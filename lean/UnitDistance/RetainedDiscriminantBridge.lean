module

public import UnitDistance.ArithmeticRetainedDiscriminant
public import UnitDistance.GenusDiscriminant
public import UnitDistance.RelativeDiscriminant
public import UnitDistance.Witness

@[expose] public section
set_option backward.privateInPublic true


/-!
# Exact discriminant reduction for the canonical retained field

The manuscript's local calculation predicts an exact integer factorization of
the absolute discriminant of the independently specified retained field.  This
file separates that arithmetic statement from the real logarithm and real
power bookkeeping in the final numerical premise.
-/

noncomputable section
namespace UnitDistance.CanonicalRetained
open NumberField
open NumberFieldAnalysis
open Witness

/-- The exact absolute discriminant predicted by the local different
calculation.  Keeping it as a natural number makes the remaining arithmetic
obligation independent of real logarithms and real powers. -/
def expectedAbsoluteDiscriminant : ℕ :=
  2 ^ 1179648 * 15015 ^ 262144

/-- Keep the cast calculation symbolic before instantiating the large
discriminant powers. -/
private theorem natCast_le_pow_mul_pow (n a b r s : ℕ)
    (h : n ≤ a ^ r * b ^ s) :
    (n : ℝ) ≤ (a : ℝ) ^ r * (b : ℝ) ^ s := by
  have hcast : (n : ℝ) ≤ ((a ^ r * b ^ s : ℕ) : ℝ) := Nat.cast_le.mpr h
  simpa only [Nat.cast_mul, Nat.cast_pow] using hcast

/-- Combine the different and genus bounds using variables.  The exponent
equalities are separate premises so their small arithmetic is checked without
reducing the resulting natural-number powers. -/
private theorem nat_mul_pow_le_pow_mul_pow
    (d g a b p r s k u v : ℕ)
    (hd : d ≤ a ^ p) (hg : g ≤ a ^ r * b ^ s)
    (hu : p + r * k = u) (hv : s * k = v) :
    d * g ^ k ≤ a ^ u * b ^ v := by
  calc
    d * g ^ k ≤ a ^ p * (a ^ r * b ^ s) ^ k :=
      Nat.mul_le_mul hd (Nat.pow_le_pow_left hg k)
    _ = a ^ u * b ^ v := by
      rw [mul_pow, ← pow_mul, ← pow_mul, ← mul_assoc, ← pow_add, hu, hv]

/-- Compose the natural-number bound and its real cast while all quantities
are variables.  Instantiating this result does not compare the closed natural
discriminant bound with its unfolded definition. -/
private theorem natCast_mul_pow_le_pow_mul_pow
    (d g a b p r s k u v : ℕ)
    (hd : d ≤ a ^ p) (hg : g ≤ a ^ r * b ^ s)
    (hu : p + r * k = u) (hv : s * k = v) :
    ((d * g ^ k : ℕ) : ℝ) ≤ (a : ℝ) ^ u * (b : ℝ) ^ v := by
  exact natCast_le_pow_mul_pow (d * g ^ k) a b u v
    (nat_mul_pow_le_pow_mul_pow d g a b p r s k u v hd hg hu hv)

/-- Transport an exact discriminant calculation on the arithmetic retained
field to the independently specified canonical field. -/
theorem discriminant_eq_expected_of_arithmetic
    (hdisc : (discr ArithmeticRetained.RetainedField).natAbs =
      expectedAbsoluteDiscriminant) :
    (discr Carrier).natAbs = expectedAbsoluteDiscriminant := by
  rw [NumberField.discr_eq_discr_of_algEquiv Carrier equiv]
  exact hdisc

theorem discriminant_le_expected_of_arithmetic
    (hdisc : (discr ArithmeticRetained.RetainedField).natAbs ≤
      expectedAbsoluteDiscriminant) :
    (discr Carrier).natAbs ≤ expectedAbsoluteDiscriminant := by
  rw [NumberField.discr_eq_discr_of_algEquiv Carrier equiv]
  exact hdisc

/-- The exact integer discriminant factorization implies the root-discriminant
identity used by the final theorem. -/
theorem log_rootDiscriminant_eq_logRD_of_discriminant
    (hdisc : (discr Carrier).natAbs = expectedAbsoluteDiscriminant) :
    Real.log (rootDiscriminant Carrier) = logRD := by
  have hD : absoluteDiscriminant Carrier =
      (2 : ℝ) ^ 1179648 * (15015 : ℝ) ^ 262144 := by
    unfold expectedAbsoluteDiscriminant at hdisc
    have hcast := congrArg (fun n : ℕ => (n : ℝ)) hdisc
    simpa only [absoluteDiscriminant, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hcast
  rw [rootDiscriminant, Real.log_rpow (absoluteDiscriminant_pos Carrier), hD,
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
    degree]
  unfold logRD
  ring

/-- The real-valued discriminant bound suffices for the logarithmic endpoint. -/
private theorem log_rootDiscriminant_le_logRD_of_real_discriminant_le
    (hD : absoluteDiscriminant Carrier ≤
      (2 : ℝ) ^ 1179648 * (15015 : ℝ) ^ 262144) :
    Real.log (rootDiscriminant Carrier) ≤ logRD := by
  have hlog : Real.log (absoluteDiscriminant Carrier) ≤
      Real.log ((2 : ℝ) ^ 1179648 * (15015 : ℝ) ^ 262144) :=
    Real.log_le_log (absoluteDiscriminant_pos Carrier) hD
  rw [rootDiscriminant, Real.log_rpow (absoluteDiscriminant_pos Carrier), degree]
  calc
    1 / (524288 : ℝ) * Real.log (absoluteDiscriminant Carrier) ≤
        1 / (524288 : ℝ) *
          Real.log ((2 : ℝ) ^ 1179648 * (15015 : ℝ) ^ 262144) := by
      exact mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = logRD := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      unfold logRD
      ring

/-- An upper bound by the predicted integer discriminant is already enough
for the final root-discriminant premise.  This is the form naturally produced
by local different bounds. -/
theorem log_rootDiscriminant_le_logRD_of_discriminant_le
    (hdisc : (discr Carrier).natAbs ≤ expectedAbsoluteDiscriminant) :
    Real.log (rootDiscriminant Carrier) ≤ logRD := by
  exact log_rootDiscriminant_le_logRD_of_real_discriminant_le
    (natCast_le_pow_mul_pow (discr Carrier).natAbs 2 15015 1179648 262144 hdisc)

/-- The exact discriminant factorization also implies the weak inequality in
the current three-premise endpoint. -/
theorem log_rootDiscriminant_le_logRD_of_discriminant
    (hdisc : (discr Carrier).natAbs = expectedAbsoluteDiscriminant) :
    Real.log (rootDiscriminant Carrier) ≤ logRD :=
  (log_rootDiscriminant_eq_logRD_of_discriminant hdisc).le

/-- Arithmetic-field form of the bridge, ready for a local-different proof on
the constructed retained field. -/
theorem log_rootDiscriminant_le_logRD_of_arithmetic_discriminant
    (hdisc : (discr ArithmeticRetained.RetainedField).natAbs =
      expectedAbsoluteDiscriminant) :
    Real.log (rootDiscriminant Carrier) ≤ logRD :=
  log_rootDiscriminant_le_logRD_of_discriminant
    (discriminant_eq_expected_of_arithmetic hdisc)

theorem log_rootDiscriminant_le_logRD_of_arithmetic_discriminant_le
    (hdisc : (discr ArithmeticRetained.RetainedField).natAbs ≤
      expectedAbsoluteDiscriminant) :
    Real.log (rootDiscriminant Carrier) ≤ logRD :=
  log_rootDiscriminant_le_logRD_of_discriminant_le
    (discriminant_le_expected_of_arithmetic hdisc)

/-- The final discriminant premise follows from two local arithmetic bounds:
one on the seven-radical genus field and one on the relative dyadic different.
The odd-prime part of the relative different has already been eliminated in
`ArithmeticRetainedDiscriminant`. -/
theorem log_rootDiscriminant_le_logRD_of_genus_and_relativeDifferent
    (hgenus : (discr ArithmeticChosenGenus.GenusField).natAbs ≤
      2 ^ 256 * 15015 ^ 64)
    (hdyadic : Ideal.absNorm
      (differentIdeal (RingOfIntegers ArithmeticChosenGenus.GenusField)
        (RingOfIntegers ArithmeticRetained.RetainedField)) ≤ 2 ^ 131072) :
    Real.log (rootDiscriminant Carrier) ≤ logRD := by
  apply log_rootDiscriminant_le_logRD_of_real_discriminant_le
  unfold absoluteDiscriminant
  rw [NumberField.discr_eq_discr_of_algEquiv Carrier equiv,
    ArithmeticRetained.retainedField_natAbs_discr_eq_relativeDifferent]
  exact natCast_mul_pow_le_pow_mul_pow _ _ 2 15015 131072 256 64 4096 1179648 262144
    hdyadic hgenus (by norm_num) (by norm_num)

/-- The exact genus discriminant is now proved by a coprime-compositum
calculation.  Consequently the root-discriminant premise is reduced to the
single dyadic relative-different bound. -/
theorem log_rootDiscriminant_le_logRD_of_relativeDifferent
    (hdyadic : Ideal.absNorm
      (differentIdeal (RingOfIntegers ArithmeticChosenGenus.GenusField)
        (RingOfIntegers ArithmeticRetained.RetainedField)) ≤ 2 ^ 131072) :
    Real.log (rootDiscriminant Carrier) ≤ logRD := by
  exact log_rootDiscriminant_le_logRD_of_genus_and_relativeDifferent
    GenusDiscriminant.chosenGenus_natAbs_discr.le hdyadic

end UnitDistance.CanonicalRetained
