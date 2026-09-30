module

public import UnitDistance.RelativeIdealCosetsBasic

@[expose] public section
set_option backward.privateInPublic true


/-!
# Norm-one principal generators produced by an actual relative class fiber

Actual ideal-class equality gives integral cross-multipliers. Applying the
actual involution cancels the extended base ideal; its field ratio supplies
the norm-one principal generator.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField nonZeroDivisors Classical
open NumberField

namespace UnitDistance.RelativeIdealCosets

open RelativeUnits

private theorem quotient_of_cross_relations {G : Type*} [CommGroup G]
    (B C A B' C' a b a' b' : G)
    (h : a * B = b * (A * C)) (h' : a' * B' = b' * (A * C')) :
    (B / B') / (C / C') = (b / a) / (b' / a') := by
  have hB : B = (b / a) * (A * C) := by
    calc
      B = a⁻¹ * (b * (A * C)) := by rw [← h]; simp
      _ = (b / a) * (A * C) := by simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hB' : B' = (b' / a') * (A * C') := by
    calc
      B' = a'⁻¹ * (b' * (A * C')) := by rw [← h']; simp
      _ = (b' / a') * (A * C') := by simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  rw [hB, hB']
  rw [mul_div_mul_comm, mul_div_mul_left_eq_div, mul_div_cancel_right]

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K]

/-- A nonzero algebraic integer viewed as an actual invertible field element. -/
def integerFieldUnit (a : 𝓞 K) (ha : a ≠ 0) : Kˣ :=
  Units.mk0 (a : K) (RingOfIntegers.coe_injective.ne ha)

@[simp] theorem integerFieldUnit_coe (a : 𝓞 K) (ha : a ≠ 0) :
    (integerFieldUnit a ha : K) = a := rfl

/-- Integral cross-multiplier equations hold in the actual fractional-ideal group. -/
theorem lift_cross_relation (B C : NonzeroIdeal K) (a b : 𝓞 K)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h : Ideal.span {a} * B.val = Ideal.span {b} * C.val) :
    toPrincipalIdeal (𝓞 K) K (integerFieldUnit a ha) * FractionalIdeal.mk0 K B =
      toPrincipalIdeal (𝓞 K) K (integerFieldUnit b hb) * FractionalIdeal.mk0 K C := by
  apply Units.ext
  have hh := congrArg (fun I : Ideal (𝓞 K) ↦ (I : FractionalIdeal (𝓞 K)⁰ K)) h
  simpa only [Units.val_mul, coe_toPrincipalIdeal, integerFieldUnit_coe,
    FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_mul,
    FractionalIdeal.coeIdeal_span_singleton] using hh

/-- The actual anti-invariant ratio of one integral ideal and its conjugate. -/
def idealAntiRatio (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (B : NonzeroIdeal K) : IdealGroup K :=
  FractionalIdeal.mk0 K B / FractionalIdeal.mk0 K (conjugateNonzeroIdeal ι hι B)

/-- A relative class fiber supplies a principal anti-invariant ratio with the
literal generator `x/ι(x)`. No principal-generator data is assumed. -/
theorem same_relativeClass_exists_normOne_generator (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (B C : NonzeroIdeal K)
    (h : relativeIdealClass (F := F) B = relativeIdealClass (F := F) C) :
    ∃ x : Kˣ, idealAntiRatio ι hι B / idealAntiRatio ι hι C =
      toPrincipalIdeal (𝓞 K) K (fieldCoboundary ι x) := by
  obtain ⟨A, a, b, ha, hb, hab⟩ := same_relativeClass_exists_cross_multipliers B C h
  let e := RingOfIntegers.mapRingEquiv ι.toRingEquiv
  have hea : e a ≠ 0 := by simpa using e.injective.ne ha
  have heb : e b ≠ 0 := by simpa using e.injective.ne hb
  have hc := congrArg (conjugateIdeal ι) hab
  simp only [map_mul, conjugateIdeal_span, conjugateIdeal_extended] at hc
  have h₁ := lift_cross_relation B (ClassGroup.extendedIdeal (𝓞 F) (𝓞 K) A * C) a b ha hb hab
  have h₂ := lift_cross_relation (conjugateNonzeroIdeal ι hι B)
    (ClassGroup.extendedIdeal (𝓞 F) (𝓞 K) A * conjugateNonzeroIdeal ι hι C)
    (e a) (e b) hea heb hc
  rw [map_mul] at h₁ h₂
  have hr := quotient_of_cross_relations _ _ _ _ _ _ _ _ _ h₁ h₂
  refine ⟨integerFieldUnit b hb / integerFieldUnit a ha, ?_⟩
  change _ = _ at hr
  rw [idealAntiRatio, idealAntiRatio, hr]
  have hae : integerFieldUnit (e a) hea = fieldUnitInvolution ι (integerFieldUnit a ha) := by
    apply Units.ext
    rfl
  have hbe : integerFieldUnit (e b) heb = fieldUnitInvolution ι (integerFieldUnit b hb) := by
    apply Units.ext
    rfl
  rw [hae, hbe]
  simp only [fieldCoboundary, map_div]

end UnitDistance.RelativeIdealCosets
