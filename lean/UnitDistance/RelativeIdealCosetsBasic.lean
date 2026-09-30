module

public import UnitDistance.RelativeUnitsMass
public import Mathlib.RingTheory.FractionalIdeal.Norm
public import Mathlib.Combinatorics.Pigeonhole

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual ideal conjugation and field norm-one ratios

These maps use the given quadratic field automorphism and the actual rings
of integers. No existence of a principal generator is a hypothesis.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField nonZeroDivisors Classical
open NumberField

namespace UnitDistance.RelativeIdealCosets

open RelativeUnits

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K]

abbrev NonzeroIdeal (K : Type) [Field K] := (Ideal (𝓞 K))⁰

abbrev IdealGroup (K : Type) [Field K] := (FractionalIdeal (𝓞 K)⁰ K)ˣ

/-- The actual quadratic automorphism on integral ideals. -/
def conjugateIdeal (ι : K ≃ₐ[F] K) : Ideal (𝓞 K) →+* Ideal (𝓞 K) :=
  Ideal.mapHom (RingOfIntegers.mapRingHom ι.toRingHom)

theorem conjugateIdeal_involutive (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    Function.Involutive (conjugateIdeal ι) := by
  intro I
  change Ideal.map _ (Ideal.map _ I) = I
  rw [Ideal.map_map]
  have h : (RingOfIntegers.mapRingHom ι.toRingHom).comp
      (RingOfIntegers.mapRingHom ι.toRingHom) = RingHom.id (𝓞 K) := by
    ext a
    exact quadratic_automorphism_involutive ι hι (a : K)
  rw [h, Ideal.map_id]

@[simp] theorem conjugateIdeal_span (ι : K ≃ₐ[F] K) (a : 𝓞 K) :
    conjugateIdeal ι (Ideal.span {a}) =
      Ideal.span {RingOfIntegers.mapRingHom ι.toRingHom a} := by
  exact (Ideal.map_span _ _).trans (by rw [Set.image_singleton])

theorem conjugateIdeal_ne_zero (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    {I : Ideal (𝓞 K)} (hI : I ≠ 0) : conjugateIdeal ι I ≠ 0 := by
  simpa only [map_zero] using (conjugateIdeal_involutive ι hι).injective.ne hI

/-- Conjugation preserves the actual ideal norm, by an isomorphism of the
ordinary finite quotient rings. -/
theorem conjugateIdeal_absNorm (ι : K ≃ₐ[F] K) (I : Ideal (𝓞 K)) :
    Ideal.absNorm (conjugateIdeal ι I) = Ideal.absNorm I := by
  exact Nat.card_congr (Ideal.quotientEquiv I (conjugateIdeal ι I)
    (RingOfIntegers.mapRingEquiv ι.toRingEquiv) rfl).symm.toEquiv

/-- The induced homomorphism on actual nonzero integral ideals. -/
def conjugateNonzeroIdeal (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    NonzeroIdeal K →* NonzeroIdeal K where
  toFun I := ⟨conjugateIdeal ι I.val, mem_nonZeroDivisors_iff_ne_zero.mpr
    (conjugateIdeal_ne_zero ι hι (mem_nonZeroDivisors_iff_ne_zero.mp I.prop))⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' I J := Subtype.ext (map_mul _ _ _)

@[simp] theorem coe_conjugateNonzeroIdeal (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (I : NonzeroIdeal K) :
    (conjugateNonzeroIdeal ι hι I).val = conjugateIdeal ι I.val := rfl

theorem conjugateNonzeroIdeal_involutive (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    Function.Involutive (conjugateNonzeroIdeal ι hι) :=
  fun I ↦ Subtype.ext (conjugateIdeal_involutive ι hι I.val)

@[simp] theorem conjugateIdeal_extended (ι : K ≃ₐ[F] K) (A : Ideal (𝓞 F)) :
    conjugateIdeal ι (Ideal.map (algebraMap (𝓞 F) (𝓞 K)) A) =
      Ideal.map (algebraMap (𝓞 F) (𝓞 K)) A := by
  have h := extendedIdeal_invariant (F := F) (K := K) A ι
  change Ideal.map (galRestrict (𝓞 F) F K (𝓞 K) ι).toRingEquiv.toRingHom _ = _ at h
  rw [galRestrict_eq_integerMap] at h
  exact h

/-- The actual class of a nonzero integral ideal in the relative class quotient. -/
def relativeIdealClass (I : NonzeroIdeal K) : RelativeClassQuotient (F := F) (K := K) :=
  QuotientGroup.mk (ClassGroup.mk0 I)

/-- Equality in the relative quotient yields an ordinary base ideal class
and an actual integral representative whose extension corrects the two ideals. -/
theorem same_relativeClass_exists_baseIdeal (B C : NonzeroIdeal K)
    (h : relativeIdealClass (F := F) B = relativeIdealClass (F := F) C) :
    ∃ A : NonzeroIdeal F,
      ClassGroup.mk0 B = ClassGroup.mk0 (ClassGroup.extendedIdeal (𝓞 F) (𝓞 K) A * C) := by
  obtain ⟨a, ha⟩ := QuotientGroup.eq_iff_div_mem.mp h
  obtain ⟨A, hA⟩ := ClassGroup.mk0_surjective a
  refine ⟨A, ?_⟩
  rw [map_mul, ← ClassGroup.extendedHom_mk0, hA, ha]
  simp

/-- Actual integral cross-multipliers are produced by ordinary ideal-class
equality; their existence is a conclusion of the quotient-fiber hypothesis. -/
theorem same_relativeClass_exists_cross_multipliers (B C : NonzeroIdeal K)
    (h : relativeIdealClass (F := F) B = relativeIdealClass (F := F) C) :
    ∃ (A : NonzeroIdeal F) (a b : 𝓞 K), a ≠ 0 ∧ b ≠ 0 ∧
      Ideal.span {a} * B.val =
        Ideal.span {b} * (Ideal.map (algebraMap (𝓞 F) (𝓞 K)) A.val * C.val) := by
  obtain ⟨A, hA⟩ := same_relativeClass_exists_baseIdeal B C h
  obtain ⟨a, b, ha, hb, hab⟩ := ClassGroup.mk0_eq_mk0_iff.mp hA
  exact ⟨A, a, b, ha, hb, hab⟩

/-- The field automorphism on actual nonzero field elements. -/
def fieldUnitInvolution (ι : K ≃ₐ[F] K) : Kˣ ≃* Kˣ :=
  Units.mapEquiv ι.toRingEquiv.toMulEquiv

@[simp] theorem coe_fieldUnitInvolution (ι : K ≃ₐ[F] K) (x : Kˣ) :
    (fieldUnitInvolution ι x : K) = ι (x : K) := rfl

/-- The literal Hilbert-90 ratio `x / ι(x)` as a nonzero field element. -/
def fieldCoboundary (ι : K ≃ₐ[F] K) (x : Kˣ) : Kˣ := x / fieldUnitInvolution ι x

@[simp] theorem coe_fieldCoboundary (ι : K ≃ₐ[F] K) (x : Kˣ) :
    (fieldCoboundary ι x : K) = (x : K) / ι (x : K) := by
  simp [fieldCoboundary, Units.val_div_eq_div_val]

/-- Its relative field norm is exactly one, proved from the actual quadratic
norm formula and involutivity. -/
theorem norm_fieldCoboundary (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (x : Kˣ) :
    Algebra.norm F (fieldCoboundary ι x : K) = 1 := by
  apply (algebraMap F K).injective
  rw [norm_eq_mul_involution ι hι, coe_fieldCoboundary, map_div₀,
    quadratic_automorphism_involutive ι hι, map_one]
  field_simp

end UnitDistance.RelativeIdealCosets
