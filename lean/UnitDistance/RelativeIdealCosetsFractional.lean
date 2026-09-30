module

public import UnitDistance.RelativeIdealCosetsBasic

@[expose] public section
set_option backward.privateInPublic true


/-! # Actual conjugation and norm-one generators for arbitrary fractional ideals

This version of relative class cancellation applies to signed prime exponents
as well as to integral one-sided ideals.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped NumberField nonZeroDivisors Classical
open NumberField

namespace UnitDistance.RelativeIdealCosets

open RelativeUnits

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K]

theorem lifted_integerInvolution_eq (ι : K ≃ₐ[F] K) :
    IsFractionRing.ringEquivOfRingEquiv (K := K) (L := K)
      (RingOfIntegers.mapRingEquiv ι.toRingEquiv) = ι.toRingEquiv := by
  have h : (IsFractionRing.ringEquivOfRingEquiv (K := K) (L := K)
      (RingOfIntegers.mapRingEquiv ι.toRingEquiv)).toRingHom = ι.toRingHom := by
    apply IsFractionRing.ringHom_ext (A := 𝓞 K)
    intro a
    exact IsFractionRing.ringEquivOfRingEquiv_algebraMap _ a
  ext x
  exact RingHom.congr_fun h x

/-- Conjugation of the actual fractional-ideal ring, induced by the actual
automorphism of the integers and its unique extension to the field. -/
def conjugateFractionalIdeal (ι : K ≃ₐ[F] K) :
    FractionalIdeal (𝓞 K)⁰ K ≃+* FractionalIdeal (𝓞 K)⁰ K :=
  FractionalIdeal.ringEquivOfRingEquiv K K (RingOfIntegers.mapRingEquiv ι.toRingEquiv)

theorem mem_conjugateFractionalIdeal (ι : K ≃ₐ[F] K)
    (I : FractionalIdeal (𝓞 K)⁰ K) (x : K) :
    x ∈ conjugateFractionalIdeal ι I ↔ ∃ y ∈ I, ι y = x := by
  letI : RingHomInvPair ((RingOfIntegers.mapRingEquiv ι.toRingEquiv) : 𝓞 K →+* 𝓞 K)
      (RingOfIntegers.mapRingEquiv ι.toRingEquiv).symm :=
    RingHomInvPair.of_ringEquiv _
  letI : RingHomInvPair
      ((RingOfIntegers.mapRingEquiv ι.toRingEquiv).symm : 𝓞 K →+* 𝓞 K)
      (RingOfIntegers.mapRingEquiv ι.toRingEquiv) :=
    RingHomInvPair.of_ringEquiv (RingOfIntegers.mapRingEquiv ι.toRingEquiv).symm
  change x ∈ I.val.map (IsFractionRing.semilinearEquivOfRingEquiv K K
    (RingOfIntegers.mapRingEquiv ι.toRingEquiv)).toLinearMap ↔ _
  simp only [Submodule.mem_map, LinearEquiv.coe_coe,
    IsFractionRing.semilinearEquivOfRingEquiv_apply, lifted_integerInvolution_eq]
  rfl

@[simp] theorem conjugateFractionalIdeal_coeIdeal (ι : K ≃ₐ[F] K) (I : Ideal (𝓞 K)) :
    conjugateFractionalIdeal ι (I : FractionalIdeal (𝓞 K)⁰ K) = conjugateIdeal ι I := by
  ext x
  rw [mem_conjugateFractionalIdeal]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp hy
    exact FractionalIdeal.mem_coeIdeal_of_mem _ (Ideal.mem_map_of_mem _ ha)
  · intro hx
    obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal (𝓞 K)⁰).mp hx
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective
      (RingOfIntegers.mapRingHom ι.toRingHom)
      (RingOfIntegers.mapRingEquiv ι.toRingEquiv).surjective).mp ha
    exact ⟨b, FractionalIdeal.mem_coeIdeal_of_mem _ hb, rfl⟩

@[simp] theorem conjugateFractionalIdeal_principal (ι : K ≃ₐ[F] K) (x : K) :
    conjugateFractionalIdeal ι (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ (ι x) := by
  rw [conjugateFractionalIdeal, FractionalIdeal.ringEquivOfRingEquiv_spanSingleton,
    lifted_integerInvolution_eq]
  rfl

/-- The actual automorphism on the group of nonzero fractional ideals. -/
def conjugateIdealGroup (ι : K ≃ₐ[F] K) : IdealGroup K ≃* IdealGroup K :=
  Units.mapEquiv (conjugateFractionalIdeal ι).toMulEquiv

@[simp] theorem conjugateIdealGroup_mk0 (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (I : NonzeroIdeal K) :
    conjugateIdealGroup ι (FractionalIdeal.mk0 K I) =
      FractionalIdeal.mk0 K (conjugateNonzeroIdeal ι hι I) := by
  apply Units.ext
  exact conjugateFractionalIdeal_coeIdeal ι I.val

@[simp] theorem conjugateIdealGroup_principal (ι : K ≃ₐ[F] K) (x : Kˣ) :
    conjugateIdealGroup ι (toPrincipalIdeal (𝓞 K) K x) =
      toPrincipalIdeal (𝓞 K) K (fieldUnitInvolution ι x) := by
  apply Units.ext
  change conjugateFractionalIdeal ι (toPrincipalIdeal (𝓞 K) K x).val = _
  simp only [coe_toPrincipalIdeal, coe_fieldUnitInvolution, conjugateFractionalIdeal_principal]

@[simp] theorem conjugateIdealGroup_extended (ι : K ≃ₐ[F] K) (A : NonzeroIdeal F) :
    conjugateIdealGroup ι
        (FractionalIdeal.mk0 K (ClassGroup.extendedIdeal (𝓞 F) (𝓞 K) A)) =
      FractionalIdeal.mk0 K (ClassGroup.extendedIdeal (𝓞 F) (𝓞 K) A) := by
  apply Units.ext
  exact (conjugateFractionalIdeal_coeIdeal ι _).trans
    (congrArg (fun I : Ideal (𝓞 K) ↦ (I : FractionalIdeal (𝓞 K)⁰ K))
      (conjugateIdeal_extended ι A.val))

/-- The class of an arbitrary nonzero fractional ideal in the actual relative
class quotient. -/
def relativeFractionalClass : IdealGroup K →* RelativeClassQuotient (F := F) (K := K) :=
  (QuotientGroup.mk' (ClassGroup.extendedHom (𝓞 F) (𝓞 K)).range).comp (ClassGroup.mk K)

@[simp] theorem relativeFractionalClass_mk0 (I : NonzeroIdeal K) :
    relativeFractionalClass (F := F) (FractionalIdeal.mk0 K I) = relativeIdealClass (F := F) I := by
  simp [relativeFractionalClass, relativeIdealClass]

/-- Ordinary class equality for actual fractional ideals produces an actual
principal ratio in the chosen field, without choosing a different fraction field. -/
theorem same_fractionalClass_exists_principal (B C : IdealGroup K)
    (h : ClassGroup.mk K B = ClassGroup.mk K C) :
    ∃ x : Kˣ, B / C = toPrincipalIdeal (𝓞 K) K x := by
  have hh := congrArg (ClassGroup.equiv K) h
  simp only [ClassGroup.equiv_mk, FractionalIdeal.canonicalEquiv_self] at hh
  change QuotientGroup.mk (s := (toPrincipalIdeal (𝓞 K) K).range) B = QuotientGroup.mk C at hh
  obtain ⟨x, hx⟩ := QuotientGroup.eq_iff_div_mem.mp hh
  exact ⟨x, hx.symm⟩

/-- The relative class correction is an extended actual base ideal and an
actual principal fractional ideal. -/
theorem same_relativeFractionalClass_exists_corrector (B C : IdealGroup K)
    (h : relativeFractionalClass (F := F) B = relativeFractionalClass (F := F) C) :
    ∃ (A : NonzeroIdeal F) (x : Kˣ),
      B = toPrincipalIdeal (𝓞 K) K x *
        (FractionalIdeal.mk0 K (ClassGroup.extendedIdeal (𝓞 F) (𝓞 K) A) * C) := by
  obtain ⟨a, ha⟩ := QuotientGroup.eq_iff_div_mem.mp h
  obtain ⟨A, hA⟩ := ClassGroup.mk0_surjective a
  have hc : ClassGroup.mk K B = ClassGroup.mk K
      (FractionalIdeal.mk0 K (ClassGroup.extendedIdeal (𝓞 F) (𝓞 K) A) * C) := by
    rw [map_mul, ClassGroup.mk_mk0, ← ClassGroup.extendedHom_mk0, hA, ha]
    simp
  obtain ⟨x, hx⟩ := same_fractionalClass_exists_principal _ _ hc
  exact ⟨A, x, (div_eq_iff_eq_mul).mp hx⟩

/-- The actual anti-invariant map on the entire fractional-ideal group. -/
def fractionalAntiRatio (ι : K ≃ₐ[F] K) : IdealGroup K →* IdealGroup K :=
  MonoidHom.id _ / (conjugateIdealGroup ι).toMonoidHom

@[simp] theorem fractionalAntiRatio_apply (ι : K ≃ₐ[F] K) (B : IdealGroup K) :
    fractionalAntiRatio ι B = B / conjugateIdealGroup ι B := rfl

/-- Equality in the actual relative class quotient produces the literal
norm-one generator for arbitrary nonzero fractional ideals. -/
theorem same_relativeFractionalClass_exists_normOne_generator (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (B C : IdealGroup K)
    (h : relativeFractionalClass (F := F) B = relativeFractionalClass (F := F) C) :
    ∃ x : Kˣ, fractionalAntiRatio ι B / fractionalAntiRatio ι C =
        toPrincipalIdeal (𝓞 K) K (fieldCoboundary ι x) ∧
      Algebra.norm F (fieldCoboundary ι x : K) = 1 := by
  obtain ⟨A, x, hx⟩ := same_relativeFractionalClass_exists_corrector B C h
  refine ⟨x, ?_, norm_fieldCoboundary ι hι x⟩
  rw [hx, map_mul, map_mul]
  have hA : fractionalAntiRatio ι
      (FractionalIdeal.mk0 K (ClassGroup.extendedIdeal (𝓞 F) (𝓞 K) A)) = 1 := by
    simp
  rw [hA, one_mul, mul_div_cancel_right]
  simp [fieldCoboundary, map_div]

end UnitDistance.RelativeIdealCosets
