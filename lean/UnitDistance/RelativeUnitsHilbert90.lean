module

public import UnitDistance.RelativeUnits
public import Mathlib.Algebra.Group.Units.Equiv

@[expose] public section
set_option backward.privateInPublic true


/-! The actual quadratic unit involution and integral Hilbert 90. -/

noncomputable section
open scoped NumberField
open NumberField

namespace UnitDistance.RelativeUnits

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K]

/-- Restriction of the specified field automorphism to the actual integral units. -/
def unitInvolution (ι : K ≃ₐ[F] K) : (𝓞 K)ˣ ≃* (𝓞 K)ˣ :=
  Units.mapEquiv (RingOfIntegers.mapRingEquiv ι.toRingEquiv).toMulEquiv

omit [NumberField F] [NumberField K] [Algebra.IsQuadraticExtension F K] in
@[simp] theorem coe_unitInvolution (ι : K ≃ₐ[F] K) (u : (𝓞 K)ˣ) :
    (unitInvolution ι u : K) = ι (u : K) := rfl

lemma quadratic_automorphism_involutive (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    Function.Involutive ι := by
  have hs : ι * ι = 1 := by
    rcases automorphism_eq_one_or ι hι (ι * ι) with h | h
    · exact h
    · exact False.elim (hι (mul_left_cancel (show ι * ι = ι * 1 by simpa using h)))
  intro x
  exact DFunLike.congr_fun hs x

lemma unitInvolution_involutive (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    Function.Involutive (unitInvolution ι) := by
  intro u
  apply NumberField.Units.coe_injective K
  simpa only [coe_unitInvolution] using quadratic_automorphism_involutive ι hι (u : K)

/-- Involution description of the actual norm-one unit group. -/
theorem mem_normOneUnits_iff (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (u : (𝓞 K)ˣ) :
    u ∈ normOneUnits (F := F) ↔ u * unitInvolution ι u = 1 := by
  change unitNorm (F := F) u = 1 ↔ _
  rw [← (NumberField.Units.coe_injective F).eq_iff,
    ← (algebraMap F K).injective.eq_iff,
    ← (NumberField.Units.coe_injective K).eq_iff]
  simp only [coe_unitNorm, NumberField.Units.coe_one, map_one,
    norm_eq_mul_involution ι hι, NumberField.Units.coe_mul, coe_unitInvolution]

/-- Every automorphism belongs to the cyclic subgroup of the nontrivial one. -/
lemma quadratic_generator (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    ∀ g : K ≃ₐ[F] K, g ∈ Subgroup.zpowers ι := by
  intro g
  rcases automorphism_eq_one_or ι hι g with h | h
  · rw [h]
    exact (Subgroup.zpowers ι).one_mem
  · rw [h]
    exact Subgroup.mem_zpowers ι

/-- Hilbert 90 for the actual unit norm, with a nonzero field generator. -/
theorem exists_field_generator (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (u : (𝓞 K)ˣ) (hu : u ∈ normOneUnits (F := F)) :
    ∃ x : Kˣ, (x : K) / ι (x : K) = (u : K) := by
  apply groupCohomology.exists_div_of_norm_eq_one (quadratic_generator ι hι)
  exact congrArg (fun v : (𝓞 F)ˣ ↦ (v : F)) hu

/-- Integral Hilbert 90 produces an actual nonzero algebraic integer. -/
theorem exists_integral_generator (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (u : (𝓞 K)ˣ) (hu : u ∈ normOneUnits (F := F)) :
    ∃ x : 𝓞 K, x ≠ 0 ∧ (u : 𝓞 K) * RingOfIntegers.mapRingHom ι.toRingHom x = x := by
  have hn : Algebra.norm F (u : K) = 1 :=
    congrArg (fun v : (𝓞 F)ˣ ↦ (v : F)) hu
  obtain ⟨x, hx, he⟩ := groupCohomology.exists_mul_galRestrict_of_norm_eq_one
    (A := 𝓞 F) (K := F) (L := K) (B := 𝓞 K) (quadratic_generator ι hι) hn
  refine ⟨x, hx, ?_⟩
  apply RingOfIntegers.coe_injective
  change (u : K) * ι (x : K) = (x : K)
  have hf := congrArg (algebraMap (𝓞 K) K) he
  simpa only [map_mul, algebraMap_galRestrict_apply] using hf

/-- The integral Hilbert-90 generator has an invariant ordinary principal ideal.
Finite unramified ideal descent, which is separate, is not assumed here. -/
theorem exists_invariant_principal_ideal (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (u : (𝓞 K)ˣ) (hu : u ∈ normOneUnits (F := F)) :
    ∃ x : 𝓞 K, x ≠ 0 ∧
      (u : 𝓞 K) * RingOfIntegers.mapRingHom ι.toRingHom x = x ∧
      Ideal.map (RingOfIntegers.mapRingHom ι.toRingHom) (Ideal.span {x}) =
        Ideal.span {x} := by
  obtain ⟨x, hx, he⟩ := exists_integral_generator ι hι u hu
  refine ⟨x, hx, he, ?_⟩
  rw [Ideal.map_span, Set.image_singleton]
  calc
    Ideal.span {RingOfIntegers.mapRingHom ι.toRingHom x} =
        Ideal.span {(u : 𝓞 K) * RingOfIntegers.mapRingHom ι.toRingHom x} :=
      (Ideal.span_singleton_mul_left_unit u.isUnit _).symm
    _ = Ideal.span {x} := by rw [he]

/-- An invariant algebraic integer in a quadratic extension descends to an
actual algebraic integer in the base field. -/
theorem invariant_integer_descends (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (x : 𝓞 K) (hx : ι (x : K) = (x : K)) :
    ∃ a : 𝓞 F, algebraMap (𝓞 F) (𝓞 K) a = x := by
  have hfix : (x : K) ∈ (⊥ : IntermediateField F K) := by
    apply (IsGalois.mem_bot_iff_fixed (F := F) (x : K)).mpr
    intro g
    rcases automorphism_eq_one_or ι hι g with hg | hg
    · rw [hg]; rfl
    · rw [hg]; exact hx
  obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp hfix
  have haint : IsIntegral ℤ a := by
    apply (isIntegral_algebraMap_iff (R := ℤ) (A := F) (B := K)).mp
    rw [ha]
    exact x.property
  refine ⟨⟨a, haint⟩, ?_⟩
  exact RingOfIntegers.coe_injective ha

/-- The fixed units are exactly the embedded base-field units, with actual
integral descent of both a unit and its inverse. -/
theorem unitInvolution_fixed_iff (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (u : (𝓞 K)ˣ) :
    unitInvolution ι u = u ↔
      ∃ v : (𝓞 F)ˣ, Units.map (algebraMap (𝓞 F) (𝓞 K)) v = u := by
  constructor
  · intro hu
    have huf : ι (u : K) = (u : K) := congrArg (fun v : (𝓞 K)ˣ ↦ (v : K)) hu
    obtain ⟨a, ha⟩ := invariant_integer_descends ι hι (u : 𝓞 K) huf
    have hui : unitInvolution ι u⁻¹ = u⁻¹ := by rw [map_inv, hu]
    obtain ⟨b, hb⟩ := invariant_integer_descends ι hι (u⁻¹ : (𝓞 K)ˣ)
      (congrArg (fun v : (𝓞 K)ˣ ↦ (v : K)) hui)
    have hab : a * b = 1 := by
      apply FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K)
      rw [map_mul, map_one, ha, hb]
      exact u.val_inv
    let v : (𝓞 F)ˣ := ⟨a, b, hab, by simpa [mul_comm] using hab⟩
    exact ⟨v, Units.ext ha⟩
  · rintro ⟨v, rfl⟩
    apply NumberField.Units.coe_injective K
    change ι (algebraMap F K (v : F)) = algebraMap F K (v : F)
    exact ι.commutes (v : F)

end UnitDistance.RelativeUnits
