module

public import UnitDistance.QuadraticUnramifiedOutside

@[expose] public section
set_option backward.privateInPublic true


/-! Transport of actual ramification support across a number-field isomorphism. -/
noncomputable section
open NumberField
namespace UnitDistance.QuadraticRamification
variable {F K : Type*} [Field F] [NumberField F] [Field K] [NumberField K]

theorem UnramifiedAway.of_ringEquiv {N : ℤ} (hF : UnramifiedAway F N)
    (e : F ≃+* K) : UnramifiedAway K N := by
  intro P hP hN
  let eO : 𝓞 F ≃ₐ[ℤ] 𝓞 K :=
    { __ := RingOfIntegers.mapRingEquiv e
      commutes' := fun n => by simp }
  let p : Ideal (𝓞 F) := P.comap eO.toRingHom
  haveI : p.IsPrime := Ideal.comap_isPrime eO.toRingHom P
  have hpN : (N : 𝓞 F) ∉ p := by
    intro h
    apply hN
    change eO (N : 𝓞 F) ∈ P at h
    simpa only [map_intCast] using h
  haveI : Algebra.IsUnramifiedAt ℤ p := hF p hpN
  exact Algebra.FormallyUnramified.of_equiv (Localization.localAlgEquiv p P eO rfl)

theorem UnramifiedAway.of_algEquiv {N : ℤ} (hF : UnramifiedAway F N)
    (e : F ≃ₐ[ℚ] K) : UnramifiedAway K N := hF.of_ringEquiv e.toRingEquiv

end UnitDistance.QuadraticRamification
