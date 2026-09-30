module

public import UnitDistance.QuadraticLocalSquareclass

@[expose] public section
set_option backward.privateInPublic true


/-! Local squareclasses and relative odd-prime ramification, using actual
prime ideals and actual localization unramifiedness. -/
noncomputable section
open NumberField
namespace UnitDistance.QuadraticRamification
open KummerInvariant
universe u v w
variable (F : Type u) [Field F] [NumberField F]

/-- Every odd prime has an integral unit in this actual squareclass. -/
def HasOddLocalUnitSquareclass (q : F) : Prop :=
  ∀ (P : Ideal (𝓞 F)), [P.IsPrime] → (2:𝓞 F) ∉ P →
    ∃ (a : 𝓞 F) (c : F), c ≠ 0 ∧ (a:F) = q*c^2 ∧ a ∉ P

variable (K : Type v) [Field K] [NumberField K] [Algebra F K]

/-- Relative unramifiedness at every prime not containing two. -/
def UnramifiedAtOddPrimes : Prop :=
  ∀ (P : Ideal (𝓞 K)), [P.IsPrime] → (2:𝓞 K) ∉ P →
    Algebra.IsUnramifiedAt (𝓞 F) P

/-- Local-unit squareclass representatives map to every number-field extension. -/
theorem HasOddLocalUnitSquareclass.map {q : F}
    (h : HasOddLocalUnitSquareclass F q) :
    HasOddLocalUnitSquareclass K (algebraMap F K q) := by
  intro P hP h2
  let p := P.under (𝓞 F)
  haveI : p.IsPrime := Ideal.comap_isPrime _ P
  have hp2 : (2:𝓞 F) ∉ p := by
    intro hh
    apply h2
    change algebraMap (𝓞 F) (𝓞 K) (2:𝓞 F) ∈ P at hh
    simpa only [map_ofNat] using hh
  obtain ⟨a,c,hc,ha,haP⟩ := h p hp2
  refine ⟨algebraMap (𝓞 F) (𝓞 K) a,algebraMap F K c,
    (map_ne_zero (algebraMap F K)).mpr hc,?_,haP⟩
  change algebraMap F K (a:F) = algebraMap F K q*(algebraMap F K c)^2
  rw [ha,map_mul,map_pow]

/-- A quadratic extension with local-unit squareclass representatives is
unramified at every odd prime. -/
theorem extension_unramifiedAtOddPrimes (q : F) [Fact (Nonsquare q)]
    (h : HasOddLocalUnitSquareclass F q) :
    UnramifiedAtOddPrimes F (Extension q) := by
  intro P hP h2
  let p := P.under (𝓞 F)
  haveI : p.IsPrime := Ideal.comap_isPrime _ P
  have hp2 : (2:𝓞 F) ∉ p := by
    intro hh
    apply h2
    change algebraMap (𝓞 F) (𝓞 (Extension q)) (2:𝓞 F) ∈ P at hh
    simpa only [map_ofNat] using hh
  obtain ⟨a,c,hc,ha,haP⟩ := h p hp2
  exact extension_isUnramifiedAt_of_local_squareclass F q a c hc ha P h2 haP

/-- Identity extensions are unramified. -/
theorem unramifiedAtOddPrimes_refl : UnramifiedAtOddPrimes F F := by
  intro P hP h2
  change Algebra.FormallyUnramified (𝓞 F) (Localization P.primeCompl)
  infer_instance

variable {F K}
variable {L : Type w} [Field L] [NumberField L] [Algebra F L]

/-- Relative odd-prime unramifiedness transports across an actual base-algebra
isomorphism. -/
theorem UnramifiedAtOddPrimes.of_algEquiv (h : UnramifiedAtOddPrimes F K)
    (e : K ≃ₐ[F] L) : UnramifiedAtOddPrimes F L := by
  intro P hP h2
  let eO : 𝓞 K ≃ₐ[𝓞 F] 𝓞 L := RingOfIntegers.mapAlgEquiv e
  let p := P.comap eO.toRingHom
  haveI : p.IsPrime := Ideal.comap_isPrime _ P
  have hp2 : (2:𝓞 K) ∉ p := by
    intro hh
    apply h2
    change eO (2:𝓞 K) ∈ P at hh
    simpa only [map_ofNat] using hh
  haveI : Algebra.IsUnramifiedAt (𝓞 F) p := h p hp2
  exact Algebra.FormallyUnramified.of_equiv (Localization.localAlgEquiv p P eO rfl)

/-- Relative odd-prime unramifiedness composes along actual towers. -/
theorem UnramifiedAtOddPrimes.trans [Algebra K L] [IsScalarTower F K L]
    (hFK : UnramifiedAtOddPrimes F K) (hKL : UnramifiedAtOddPrimes K L) :
    UnramifiedAtOddPrimes F L := by
  intro P hP h2
  let p := P.under (𝓞 K)
  haveI : p.IsPrime := Ideal.comap_isPrime _ P
  haveI : P.LiesOver p := inferInstance
  have hp2 : (2:𝓞 K) ∉ p := by
    intro hh
    apply h2
    change algebraMap (𝓞 K) (𝓞 L) (2:𝓞 K) ∈ P at hh
    simpa only [map_ofNat] using hh
  haveI : Algebra.IsUnramifiedAt (𝓞 F) p := hFK p hp2
  haveI : Algebra.IsUnramifiedAt (𝓞 K) P := hKL P h2
  exact Algebra.IsUnramifiedAt.comp p P

end UnitDistance.QuadraticRamification
