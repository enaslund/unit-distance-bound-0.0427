module

public import UnitDistance.RelativeUnitsCohomology
public import UnitDistance.RelativeUnitsIdealDescent

@[expose] public section
set_option backward.privateInPublic true


/-! Actual capitulation representatives and their norm-one unit cocycles. -/

noncomputable section
open NumberField
open scoped nonZeroDivisors

namespace UnitDistance.RelativeUnits

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [Algebra.IsQuadraticExtension F K]

/-- An integral generator equation gives an actual norm-one unit, by cancelling
its nonzero generator after applying the quadratic involution twice. -/
theorem normOne_of_generator_equation (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (u : (𝓞 K)ˣ) (x : 𝓞 K) (hx : x ≠ 0)
    (he : (u : 𝓞 K) * RingOfIntegers.mapRingHom ι.toRingHom x = x) :
    u ∈ normOneUnits (F := F) := by
  have hxK : (x : K) ≠ 0 := by simpa using RingOfIntegers.coe_injective.ne hx
  have heK : (u : K) * ι (x : K) = (x : K) :=
    congrArg (algebraMap (𝓞 K) K) he
  have hi := congrArg ι heK
  rw [map_mul, quadratic_automorphism_involutive ι hι] at hi
  rw [mem_normOneUnits_iff ι hι]
  apply NumberField.Units.coe_injective K
  change (u : K) * ι (u : K) = 1
  apply mul_right_cancel₀ hxK
  calc
    (u : K) * ι (u : K) * (x : K) = (u : K) * (ι (u : K) * (x : K)) := mul_assoc _ _ _
    _ = (u : K) * ι (x : K) := by rw [hi]
    _ = (x : K) := heK
    _ = 1 * (x : K) := (one_mul _).symm

/-- Every actual capitulating nonzero integral ideal admits an integral
principal generator and its norm-one unit cocycle. -/
theorem capitulation_representative_has_unit
    (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (a : (Ideal (𝓞 F))⁰)
    (ha : ClassGroup.mk0 a ∈ (ClassGroup.extendedHom (𝓞 F) (𝓞 K)).ker) :
    ∃ (x : 𝓞 K) (u : (𝓞 K)ˣ), x ≠ 0 ∧
      Ideal.map (algebraMap (𝓞 F) (𝓞 K)) a.val = Ideal.span {x} ∧
      u ∈ normOneUnits (F := F) ∧
      (u : 𝓞 K) * RingOfIntegers.mapRingHom ι.toRingHom x = x := by
  have hp : (Ideal.map (algebraMap (𝓞 F) (𝓞 K)) a.val).IsPrincipal := by
    apply (ClassGroup.mk0_eq_one_iff (ClassGroup.extendedIdeal (𝓞 F) (𝓞 K) a).property).mp
    exact (ClassGroup.extendedHom_mk0 (𝓞 F) (𝓞 K) a).symm.trans ha
  obtain ⟨x, hgen⟩ := hp.principal
  have hx : x ≠ 0 := by
    intro hx
    have hz : Ideal.map (algebraMap (𝓞 F) (𝓞 K)) a.val = ⊥ := by
      simpa [hx] using hgen
    exact Ideal.map_ne_bot_of_ne_bot (mem_nonZeroDivisors_iff_ne_zero.mp a.property) hz
  have hmap := extendedIdeal_invariant (F := F) (K := K) a.val ι
  change Ideal.map (galRestrict (𝓞 F) F K (𝓞 K) ι).toRingEquiv.toRingHom _ = _ at hmap
  rw [hgen, galRestrict_eq_integerMap, Ideal.map_span, Set.image_singleton] at hmap
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hmap
  have he : (u : 𝓞 K) * RingOfIntegers.mapRingHom ι.toRingHom x = x := by
    simpa only [mul_comm] using hu
  exact ⟨x, u, hx, hgen, normOne_of_generator_equation ι hι u x hx he, he⟩

omit [NumberField K] in
lemma coe_integralUnit_div (u v : (𝓞 K)ˣ) :
    ((u / v : (𝓞 K)ˣ) : K) = (u : K) / (v : K) := by
  change ((Units.map (algebraMap (𝓞 K) K) (u / v) : Kˣ) : K) = _
  rw [map_div, Units.val_div_eq_div_val]
  rfl

omit [NumberField F] [NumberField K] [Algebra.IsQuadraticExtension F K] in
/-- The cocycle computed from an integral generator is its ordinary field ratio. -/
theorem generator_unit_eq_div (ι : K ≃ₐ[F] K) (u : (𝓞 K)ˣ)
    (x : 𝓞 K) (hx : x ≠ 0)
    (he : (u : 𝓞 K) * RingOfIntegers.mapRingHom ι.toRingHom x = x) :
    (u : K) = (x : K) / ι (x : K) := by
  have hxK : (x : K) ≠ 0 := by simpa using RingOfIntegers.coe_injective.ne hx
  apply (eq_div_iff (by simpa using ι.injective.ne hxK)).mpr
  exact congrArg (algebraMap (𝓞 K) K) he

/-- Two generator cocycles differ by the specified integral unit coboundary
exactly when their generators differ, after that unit correction, by a fixed
field element. -/
theorem coboundary_eq_ratio_iff_fixed_generator_ratio
    (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (u v : normOneUnits (F := F) (K := K))
    (x y : 𝓞 K) (hx : x ≠ 0) (hy : y ≠ 0)
    (hux : (u.val : 𝓞 K) * RingOfIntegers.mapRingHom ι.toRingHom x = x)
    (hvy : (v.val : 𝓞 K) * RingOfIntegers.mapRingHom ι.toRingHom y = y)
    (ε : (𝓞 K)ˣ) :
    unitCoboundary ι hι ε = u / v ↔
      ι ((x : K) / ((ε : K) * (y : K))) = (x : K) / ((ε : K) * (y : K)) := by
  have hxK : (x : K) ≠ 0 := by simpa using RingOfIntegers.coe_injective.ne hx
  have hyK : (y : K) ≠ 0 := by simpa using RingOfIntegers.coe_injective.ne hy
  have hix : ι (x : K) ≠ 0 := by simpa using ι.injective.ne hxK
  have hiy : ι (y : K) ≠ 0 := by simpa using ι.injective.ne hyK
  have heK := NumberField.Units.coe_ne_zero ε
  have hie : ι (ε : K) ≠ 0 := by simp
  rw [← Subtype.val_inj, ← (NumberField.Units.coe_injective K).eq_iff]
  change ((ε / unitInvolution ι ε : (𝓞 K)ˣ) : K) =
    ((u.val / v.val : (𝓞 K)ˣ) : K) ↔ _
  rw [coe_integralUnit_div, coe_integralUnit_div, coe_unitInvolution,
    generator_unit_eq_div ι u.val x hx hux, generator_unit_eq_div ι v.val y hy hvy,
    map_div₀, map_mul]
  field_simp

/-- Fixed field elements descend through the actual quadratic algebra map. -/
theorem invariant_field_descends (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (z : K)
    (hz : ι z = z) : ∃ a : F, algebraMap F K a = z := by
  apply (IsGalois.mem_range_algebraMap_iff_fixed (F := F) z).mpr
  intro g
  rcases automorphism_eq_one_or ι hι g with hg | hg
  · rw [hg]; rfl
  · rw [hg]; exact hz

/-- Equality of base ideal classes is equivalent to a fixed field ratio of
principal generators after correction by one actual integral unit. -/
theorem same_class_iff_fixed_generator_ratio
    (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (A B : (Ideal (𝓞 F))⁰) (x y : 𝓞 K) (hx : x ≠ 0) (hy : y ≠ 0)
    (hA : Ideal.map (algebraMap (𝓞 F) (𝓞 K)) A.val = Ideal.span {x})
    (hB : Ideal.map (algebraMap (𝓞 F) (𝓞 K)) B.val = Ideal.span {y}) :
    ClassGroup.mk0 A = ClassGroup.mk0 B ↔ ∃ ε : (𝓞 K)ˣ,
      ι ((x : K) / ((ε : K) * (y : K))) = (x : K) / ((ε : K) * (y : K)) := by
  have hxK : (x : K) ≠ 0 := by simpa using RingOfIntegers.coe_injective.ne hx
  have hyK : (y : K) ≠ 0 := by simpa using RingOfIntegers.coe_injective.ne hy
  constructor
  · intro hclasses
    obtain ⟨a, b, ha, hb, hab⟩ := ClassGroup.mk0_eq_mk0_iff.mp hclasses
    have hspan := congrArg (Ideal.map (algebraMap (𝓞 F) (𝓞 K))) hab
    simp only [Ideal.map_mul, Ideal.map_span, Set.image_singleton, hA, hB,
      Ideal.span_singleton_mul_span_singleton] at hspan
    obtain ⟨ε, he⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan.symm
    refine ⟨ε, ?_⟩
    have haK : algebraMap F K (a : F) ≠ 0 := by
      simpa using (algebraMap F K).injective.ne
        (show (a : F) ≠ 0 by simpa using RingOfIntegers.coe_injective.ne ha)
    have heK := congrArg (algebraMap (𝓞 K) K) he
    change (algebraMap F K (b : F) * (y : K)) * (ε : K) =
      algebraMap F K (a : F) * (x : K) at heK
    have hz : (x : K) / ((ε : K) * (y : K)) = algebraMap F K ((b : F) / (a : F)) := by
      rw [map_div₀]
      apply (div_eq_div_iff (mul_ne_zero (NumberField.Units.coe_ne_zero ε) hyK) haK).mpr
      linear_combination -heK
    rw [hz]
    exact ι.commutes _
  · rintro ⟨ε, hfix⟩
    obtain ⟨z, hz⟩ := invariant_field_descends ι hι _ hfix
    have heK := NumberField.Units.coe_ne_zero ε
    have hz0 : z ≠ 0 := by
      intro hz0
      rw [hz0, map_zero] at hz
      exact (div_ne_zero hxK (mul_ne_zero heK hyK)) hz.symm
    obtain ⟨b, a, ha, hba⟩ := IsFractionRing.div_surjective (𝓞 F) z
    have ha0 : a ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp ha
    have hb0 : b ≠ 0 := by
      intro hb0
      rw [hb0, map_zero, zero_div] at hba
      exact hz0 hba.symm
    have haK : algebraMap F K (a : F) ≠ 0 := by
      simpa using (algebraMap F K).injective.ne
        (show (a : F) ≠ 0 by simpa using RingOfIntegers.coe_injective.ne ha0)
    have hcrossK : algebraMap F K (a : F) * (x : K) =
        algebraMap F K (b : F) * (ε : K) * (y : K) := by
      rw [← hba, map_div₀] at hz
      have hc := (div_eq_div_iff haK (mul_ne_zero heK hyK)).mp hz
      linear_combination -hc
    have hcross : algebraMap (𝓞 F) (𝓞 K) a * x =
        (algebraMap (𝓞 F) (𝓞 K) b * y) * (ε : 𝓞 K) := by
      apply RingOfIntegers.coe_injective
      change algebraMap F K (a : F) * (x : K) =
        (algebraMap F K (b : F) * (y : K)) * (ε : K)
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hcrossK
    apply ClassGroup.mk0_eq_mk0_iff.mpr
    refine ⟨a, b, ha0, hb0, extendedIdeal_injective (F := F) (K := K) ?_⟩
    simp only [Ideal.map_mul, Ideal.map_span, Set.image_singleton, hA, hB,
      Ideal.span_singleton_mul_span_singleton]
    rw [hcross, Ideal.span_singleton_mul_right_unit ε.isUnit]

/-- Actual class equality is exactly equality of the two cyclic unit-cohomology
classes attached to principal generators. This establishes representative
independence in both directions. -/
theorem same_class_iff_unitH1_eq
    (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (A B : (Ideal (𝓞 F))⁰) (x y : 𝓞 K) (hx : x ≠ 0) (hy : y ≠ 0)
    (hA : Ideal.map (algebraMap (𝓞 F) (𝓞 K)) A.val = Ideal.span {x})
    (hB : Ideal.map (algebraMap (𝓞 F) (𝓞 K)) B.val = Ideal.span {y})
    (u v : normOneUnits (F := F) (K := K))
    (hux : (u.val : 𝓞 K) * RingOfIntegers.mapRingHom ι.toRingHom x = x)
    (hvy : (v.val : 𝓞 K) * RingOfIntegers.mapRingHom ι.toRingHom y = y) :
    ClassGroup.mk0 A = ClassGroup.mk0 B ↔
      (QuotientGroup.mk u : UnitH1 ι hι) = QuotientGroup.mk v := by
  rw [same_class_iff_fixed_generator_ratio ι hι A B x y hx hy hA hB,
    QuotientGroup.eq_iff_div_mem]
  change (∃ ε, _) ↔ ∃ ε, unitCoboundary ι hι ε = u / v
  exact exists_congr fun ε ↦
    (coboundary_eq_ratio_iff_fixed_generator_ratio ι hι u v x y hx hy hux hvy ε).symm

/-- The actual capitulation kernel of ideal-class extension. -/
abbrev CapitulationKernel := (ClassGroup.extendedHom (𝓞 F) (𝓞 K)).ker

/-- A principal-generator representative of one actual capitulating ideal class. -/
structure CapitulationData (ι : K ≃ₐ[F] K) (c : CapitulationKernel (F := F) (K := K)) where
  ideal : (Ideal (𝓞 F))⁰
  generator : 𝓞 K
  unit : normOneUnits (F := F) (K := K)
  class_eq : ClassGroup.mk0 ideal = c.val
  generator_ne_zero : generator ≠ 0
  extended_eq : Ideal.map (algebraMap (𝓞 F) (𝓞 K)) ideal.val = Ideal.span {generator}
  equation : (unit.val : 𝓞 K) * RingOfIntegers.mapRingHom ι.toRingHom generator = generator

theorem nonempty_capitulationData (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (c : CapitulationKernel (F := F) (K := K)) : Nonempty (CapitulationData ι c) := by
  obtain ⟨A, hA⟩ := ClassGroup.mk0_surjective c.val
  have hker : ClassGroup.mk0 A ∈ (ClassGroup.extendedHom (𝓞 F) (𝓞 K)).ker := hA ▸ c.property
  obtain ⟨x, u, hx, he, hu, hux⟩ := capitulation_representative_has_unit ι hι A hker
  exact ⟨⟨A, x, ⟨u, hu⟩, hA, hx, he, hux⟩⟩

/-- Choice of ordinary principal-generator data; its cohomology class is proved
independent of the choice by `same_class_iff_unitH1_eq`. -/
def capitulationData (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (c : CapitulationKernel (F := F) (K := K)) : CapitulationData ι c :=
  Classical.choice (nonempty_capitulationData ι hι c)

/-- The actual capitulation-to-unit-cohomology map. -/
def capitulationToUnitH1 (ι : K ≃ₐ[F] K) (hι : ι ≠ 1)
    (c : CapitulationKernel (F := F) (K := K)) : UnitH1 ι hι :=
  QuotientGroup.mk (capitulationData ι hι c).unit

/-- Capitulation injects into cyclic unit cohomology. This does not require
unramifiedness at finite primes. -/
theorem capitulationToUnitH1_injective (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    Function.Injective (capitulationToUnitH1 ι hι) := by
  intro c d h
  let C := capitulationData ι hι c
  let D := capitulationData ι hι d
  have hc := (same_class_iff_unitH1_eq ι hι C.ideal D.ideal C.generator D.generator
    C.generator_ne_zero D.generator_ne_zero C.extended_eq D.extended_eq C.unit D.unit
    C.equation D.equation).mpr h
  apply Subtype.ext
  exact C.class_eq.symm.trans (hc.trans D.class_eq)

/-- Finite-unramified ideal descent proves surjectivity onto actual cyclic
unit cohomology, with no capitulation cardinality premise. -/
theorem capitulationToUnitH1_surjective
    (hunr : NumberFieldAnalysis.FiniteUnramified F K)
    (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    Function.Surjective (capitulationToUnitH1 ι hι) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H u =>
    obtain ⟨A, x, hAker, hx, hA, hux⟩ :=
      normOneUnit_from_capitulation_kernel hunr ι hι u.val u.property
    let c : CapitulationKernel (F := F) (K := K) := ⟨ClassGroup.mk0 A, hAker⟩
    let C := capitulationData ι hι c
    refine ⟨c, ?_⟩
    exact (same_class_iff_unitH1_eq ι hι C.ideal A C.generator x
      C.generator_ne_zero hx C.extended_eq hA C.unit u C.equation hux).mp C.class_eq

/-- A proved equivalence between the actual capitulation kernel and the actual
norm-one/coboundary quotient in a finite-unramified quadratic extension. -/
def capitulationEquivUnitH1
    (hunr : NumberFieldAnalysis.FiniteUnramified F K)
    (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    CapitulationKernel (F := F) (K := K) ≃ UnitH1 ι hι :=
  Equiv.ofBijective (capitulationToUnitH1 ι hι)
    ⟨capitulationToUnitH1_injective ι hι, capitulationToUnitH1_surjective hunr ι hι⟩

/-- The exact capitulation cardinality reduces to the genuine unit quotient.
The Herbrand rank formula determining this cardinality is proved separately
in `RelativeUnitsHerbrand`. -/
theorem capitulation_card_eq_unitH1_card
    (hunr : NumberFieldAnalysis.FiniteUnramified F K)
    (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) :
    Nat.card (CapitulationKernel (F := F) (K := K)) = Nat.card (UnitH1 ι hι) :=
  Nat.card_congr (capitulationEquivUnitH1 hunr ι hι)

end UnitDistance.RelativeUnits
