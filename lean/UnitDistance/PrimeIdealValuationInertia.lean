module

public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Completion.ExtensionIndex
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.Ramification.HilbertRamification.LocalizationRamificationGroups

@[expose] public section
set_option backward.privateInPublic true


/-! Comparison of actual inertia at a prime ideal and at its valuation ring. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open NumberField IsDedekindDomain
open scoped Pointwise
namespace UnitDistance.PrimeCompletion
open HilbertRamification AlgebraicNumberTheory.Valuations
variable (M : Type) [Field M] [NumberField M] [IsGalois ℚ M]
variable (v : HeightOneSpectrum (𝓞 ℚ))
  (w : AbsoluteValueExtension (HeightOneSpectrum.adicAbv ℚ v) M)

/-- Congruence on algebraic integers extends to the whole local valuation ring. -/
theorem prime_inertia_displacement
    (σ : absoluteValueDecompositionGroup ℚ w.1)
    (hσ : (σ : Gal(M/ℚ)) ∈ (finitePlaceExtensionCentre v w).asIdeal.inertia Gal(M/ℚ))
    (x : M) (hx : w.1 x ≤ 1) : w.1 (σ.val x-x)<1 := by
  have hi : ∀a : 𝓞 M, w.1 (σ.val (a:M)-(a:M))<1 := by
    intro a
    have h := (HilbertRamification.Dedekind.mem_inertiaGroup_iff).mp hσ a
    exact (mem_finitePlaceExtensionCentreIdeal_iff v w _).mp h
  have hmem : x ∈ (finitePlaceExtensionCentre v w).valuationSubringAtPrime M := by
    rw [←finitePlaceExtensionValuationSubring_eq_localization v w]
    exact hx
  obtain ⟨a,s,hs,hxs⟩ := hmem
  have ha : w.1 (a:M) ≤ 1 := ringOfIntegers_mem_finitePlaceExtensionValuationSubring v w a
  have hs1 : w.1 (s:M)=1 := by
    apply le_antisymm
    · exact ringOfIntegers_mem_finitePlaceExtensionValuationSubring v w s
    · apply le_of_not_gt
      intro hlt
      exact hs ((mem_finitePlaceExtensionCentreIdeal_iff v w s).mpr hlt)
  have hσs : w.1 (σ.val (s:M))=1 := by
    rw [absoluteValueDecompositionGroup_preserves_absoluteValue
      (HeightOneSpectrum.adicAbv ℚ v) (RayClass.adicAbv_isNontrivial v) w σ,hs1]
  have hs0 : (s:M)≠0 := by intro h; simpa [h] using hs1
  have hσs0 : σ.val (s:M)≠0 := (map_ne_zero σ.val).mpr hs0
  have heq : σ.val ((a:M)/(s:M))-(a:M)/(s:M) =
      ((σ.val (a:M)-(a:M))*(s:M)-(a:M)*(σ.val (s:M)-(s:M))) /
        (σ.val (s:M)*(s:M)) := by
    rw [map_div₀]
    field_simp
    <;> ring
  have hstrong := LubinTate.Valuations.strong_triangle_of_nonarchimedean w.1
    (finitePlaceExtension_nonarchimedean v w)
  have hnum : w.1 ((σ.val (a:M)-(a:M))*(s:M)-(a:M)*(σ.val (s:M)-(s:M)))<1 := by
    rw [sub_eq_add_neg]
    apply lt_of_le_of_lt (hstrong _ _) ?_
    rw [AbsoluteValue.map_neg, max_lt_iff]
    constructor
    · simpa [map_mul,hs1] using hi a
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left (w.1.nonneg _) ha) (hi s)
  rw [hxs]
  change w.1 (σ.val ((a:M)*(s:M)⁻¹)-(a:M)*(s:M)⁻¹)<1
  rw [←div_eq_mul_inv,heq,map_div₀,map_mul,hσs,hs1,mul_one,div_one]
  exact hnum

/-- Exact equivalence of the ideal and valuation-ring inertia conditions. -/
theorem prime_inertia_iff_valuation_inertia
    (σ : absoluteValueDecompositionGroup ℚ w.1) :
    (σ : Gal(M/ℚ)) ∈ (finitePlaceExtensionCentre v w).asIdeal.inertia Gal(M/ℚ) ↔
      localizationRamificationGroups_absoluteValueDecompositionGroupEquiv
        (HeightOneSpectrum.adicAbv ℚ v) (RayClass.adicAbv_isNontrivial v) w
        (finitePlaceExtension_nonarchimedean v w) σ ∈
      RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup ℚ
        (finitePlaceExtensionValuationSubring v w) := by
  rw [ValuationSubring.mem_inertiaGroup_iff_sub_mem_nonunits]
  constructor
  · intro h x
    apply (algebraicLocalizationDensity_mem_nonunits_iff_abs_lt_one w.1
      (finitePlaceExtension_nonarchimedean v w) _).mpr
    exact prime_inertia_displacement M v w σ h x x.property
  · intro h
    rw [HilbertRamification.Dedekind.mem_inertiaGroup_iff]
    intro x
    apply (mem_finitePlaceExtensionCentreIdeal_iff v w _).mpr
    let xA : finitePlaceExtensionValuationSubring v w :=
      ⟨x,ringOfIntegers_mem_finitePlaceExtensionValuationSubring v w x⟩
    exact (algebraicLocalizationDensity_mem_nonunits_iff_abs_lt_one w.1
      (finitePlaceExtension_nonarchimedean v w) _).mp (h xA)

end UnitDistance.PrimeCompletion
