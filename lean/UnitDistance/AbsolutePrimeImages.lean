module

public import UnitDistance.AbsoluteDecompositionPrime
public import UnitDistance.RationalInertiaBaseChange
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Completion.ExtensionIndex

@[expose] public section
set_option backward.privateInPublic true


/-! Actual finite inertia and decomposition images at rational primes. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open NumberField IsDedekindDomain
namespace UnitDistance.PrimeCompletion
open ArithmeticProP LocalClassFieldTheory
attribute [local instance] primeFact baseRationalAlgebra
variable (p : Nat.Primes) (M : Type) [Field M] [NumberField M] [IsGalois ℚ M]
  (j : M →ₐ[ℚ] AlgebraicClosure ℚ)

/-- The actual decomposition image has the actual product `e*f` as its cardinality. -/
theorem decompositionRestriction_card :
    Nat.card (decompositionRestriction p M j).range=
      (NumberFieldAnalysis.rationalPrimeIdeal p.val).ramificationIdxIn (𝓞 M)*
      (NumberFieldAnalysis.rationalPrimeIdeal p.val).inertiaDegIn (𝓞 M) := by
  let P := restrictedAbsolutePrime M p j
  letI : P.asIdeal.LiesOver (NumberFieldAnalysis.rationalPrimeIdeal p.val) :=
    restrictedAbsolutePrime_liesOver M p j
  rw [decompositionRestriction_range M p j]
  exact Ideal.card_stabilizer_eq (G:=Gal(M/ℚ))
    (NumberFieldAnalysis.rationalPrimeIdeal p.val) P.asIdeal

/-- Actual absolute inertia restricts into inertia of its actual center prime. -/
theorem inertiaRestriction_range_le :
    (inertiaRestriction p M j).range ≤
      (restrictedAbsolutePrime M p j).asIdeal.inertia Gal(M/ℚ) := by
  rintro _ ⟨σ,rfl⟩
  rw [HilbertRamification.Dedekind.mem_inertiaGroup_iff]
  intro x
  apply (mem_finitePlaceExtensionCentreIdeal_iff (place p)
    (restrictedAbsolutePlace M p j) _).mpr
  let w := ClassFieldTower.Martinet.Shafarevich.finitePlaceAbsoluteValueExtension ℚ (place p)
  let A := ClassFieldTower.Martinet.Shafarevich.finitePlaceAbsoluteValuationSubring ℚ (place p)
  let τ := ClassFieldTower.Martinet.Shafarevich.finitePlaceAbsoluteDecompositionValuationEquiv
    ℚ (place p) σ.val
  have hτ : τ∈RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup ℚ A :=
    σ.property
  let xA : A := ⟨j (x:M),
    ringOfIntegers_mem_finitePlaceExtensionValuationSubring (place p)
      (restrictedAbsolutePlace M p j) x⟩
  have hx := (HilbertRamification.ValuationSubring.mem_inertiaGroup_iff_sub_mem_nonunits A τ).mp hτ xA
  have hlt := (HilbertRamification.algebraicLocalizationDensity_mem_nonunits_iff_abs_lt_one
    w.1 (ClassFieldTower.Martinet.Shafarevich.finitePlaceAbsoluteValueExtension_nonarchimedean
      ℚ (place p)) _).mp hx
  change w.1 (j ((GaloisEmbedding.restriction j σ.val.val) (x:M)-(x:M)))<1
  rw [map_sub,GaloisEmbedding.restriction_commutes]
  exact hlt

end UnitDistance.PrimeCompletion
