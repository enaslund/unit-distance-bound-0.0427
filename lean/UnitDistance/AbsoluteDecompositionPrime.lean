module

public import UnitDistance.RationalLocalFiniteRestriction
public import UnitDistance.GaloisPrimeConjugation
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Completion.ExtensionIndex
public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Galois.CyclicPrimeSubextension

@[expose] public section
set_option backward.privateInPublic true


/-! The actual image of the chosen rational absolute decomposition group is
the stabilizer of an actual prime ideal of each finite Galois field. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open NumberField IsDedekindDomain
open scoped Pointwise
namespace UnitDistance.PrimeCompletion
open HilbertRamification AlgebraicNumberTheory.Valuations
open ClassFieldTower.Martinet.Shafarevich GaloisPrimeConjugation
attribute [local instance] primeFact baseRationalAlgebra
variable (M : Type) [Field M] [NumberField M] [IsGalois ℚ M]

private theorem centre_conjugate_ideal (v : HeightOneSpectrum (𝓞 ℚ))
    (w : AbsoluteValueExtension (HeightOneSpectrum.adicAbv ℚ v) M) (σ : Gal(M/ℚ)) :
    (finitePlaceExtensionCentre v
      (absoluteValueExtensionConjugate (HeightOneSpectrum.adicAbv ℚ v) w σ)).asIdeal =
        σ⁻¹ • (finitePlaceExtensionCentre v w).asIdeal := by
  rw [finitePlaceExtensionCentre_conjugate,finitePlaceEquiv_asIdeal,galois_smul_ideal]
  rfl

/-- The finite valuation decomposition group equals the literal prime-ideal stabilizer. -/
theorem absoluteValueDecompositionGroup_eq_prime_stabilizer
    (v : HeightOneSpectrum (𝓞 ℚ))
    (w : AbsoluteValueExtension (HeightOneSpectrum.adicAbv ℚ v) M) :
    absoluteValueDecompositionGroup ℚ w.1 =
      MulAction.stabilizer Gal(M/ℚ) (finitePlaceExtensionCentre v w).asIdeal := by
  ext σ
  rw [mem_absoluteValueDecompositionGroup_iff_extensionConjugate_eq
    (HeightOneSpectrum.adicAbv ℚ v) (RayClass.adicAbv_isNontrivial v)]
  change _ ↔ σ • (finitePlaceExtensionCentre v w).asIdeal = _
  constructor
  · intro h
    have he := congrArg (fun w => (finitePlaceExtensionCentre v w).asIdeal) h
    rw [centre_conjugate_ideal M] at he
    exact ((inv_smul_eq_iff).mp he).symm
  · intro h
    apply finitePlaceExtensionCentre_injective v
    apply HeightOneSpectrum.ext
    rw [centre_conjugate_ideal M]
    exact inv_smul_eq_iff.mpr h.symm

variable (p : Nat.Primes) (j : M →ₐ[ℚ] AlgebraicClosure ℚ)

/-- Restrict the fixed absolute place along the actual embedding of M. -/
def restrictedAbsolutePlace : AbsoluteValueExtension (HeightOneSpectrum.adicAbv ℚ (place p)) M :=
  ⟨(finitePlaceAbsoluteValueExtension ℚ (place p)).1.comp j.injective,by
    intro x
    change (finitePlaceAbsoluteValueExtension ℚ (place p)).1 (j (algebraMap ℚ M x)) = _
    rw [j.commutes]
    exact (finitePlaceAbsoluteValueExtension ℚ (place p)).2 x⟩

def restrictedAbsolutePrime : HeightOneSpectrum (𝓞 M) :=
  finitePlaceExtensionCentre (place p) (restrictedAbsolutePlace M p j)

/-- The chosen rational prime contains its ordinary integer prime. -/
theorem prime_mem_place : (p.val : 𝓞 ℚ) ∈ (place p).asIdeal := by
  have hmem : (p.val : ℤ) ∈ (place p).asIdeal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) := by
    rw [← Rat.HeightOneSpectrum.span_natGenerator]
    have hp : Rat.HeightOneSpectrum.natGenerator (place p)=p.val := place_prime p
    rw [hp]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hh : (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) (p.val : 𝓞 ℚ) ∈
      (place p).asIdeal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) := by simpa using hmem
  exact Ideal.apply_mem_of_equiv_iff.mp hh

/-- The actual prime center lies over the ordinary rational ideal `(p)` in ℤ. -/
theorem restrictedAbsolutePrime_liesOver :
    (restrictedAbsolutePrime M p j).asIdeal.LiesOver
      (NumberFieldAnalysis.rationalPrimeIdeal p.val) := by
  let P := restrictedAbsolutePrime M p j
  letI := P.isPrime
  letI : P.asIdeal.LiesOver (place p).asIdeal :=
    finitePlaceExtensionCentre_liesOver (place p) (restrictedAbsolutePlace M p j)
  have hmem : (p.val : 𝓞 M) ∈ P.asIdeal := by
    have h : (p.val : 𝓞 ℚ) ∈ P.asIdeal.under (𝓞 ℚ) := by
      rw [←Ideal.over_def P.asIdeal (place p).asIdeal]
      exact prime_mem_place p
    change algebraMap (𝓞 ℚ) (𝓞 M) (p.val : 𝓞 ℚ) ∈ P.asIdeal at h
    simpa using h
  constructor
  apply Ideal.IsMaximal.eq_of_le (inferInstance :
    (NumberFieldAnalysis.rationalPrimeIdeal p.val).IsMaximal)
    (Ideal.IsPrime.ne_top (inferInstance : (P.asIdeal.under ℤ).IsPrime))
  rw [Ideal.span_singleton_le_iff_mem]
  change algebraMap ℤ (𝓞 M) (p.val : ℤ) ∈ P.asIdeal
  simpa using hmem

/-- Exact actual finite decomposition image, with no local surjectivity hypothesis. -/
theorem decompositionRestriction_range :
    (decompositionRestriction p M j).range =
      MulAction.stabilizer Gal(M/ℚ) (restrictedAbsolutePrime M p j).asIdeal := by
  letI : Algebra M (AlgebraicClosure ℚ) := j.toRingHom.toAlgebra
  letI : IsScalarTower ℚ M (AlgebraicClosure ℚ) :=
    IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  have he : (GaloisEmbedding.restriction j).toMonoidHom =
      AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) M := by
    ext σ x
    have hh := GaloisEmbedding.restriction_commutes j σ x
    have ht := AlgEquiv.restrictNormal_commutes σ M x
    exact j.injective (hh.trans ht.symm)
  have hr : (decompositionRestriction p M j).range =
      (AbsoluteDecomposition p).map
        (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) M) := by
    rw [←he]
    exact MonoidHom.range_comp _ _ |>.trans (by rw [Subgroup.range_subtype])
  rw [hr,absoluteValueDecompositionGroup_map_restrictNormalHom
    (HeightOneSpectrum.adicAbv ℚ (place p)) (RayClass.adicAbv_isNontrivial (place p))
    (finitePlaceAbsoluteValueExtension ℚ (place p))]
  exact absoluteValueDecompositionGroup_eq_prime_stabilizer M (place p)
    (restrictedAbsolutePlace M p j)

/-- Exclusion on the genuine absolute decomposition group proves that
conjugation moves every actual prime of norm `p^f`. -/
theorem prime_moved_of_absolute_genus_exclusion {A : Type*} [CommGroup A]
    (π : Gal(M/ℚ) →* A) (c : Gal(M/ℚ))
    (hex : ∀σ : AbsoluteDecomposition p, π (decompositionRestriction p M j σ) ≠ π c)
    (f : ℕ) (hf : 0 < f) (P : NumberFieldAnalysis.PrimeNormFiber M (p.val^f)) :
    Ideal.map (RingOfIntegers.mapRingHom c.toRingHom) P.1.asIdeal ≠ P.1.asIdeal := by
  let W := restrictedAbsolutePrime M p j
  letI : W.asIdeal.LiesOver (NumberFieldAnalysis.rationalPrimeIdeal p.val) :=
    restrictedAbsolutePrime_liesOver M p j
  apply GaloisPrimeConjugation.map_ideal_ne_of_genus_exclusion π c p.val p.property W _ f hf P
  rw [←decompositionRestriction_range M p j]
  rintro ⟨g,⟨σ,rfl⟩,he⟩
  exact hex σ he

end UnitDistance.PrimeCompletion
