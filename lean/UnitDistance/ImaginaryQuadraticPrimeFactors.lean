module

public import UnitDistance.GaussianPrimeFactors
public import UnitDistance.ConjugationQuadraticPresentation
public import UnitDistance.IdealResidueProduct

@[expose] public section
set_option backward.privateInPublic true


/-! The odd-prime Euler identity for an actual displayed imaginary quadratic extension. -/
noncomputable section
namespace UnitDistance.ImaginaryQuadraticEuler
open NumberField UniqueFactorizationMonoid GaussianQuadraticOrder
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable (F K : Type*) [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  [Fact (KummerInvariant.Nonsquare (-1:F))]

def quotientEquiv (e : GaussianField F ≃ₐ[F] K) (P : Ideal (𝓞 F)) :
    𝓞 (GaussianField F) ⧸ primeMap F P ≃+*
      𝓞 K ⧸ P.map (algebraMap (𝓞 F) (𝓞 K)) := by
  let eO : 𝓞 (GaussianField F) ≃ₐ[𝓞 F] 𝓞 K := RingOfIntegers.mapAlgEquiv e
  apply Ideal.quotientEquiv _ _ eO.toRingEquiv
  rw [primeMap, Ideal.map_map]
  congr 1
  exact RingHom.ext (fun a => (eO.commutes a).symm)

/-- Exact odd-prime Euler denominator identity; prime factors and norms are actual. -/
theorem oddPrime_factor_product (i : K) (hi : i^2=(-1:K))
    (hdegree : Module.finrank F K=2) (P : Ideal (𝓞 F)) [P.IsMaximal]
    (hP : P ≠ ⊥) (h2 : (2:𝓞 F) ∉ P) (s : ℂ) :
    (∏ Q ∈ (normalizedFactors (P.map (algebraMap (𝓞 F) (𝓞 K)))).toFinset,
      (1-(Ideal.absNorm Q:ℂ)^(-s))) =
      (1-(Ideal.absNorm P:ℂ)^(-s)) *
        (1-NumberFieldAnalysis.chiFourComplex (Ideal.absNorm P)*(Ideal.absNorm P:ℂ)^(-s)) := by
  have hmap : P.map (algebraMap (𝓞 F) (𝓞 K)) ≠ ⊥ := by
    rwa [ne_eq, Ideal.map_eq_bot_iff_of_injective
      (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K))]
  let e := ConjugationQuadratic.imaginaryEquiv (F := F) i hi hdegree
  have h := QuotientPrimeCorrespondence.prod_residue_natCard
    (quotientEquiv F K e P).symm hmap (primeMap_ne_bot F P hP)
    (fun n => 1-(n:ℂ)^(-s))
  exact h.trans (GaussianQuadraticOrder.oddPrime_factor_product F P hP h2 s)

end UnitDistance.ImaginaryQuadraticEuler
