module

public import UnitDistance.RationalCompletionPadic
public import UnitDistance.PadicFiniteGaloisValuation
public import UnitDistance.GaloisBaseEquiv

import all UnitDistance.RationalCompletionPadic
@[expose] public section
set_option backward.privateInPublic true


/-! Finite p-adic fields regarded over the actual rational norm
completion used by the absolute decomposition comparison. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
open scoped NumberField ValuativeRel
namespace UnitDistance.PrimeCompletion
open NumberField IsDedekindDomain ArithmeticProP
open ValuationTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
local instance primeFact (p : Nat.Primes) : Fact p.val.Prime := ⟨p.property⟩

def place (p : Nat.Primes) : HeightOneSpectrum (𝓞 ℚ) :=
  Rat.HeightOneSpectrum.primesEquiv.symm p

theorem place_prime (p : Nat.Primes) :
    (Rat.HeightOneSpectrum.primesEquiv (place p)).val=p.val :=
  congrArg Subtype.val (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply _)

abbrev Base (p : Nat.Primes) := (HeightOneSpectrum.adicAbv ℚ (place p)).Completion

local instance baseRationalAlgebra (p : Nat.Primes) : Algebra ℚ (Base p) :=
  inferInstanceAs (Algebra ℚ ((HeightOneSpectrum.adicAbv ℚ (place p)).Completion))

instance baseCharZero (p : Nat.Primes) : CharZero (Base p) :=
  charZero_of_injective_algebraMap (algebraMap ℚ (Base p)).injective

def padicCast (p q : Nat.Primes) (h : p=q) : ℚ_[p] ≃A[ℚ] ℚ_[q] := by
  subst q
  exact ContinuousAlgEquiv.refl ℚ ℚ_[p]

def equiv (p : Nat.Primes) : Base p ≃A[ℚ] ℚ_[p.val] :=
  (rationalCompletionPadic (place p)).trans
    (padicCast _ p
      (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply _))

instance baseValuativeRel (p : Nat.Primes) : ValuativeRel (Base p) :=
  finitePlaceCompletionValuativeRel (HeightOneSpectrum.adicAbv ℚ (place p))
    (HeightOneSpectrum.isNonarchimedean_adicAbv ℚ (place p))

theorem padicCast_integers (p q : Nat.Primes) (h : p=q) (y : ℚ_[p]) :
    padicCast p q h y ∈ (padicCompleteDVF q).valuation.valuationSubring ↔
      y∈(padicCompleteDVF p).valuation.valuationSubring := by
  subst q
  rfl

theorem equiv_integers (p : Nat.Primes) (x : Base p) :
    x∈𝒪[Base p] ↔ equiv p x∈(PadicFiniteGalois.base (p.val)).valuation.valuationSubring := by
  exact (rationalCompletionPadic_valuationSubring (place p) x).trans
    (padicCast_integers (Rat.HeightOneSpectrum.primesEquiv (place p))
      p
      (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply _)
      (rationalCompletionPadic (place p) x)).symm

instance baseAlgebra (p : Nat.Primes) : Algebra (Base p) ℚ_[p.val] :=
  (equiv p).toRingHom.toAlgebra

variable (p : Nat.Primes) (L : Type) [Field L] [Algebra ℚ_[p.val] L]
  [FiniteDimensional ℚ_[p.val] L] [IsGalois ℚ_[p.val] L]

instance (priority := 100) targetAlgebra : Algebra (Base p) L :=
  ((algebraMap ℚ_[p.val] L).comp (equiv p).toRingHom).toAlgebra
instance targetTower : IsScalarTower (Base p) ℚ_[p.val] L :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

instance targetFinite : Module.Finite (Base p) L :=
  GaloisBaseEquiv.finite (Base p) ℚ_[p.val] L (equiv p).surjective

instance targetGalois : IsGalois (Base p) L :=
  GaloisBaseEquiv.galois (Base p) ℚ_[p.val] L (equiv p).surjective

def galoisEquiv : Gal(L/Base p) ≃* Gal(L/ℚ_[p.val]) :=
  GaloisBaseEquiv.autEquiv (Base p) ℚ_[p.val] L (equiv p).surjective

@[reducible] def targetValuativeRel : ValuativeRel L :=
  ValuativeRel.ofValuation (PadicFiniteGalois.target (p.val) L).valuation

theorem targetCompatible :
    letI := targetValuativeRel p L
    (PadicFiniteGalois.target (p.val) L).valuation.Compatible :=
  Valuation.Compatible.ofValuation _

variable [ValuativeRel L] [(PadicFiniteGalois.target (p.val) L).valuation.Compatible]

instance targetHasExtension :
    (ValuativeRel.valuation (Base p)).HasExtension (ValuativeRel.valuation L) := by
  apply Valuation.HasExtension.ofComapInteger
  ext x
  change (ValuativeRel.valuation L) (algebraMap (Base p) L x)≤1 ↔
    (ValuativeRel.valuation (Base p)) x≤1
  have h := ValuativeRel.isEquiv (ValuativeRel.valuation L)
    (PadicFiniteGalois.target (p.val) L).valuation
  have hmap : algebraMap (Base p) L x=algebraMap ℚ_[p.val] L (equiv p x) := rfl
  have he : (ValuativeRel.valuation L) (algebraMap (Base p) L x)≤1 ↔
      (PadicFiniteGalois.target (p.val) L).valuation
        (algebraMap ℚ_[p.val] L (equiv p x))≤1 := by
    simpa only [map_one,hmap] using h (algebraMap (Base p) L x) 1
  rw [he,Valuation.HasExtension.val_map_le_one_iff
    (PadicFiniteGalois.base (p.val)).valuation
    (PadicFiniteGalois.target (p.val) L).valuation]
  exact (equiv_integers p x).symm

end UnitDistance.PrimeCompletion
