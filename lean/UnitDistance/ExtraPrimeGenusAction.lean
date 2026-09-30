module

public import UnitDistance.ExtraPrimeRadicals
public import UnitDistance.PadicFiniteGaloisValuation

@[expose] public section
set_option backward.privateInPublic true


/-! Actual finite local Frobenius actions at the five additional primes. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace UnitDistance.ExtraPrime
open RamificationTheory.HilbertRamification.Higher
open ValuationTheory.DiscreteValuationField.ResidueField
open OddTame
local instance primeFact (i : Fin 5) : Fact (primes i).Prime := ⟨primes_prime i⟩

variable (i : Fin 5) (L : Type u) [Field L] [Algebra ℚ_[primes i] L]
  [FiniteDimensional ℚ_[primes i] L] [IsGalois ℚ_[primes i] L]
  (a : Fin 7 → L) (ha : ∀j,(a j)^2=(radicands j : L))
include ha

abbrev base := PadicFiniteGalois.base (primes i)
abbrev target := PadicFiniteGalois.target (primes i) L
abbrev unique : RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{0,0,u,0,0}
    (base i).toDVF (target i L).toDVF := completeUnique (base i) (target i L)

def integralRoot (j : Fin 7) : (target i L).valuationSubring :=
  ⟨a j,PadicFiniteGalois.radical_integral (primes i) L _ _ (ha j)⟩

theorem integralRoot_sq (j : Fin 7) : (integralRoot i L a ha j)^2=radicands j := by
  apply Subtype.ext
  exact ha j

theorem integralRoot_isUnit (j : Fin 7) : IsUnit (integralRoot i L a ha j) :=
  PadicFiniteGalois.radical_isUnit (primes i) L _ _
    (integralRoot_sq i L a ha j) (radicands_unit i j)

theorem frobenius_action (φ : Gal(L/ℚ_[primes i]))
    (hφ : ∀b : (target i L).valuationSubringˣ,
      residueUnit (dvfValuationSubringUnitAut (unique i L) φ b)=(residueUnit b)^(primes i))
    (j : Fin 7) : φ (a j)=(residueSign i j : L)*a j := by
  let h := integralRoot_isUnit i L a ha j
  have hs : (h.unit : (target i L).valuationSubring)^2=radicands j := by
    rw [h.unit_spec,integralRoot_sq]
  have hd : (radicands j : (target i L).residueField)^((primes i-1)/2)=residueSign i j := by
    have he := congrArg (PadicFiniteGalois.residueEmbedding (primes i) L) (euler_residue_sign i j)
    simpa only [map_pow,map_intCast] using he
  have he : residueSign i j=1 ∨ residueSign i j= -1 := by
    simp only [residueSign]
    split_ifs <;> simp
  have hv := congrArg Subtype.val (frobenius_unit_radical (unique i L)
    (PadicFiniteGalois.two_residue_ne_zero (primes i) L (primes_ne_two i))
    _ _ (primes_odd i) φ hφ h.unit _ _ hs he hd)
  change φ ((h.unit : (target i L).valuationSubring) : L)=
    (residueSign i j : L)*((h.unit : (target i L).valuationSubring) : L) at hv
  rw [h.unit_spec] at hv
  exact hv

/-- A genuine Frobenius of a finite p-adic Galois field acts by the kernel-checked
Euler sign table on every one of the seven actual radicals. -/
theorem exists_frobenius_signs : ∃φ : Gal(L/ℚ_[primes i]),
    ∀j,φ (a j)=(residueSign i j : L)*a j := by
  obtain ⟨φ,hφ,_⟩ := exists_generating_frobenius (base i) (target i L)
  rw [PadicFiniteGalois.residue_card] at hφ
  exact ⟨φ,frobenius_action i L a ha φ hφ⟩

end UnitDistance.ExtraPrime
