module

public import UnitDistance.PadicFiniteGaloisValuation
public import UnitDistance.PadicOddRadicals

@[expose] public section
set_option backward.privateInPublic true


/-! Actual inertia and Frobenius signs on the seven genus radicals in finite Qp extensions. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace UnitDistance.PadicOddGenus
open RamificationTheory.HilbertRamification.Higher
open ValuationTheory.DiscreteValuationField.ResidueField
open OddTame

local instance oddPrime (i : Fin 5) : Fact (PadicOdd.primes i).Prime := ⟨PadicOdd.primes_prime i⟩

variable (i : Fin 5) (L : Type u) [Field L] [Algebra ℚ_[PadicOdd.primes i] L]
  [FiniteDimensional ℚ_[PadicOdd.primes i] L] [IsGalois ℚ_[PadicOdd.primes i] L]

abbrev base := PadicFiniteGalois.base (PadicOdd.primes i)
abbrev target := PadicFiniteGalois.target (PadicOdd.primes i) L
abbrev unique : RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{0,0,u,0,0}
    (base i).toDVF (target i L).toDVF := completeUnique (base i) (target i L)
abbrev inertia := lowerRamificationGroup (base:=(base i).toDVF) (target:=(target i L).toDVF)
  (unique i L) ((0 : ℕ) : ℝ)

theorem residue_two_ne_zero : (2 : (target i L).residueField)≠0 := by
  apply PadicFiniteGalois.two_residue_ne_zero
  have h : ∀ j : Fin 5,PadicOdd.primes j≠2 := by decide +kernel
  exact h i

variable (a : Fin 7 → L) (ha : ∀ j, (a j)^2=(PadicOdd.radicands j : L))
include ha

def integralRoot (j : Fin 7) : (target i L).valuationSubring :=
  ⟨a j, PadicFiniteGalois.radical_integral (PadicOdd.primes i) L _ _ (ha j)⟩

theorem integralRoot_sq (j : Fin 7) : (integralRoot i L a ha j)^2=PadicOdd.radicands j := by
  apply Subtype.ext
  exact ha j

theorem integralRoot_isUnit (j : Fin 7) (hj : j≠PadicOdd.ramifiedIndex i) :
    IsUnit (integralRoot i L a ha j) :=
  PadicFiniteGalois.radical_isUnit (PadicOdd.primes i) L _ _
    (integralRoot_sq i L a ha j) (PadicOdd.radicands_unit i j hj)

theorem inertia_fixes_other (σ : inertia i L) (j : Fin 7)
    (hj : j≠PadicOdd.ramifiedIndex i) : (σ : Gal(L/ℚ_[PadicOdd.primes i])) (a j)=a j := by
  let h := integralRoot_isUnit i L a ha j hj
  have hs : ((h.unit : (target i L).valuationSubring))^2=PadicOdd.radicands j := by
    rw [h.unit_spec,integralRoot_sq]
  have hv := congrArg Subtype.val
    (inertia_fixes_unit_radical (unique i L) (residue_two_ne_zero i L) σ h.unit _ hs)
  change (σ : Gal(L/ℚ_[PadicOdd.primes i])) ((h.unit : (target i L).valuationSubring) : L)=
    ((h.unit : (target i L).valuationSubring) : L) at hv
  rw [h.unit_spec] at hv
  exact hv

theorem frobenius_other (φ : Gal(L/ℚ_[PadicOdd.primes i]))
    (hφ : ∀ b : (target i L).valuationSubringˣ,
      residueUnit (dvfValuationSubringUnitAut (unique i L) φ b)=
        (residueUnit b)^(PadicOdd.primes i))
    (j : Fin 7) (hj : j≠PadicOdd.ramifiedIndex i) :
    φ (a j)=(PadicOdd.residueSign i j : L)*a j := by
  let h := integralRoot_isUnit i L a ha j hj
  have hs : ((h.unit : (target i L).valuationSubring))^2=PadicOdd.radicands j := by
    rw [h.unit_spec,integralRoot_sq]
  have hd : (PadicOdd.radicands j : (target i L).residueField)^((PadicOdd.primes i-1)/2)=
      PadicOdd.residueSign i j := by
    have he := congrArg (PadicFiniteGalois.residueEmbedding (PadicOdd.primes i) L)
      (PadicOdd.euler_residue_sign i j hj)
    simpa only [map_pow,map_intCast] using he
  have he : PadicOdd.residueSign i j=1 ∨ PadicOdd.residueSign i j= -1 := by
    simp only [PadicOdd.residueSign]
    split_ifs <;> simp
  have hv := congrArg Subtype.val (frobenius_unit_radical (unique i L)
    (residue_two_ne_zero i L) _ _ (PadicOdd.primes_odd i) φ hφ h.unit _ _ hs he hd)
  change φ ((h.unit : (target i L).valuationSubring) : L)=
    (PadicOdd.residueSign i j : L)*((h.unit : (target i L).valuationSubring) : L) at hv
  rw [h.unit_spec] at hv
  exact hv

theorem inertia_moves_ramified
    (φ : Gal(L/ℚ_[PadicOdd.primes i]))
    (hφ : ∀ b : (target i L).valuationSubringˣ,
      residueUnit (dvfValuationSubringUnitAut (unique i L) φ b)=
        (residueUnit b)^(PadicOdd.primes i))
    (hgen : ∀ σ, ∃ n : ℕ, completeResidueAction (base i) (target i L) σ=
      (completeResidueAction (base i) (target i L) φ)^n) :
    ∃ σ : inertia i L, (σ : Gal(L/ℚ_[PadicOdd.primes i]))
      (a (PadicOdd.ramifiedIndex i))= -a (PadicOdd.ramifiedIndex i) := by
  letI : CharZero L := charZero_of_injective_algebraMap
    (algebraMap ℚ_[PadicOdd.primes i] L).injective
  have hr : PadicOdd.radicands (PadicOdd.ramifiedIndex i)=(PadicOdd.primes i : ℤ) := by
    have h : ∀ k : Fin 5, PadicOdd.radicands (PadicOdd.ramifiedIndex k)=
        (PadicOdd.primes k : ℤ) := by decide +kernel
    exact h i
  have hram : (a (PadicOdd.ramifiedIndex i))^2=
      algebraMap ℚ_[PadicOdd.primes i] L (PadicOdd.primes i : ℚ_[PadicOdd.primes i]) := by
    rw [ha,hr,map_natCast,Int.cast_natCast]
  have hunram : (a (PadicOdd.nonresidueIndex i))^2=
      algebraMap ℚ_[PadicOdd.primes i] L
        (PadicOdd.radicands (PadicOdd.nonresidueIndex i) : ℚ_[PadicOdd.primes i]) := by
    rw [ha,map_intCast]
  have hbi : ∀ σ∈(completeResidueAction (base i) (target i L)).ker,
      σ (a (PadicOdd.nonresidueIndex i))=a (PadicOdd.nonresidueIndex i) := by
    intro σ hσ
    rw [← inertia_eq_ker_completeResidueAction] at hσ
    exact inertia_fixes_other i L a ha ⟨σ,hσ⟩ _ (PadicOdd.nonresidue_index_ne i)
  have hbf : φ (a (PadicOdd.nonresidueIndex i))= -a (PadicOdd.nonresidueIndex i) := by
    rw [frobenius_other i L a ha φ hφ _ (PadicOdd.nonresidue_index_ne i),PadicOdd.nonresidue_sign]
    simp
  obtain ⟨σ,hσ,hs⟩ := exists_inertia_neg_radical
    (completeResidueAction (base i) (target i L)) φ hgen
    (a (PadicOdd.ramifiedIndex i)) (a (PadicOdd.nonresidueIndex i))
    (PadicOdd.primes i : ℚ_[PadicOdd.primes i])
    (PadicOdd.radicands (PadicOdd.nonresidueIndex i) : ℚ_[PadicOdd.primes i])
    hram hunram (PadicOdd.prime_not_isSquare _)
    (PadicOdd.prime_mul_unit_not_isSquare _ _
      (PadicOdd.radicands_unit i _ (PadicOdd.nonresidue_index_ne i))) hbi hbf
  rw [← inertia_eq_ker_completeResidueAction] at hσ
  exact ⟨⟨σ,hσ⟩,hs⟩

end UnitDistance.PadicOddGenus
