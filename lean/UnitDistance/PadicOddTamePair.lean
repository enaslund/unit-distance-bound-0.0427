module

public import UnitDistance.PadicOddGenusAction

@[expose] public section
set_option backward.privateInPublic true


/-! Actual five odd tame pairs, with every genus coordinate determined arithmetically. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace UnitDistance.PadicOddGenus
open RamificationTheory.HilbertRamification.Higher
open ValuationTheory.DiscreteValuationField.ResidueField
open OddTame

attribute [local instance] oddPrime

variable (i : Fin 5) (L : Type u) [Field L] [Algebra ℚ_[PadicOdd.primes i] L]
  [FiniteDimensional ℚ_[PadicOdd.primes i] L] [IsGalois ℚ_[PadicOdd.primes i] L]
  (a : Fin 7 → L) (ha : ∀ j, (a j)^2=(PadicOdd.radicands j : L))
include ha

theorem inertia_generator_neg
    (τ : inertia i L)
    (hτ : Subgroup.zpowers (τ : Gal(L/ℚ_[PadicOdd.primes i]))=inertia i L)
    (φ : Gal(L/ℚ_[PadicOdd.primes i]))
    (hφ : ∀ b : (target i L).valuationSubringˣ,
      residueUnit (dvfValuationSubringUnitAut (unique i L) φ b)=
        (residueUnit b)^(PadicOdd.primes i))
    (hgen : ∀ σ, ∃ n : ℕ, completeResidueAction (base i) (target i L) σ=
      (completeResidueAction (base i) (target i L) φ)^n) :
    (τ : Gal(L/ℚ_[PadicOdd.primes i])) (a (PadicOdd.ramifiedIndex i))=
      -a (PadicOdd.ramifiedIndex i) := by
  letI : CharZero L := charZero_of_injective_algebraMap
    (algebraMap ℚ_[PadicOdd.primes i] L).injective
  have hs : ((τ : Gal(L/ℚ_[PadicOdd.primes i])) (a (PadicOdd.ramifiedIndex i)))^2=
      (a (PadicOdd.ramifiedIndex i))^2 := by rw [← map_pow,ha,map_intCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hfix | hneg
  · obtain ⟨σ,hσ⟩ := inertia_moves_ramified i L a ha φ hφ hgen
    have hstab : (τ : Gal(L/ℚ_[PadicOdd.primes i]))∈
        MulAction.stabilizer (Gal(L/ℚ_[PadicOdd.primes i])) (a (PadicOdd.ramifiedIndex i)) := hfix
    have hσmem : (σ : Gal(L/ℚ_[PadicOdd.primes i]))∈
        Subgroup.zpowers (τ : Gal(L/ℚ_[PadicOdd.primes i])) := by rw [hτ]; exact σ.property
    have hσfix := (Subgroup.zpowers_le.mpr hstab) hσmem
    change (σ : Gal(L/ℚ_[PadicOdd.primes i])) (a (PadicOdd.ramifiedIndex i))=
      a (PadicOdd.ramifiedIndex i) at hσfix
    have ha0 : a (PadicOdd.ramifiedIndex i)≠0 := by
      intro hz
      have hr : PadicOdd.radicands (PadicOdd.ramifiedIndex i)≠0 := by
        have h : ∀ k : Fin 5, PadicOdd.radicands (PadicOdd.ramifiedIndex k)≠0 := by decide +kernel
        exact h i
      have he := ha (PadicOdd.ramifiedIndex i)
      rw [hz,zero_pow (by decide : (2:ℕ)≠0)] at he
      exact hr (by exact_mod_cast he.symm)
    have htwo : (2 : L)*a (PadicOdd.ramifiedIndex i)=0 := by linear_combination hσ-hσfix
    exact False.elim ((mul_ne_zero two_ne_zero ha0) htwo)
  · exact hneg

theorem exists_normalized_frobenius
    (τ : inertia i L)
    (hτ : (τ : Gal(L/ℚ_[PadicOdd.primes i])) (a (PadicOdd.ramifiedIndex i))=
      -a (PadicOdd.ramifiedIndex i))
    (φ₀ : Gal(L/ℚ_[PadicOdd.primes i]))
    (hφ₀ : ∀ b : (target i L).valuationSubringˣ,
      residueUnit (dvfValuationSubringUnitAut (unique i L) φ₀ b)=
        (residueUnit b)^(PadicOdd.primes i)) :
    ∃ φ : Gal(L/ℚ_[PadicOdd.primes i]),
      (∀ b : (target i L).valuationSubringˣ,
        residueUnit (dvfValuationSubringUnitAut (unique i L) φ b)=
          (residueUnit b)^(PadicOdd.primes i)) ∧
      ∀ j, φ (a j)=(PadicOdd.residueSign i j : L)*a j := by
  have hs : (φ₀ (a (PadicOdd.ramifiedIndex i)))^2=(a (PadicOdd.ramifiedIndex i))^2 := by
    rw [← map_pow,ha,map_intCast]
  have hex : ∃ φ : Gal(L/ℚ_[PadicOdd.primes i]),
      (∀ b : (target i L).valuationSubringˣ,
        residueUnit (dvfValuationSubringUnitAut (unique i L) φ b)=
          (residueUnit b)^(PadicOdd.primes i)) ∧
      φ (a (PadicOdd.ramifiedIndex i))=a (PadicOdd.ramifiedIndex i) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hf | hf
    · exact ⟨φ₀,hφ₀,hf⟩
    · refine ⟨(τ : Gal(L/ℚ_[PadicOdd.primes i]))*φ₀,?_,?_⟩
      · intro b
        rw [valuationUnitAut_mul, residueUnit_aut_of_inertia (unique i L) τ, hφ₀]
      · rw [AlgEquiv.mul_apply,hf,map_neg,hτ,neg_neg]
  obtain ⟨φ,hφ,hfix⟩ := hex
  refine ⟨φ,hφ,fun j ↦ ?_⟩
  by_cases hj : j=PadicOdd.ramifiedIndex i
  · subst j
    rw [hfix,PadicOdd.ramified_sign,Int.cast_one,one_mul]
  · exact frobenius_other i L a ha φ hφ j hj

/-- Every actual finite Galois two-extension of Qp containing the seven
specified radicals has a cyclic inertia generator and Frobenius with all
seven prescribed signs and the literal tame relation. -/
theorem exists_labeled_tame_pair
    (hG : IsPGroup 2 Gal(L/ℚ_[PadicOdd.primes i])) :
    ∃ τ : inertia i L, ∃ φ : Gal(L/ℚ_[PadicOdd.primes i]),
      Subgroup.zpowers (τ : Gal(L/ℚ_[PadicOdd.primes i]))=inertia i L ∧
      φ*(τ : Gal(L/ℚ_[PadicOdd.primes i]))*φ⁻¹=
        (τ : Gal(L/ℚ_[PadicOdd.primes i]))^(PadicOdd.primes i) ∧
      (∀ j, (τ : Gal(L/ℚ_[PadicOdd.primes i])) (a j)=
        if j=PadicOdd.ramifiedIndex i then -a j else a j) ∧
      ∀ j, φ (a j)=(PadicOdd.residueSign i j : L)*a j := by
  have hpq : Nat.Coprime 2 (PadicOdd.primes i) := by
    have h : ∀ k : Fin 5, Nat.Coprime 2 (PadicOdd.primes k) := by decide +kernel
    exact h i
  have hq := PadicFiniteGalois.prime_mem_maximalIdeal (PadicOdd.primes i) L
  obtain ⟨pi,hpi⟩ := (target i L).exists_uniformizer
  letI := inertia_isCyclic (unique i L) 2 (PadicOdd.primes i) hG hpq hq pi hpi
  obtain ⟨τ,hτ⟩ := IsCyclic.exists_generator (α:=inertia i L)
  have hτgen : Subgroup.zpowers (τ : Gal(L/ℚ_[PadicOdd.primes i]))=inertia i L := by
    apply le_antisymm
    · exact Subgroup.zpowers_le.mpr τ.property
    · intro σ hσ
      obtain ⟨n,hn⟩ := hτ ⟨σ,hσ⟩
      exact ⟨n,congrArg Subtype.val hn⟩
  obtain ⟨φ₀,hφ₀,hgen⟩ := exists_generating_frobenius (base i) (target i L)
  rw [PadicFiniteGalois.residue_card] at hφ₀
  have hτneg := inertia_generator_neg i L a ha τ hτgen φ₀ hφ₀ hgen
  obtain ⟨φ,hφ,hsigns⟩ := exists_normalized_frobenius i L a ha τ hτneg φ₀ hφ₀
  refine ⟨τ,φ,hτgen,frobenius_conj_eq_pow (unique i L) 2 (PadicOdd.primes i)
    hG hpq hq pi hpi φ hφ τ,?_,hsigns⟩
  intro j
  by_cases hj : j=PadicOdd.ramifiedIndex i
  · subst j
    simpa using hτneg
  · simpa [hj] using inertia_fixes_other i L a ha τ j hj

end UnitDistance.PadicOddGenus
