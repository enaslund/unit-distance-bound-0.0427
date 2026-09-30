module

public import UnitDistance.PadicOddTamePair

@[expose] public section
set_option backward.privateInPublic true


/-! The arithmetically labelled tame pair generates the full finite local
Galois group, and its inertia component generates actual inertia. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.OddTame

variable {G H : Type*} [Group G] [Group H]

theorem closure_pair_eq_top (r : G →* H) (τ φ : G)
    (hτ : Subgroup.zpowers τ=r.ker)
    (hφ : ∀σ, ∃n : ℕ, r σ=(r φ)^n) :
    Subgroup.closure ({τ,φ} : Set G)=⊤ := by
  apply top_unique
  intro σ _
  let S := Subgroup.closure ({τ,φ} : Set G)
  have ht : τ∈S := Subgroup.subset_closure (by simp)
  have hp : φ∈S := Subgroup.subset_closure (by simp)
  have hker : r.ker≤S := by rw [←hτ]; exact Subgroup.zpowers_le.mpr ht
  obtain ⟨n,hn⟩ := hφ σ
  have hdiff : σ*(φ^n)⁻¹∈r.ker := by
    simp only [MonoidHom.mem_ker,map_mul,map_inv,map_pow,hn,mul_inv_cancel]
  have h := S.mul_mem (hker hdiff) (S.pow_mem hp n)
  simpa only [inv_mul_cancel_right] using h

end UnitDistance.OddTame
namespace UnitDistance.PadicOddGenus
open RamificationTheory.HilbertRamification.Higher
open ValuationTheory.DiscreteValuationField.ResidueField
open OddTame
attribute [local instance] oddPrime

variable (i : Fin 5) (L : Type*) [Field L] [Algebra ℚ_[PadicOdd.primes i] L]
  [FiniteDimensional ℚ_[PadicOdd.primes i] L] [IsGalois ℚ_[PadicOdd.primes i] L]
  (a : Fin 7 → L) (ha : ∀j,(a j)^2=(PadicOdd.radicands j : L))
include ha

theorem exists_normalized_generating_frobenius
    (τ : inertia i L)
    (hτ : (τ : Gal(L/ℚ_[PadicOdd.primes i])) (a (PadicOdd.ramifiedIndex i))=
      -a (PadicOdd.ramifiedIndex i))
    (φ₀ : Gal(L/ℚ_[PadicOdd.primes i]))
    (hφ₀ : ∀ b : (target i L).valuationSubringˣ,
      residueUnit (dvfValuationSubringUnitAut (unique i L) φ₀ b)=
        (residueUnit b)^(PadicOdd.primes i))
    (hgen : ∀σ, ∃n : ℕ, completeResidueAction (base i) (target i L) σ=
      (completeResidueAction (base i) (target i L) φ₀)^n) :
    ∃φ : Gal(L/ℚ_[PadicOdd.primes i]),
      (∀ b : (target i L).valuationSubringˣ,
        residueUnit (dvfValuationSubringUnitAut (unique i L) φ b)=
          (residueUnit b)^(PadicOdd.primes i)) ∧
      (∀σ, ∃n : ℕ, completeResidueAction (base i) (target i L) σ=
        (completeResidueAction (base i) (target i L) φ)^n) ∧
      ∀j,φ (a j)=(PadicOdd.residueSign i j : L)*a j := by
  have hs : (φ₀ (a (PadicOdd.ramifiedIndex i)))^2=(a (PadicOdd.ramifiedIndex i))^2 := by
    rw [←map_pow,ha,map_intCast]
  have hτr : completeResidueAction (base i) (target i L) τ=1 := by
    have he := inertia_eq_ker_completeResidueAction (base i) (target i L)
    exact (show (τ : Gal(L/ℚ_[PadicOdd.primes i]))∈
      (completeResidueAction (base i) (target i L)).ker from he ▸ τ.property)
  have hex : ∃φ : Gal(L/ℚ_[PadicOdd.primes i]),
      (∀ b : (target i L).valuationSubringˣ,
        residueUnit (dvfValuationSubringUnitAut (unique i L) φ b)=
          (residueUnit b)^(PadicOdd.primes i)) ∧
      (∀σ, ∃n : ℕ, completeResidueAction (base i) (target i L) σ=
        (completeResidueAction (base i) (target i L) φ)^n) ∧
      φ (a (PadicOdd.ramifiedIndex i))=a (PadicOdd.ramifiedIndex i) := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hf | hf
    · exact ⟨φ₀,hφ₀,hgen,hf⟩
    · refine ⟨(τ : Gal(L/ℚ_[PadicOdd.primes i]))*φ₀,?_,?_,?_⟩
      · intro b
        rw [valuationUnitAut_mul,residueUnit_aut_of_inertia (unique i L) τ,hφ₀]
      · simpa only [map_mul,hτr,one_mul] using hgen
      · rw [AlgEquiv.mul_apply,hf,map_neg,hτ,neg_neg]
  obtain ⟨φ,hφ,hφgen,hfix⟩ := hex
  refine ⟨φ,hφ,hφgen,fun j ↦ ?_⟩
  by_cases hj : j=PadicOdd.ramifiedIndex i
  · subst j
    rw [hfix,PadicOdd.ramified_sign,Int.cast_one,one_mul]
  · exact frobenius_other i L a ha φ hφ j hj

/-- Every finite Galois two-field containing the seven radicals has a
labelled tame pair generating its actual local Galois group. -/
theorem exists_labeled_generating_tame_pair
    (hG : IsPGroup 2 Gal(L/ℚ_[PadicOdd.primes i])) :
    ∃τ : inertia i L, ∃φ : Gal(L/ℚ_[PadicOdd.primes i]),
      Subgroup.zpowers (τ : Gal(L/ℚ_[PadicOdd.primes i]))=inertia i L ∧
      Subgroup.closure ({(τ : Gal(L/ℚ_[PadicOdd.primes i])),φ} : Set _)=⊤ ∧
      φ*(τ : Gal(L/ℚ_[PadicOdd.primes i]))*φ⁻¹=
        (τ : Gal(L/ℚ_[PadicOdd.primes i]))^(PadicOdd.primes i) ∧
      (∀j,(τ : Gal(L/ℚ_[PadicOdd.primes i])) (a j)=
        if j=PadicOdd.ramifiedIndex i then -a j else a j) ∧
      ∀j,φ (a j)=(PadicOdd.residueSign i j : L)*a j := by
  have hpq : Nat.Coprime 2 (PadicOdd.primes i) := by
    have h : ∀k : Fin 5,Nat.Coprime 2 (PadicOdd.primes k) := by decide +kernel
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
  obtain ⟨φ,hφ,hφgen,hsigns⟩ := exists_normalized_generating_frobenius
    i L a ha τ hτneg φ₀ hφ₀ hgen
  refine ⟨τ,φ,hτgen,?_,frobenius_conj_eq_pow (unique i L) 2 (PadicOdd.primes i)
    hG hpq hq pi hpi φ hφ τ,?_,hsigns⟩
  · exact closure_pair_eq_top (completeResidueAction (base i) (target i L)) τ φ
      (hτgen.trans (inertia_eq_ker_completeResidueAction (base i) (target i L))) hφgen
  · intro j
    by_cases hj : j=PadicOdd.ramifiedIndex i
    · subst j
      simpa using hτneg
    · simpa [hj] using inertia_fixes_other i L a ha τ j hj

end UnitDistance.PadicOddGenus
