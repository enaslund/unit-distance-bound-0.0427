module

public import UnitDistance.PadicOddGeneratingPair
public import UnitDistance.PadicOddRadicals

@[expose] public section
set_option backward.privateInPublic true

/-!
# Labelled generating tame pairs over `ℚ_p`, for an arbitrary radicand table

The ℚ package proves the tame-pair theorem for the fixed seven rational radicands
(`PadicOddGenus.exists_labeled_generating_tame_pair`). Here the same argument is
stated for an odd prime `p`, a finite Galois `2`-extension `L/ℚ_p`, one
nonresidue unit radical `u` (`u² = d_u`, `(d_u/p) = -1`) and one ramified radical
`w` (`w² = p·d_w`, `p ∤ d_w`): there are an inertia generator `τ` and a Frobenius
lift `φ`, generating `Gal(L/ℚ_p)`, with `φ τ φ⁻¹ = τ^p`, `τ w = -w`, `φ w = w`.
Every unit radical (`x² = d`, `p ∤ d`) is fixed by inertia and multiplied by the
Euler sign `d^((p-1)/2) mod p` under `φ` (`inertia_fixes_unit`, `frobenius_unit`).

This is the generalization "radicand table as a parameter, ramified class `p·c`"
of the ℚ files `PadicOddGenusAction`, `PadicOddTamePair`, `PadicOddGeneratingPair`;
the proofs are those of the ℚ files.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace UnitDistance.Sqrt241.Local.Tame

open RamificationTheory.HilbertRamification.Higher
open ValuationTheory.DiscreteValuationField.ResidueField
open UnitDistance.OddTame

variable (p : ℕ) [Fact p.Prime] (L : Type u) [Field L] [Algebra ℚ_[p] L]
  [FiniteDimensional ℚ_[p] L] [IsGalois ℚ_[p] L]

abbrev base := PadicFiniteGalois.base p
abbrev target := PadicFiniteGalois.target p L
abbrev unique : RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{0,0,u,0,0}
    (base p).toDVF (target p L).toDVF := completeUnique (base p) (target p L)
abbrev inertia := lowerRamificationGroup (base:=(base p).toDVF) (target:=(target p L).toDVF)
  (unique p L) ((0 : ℕ) : ℝ)

/-- The Frobenius property of an automorphism: residue action `x ↦ x^p` on units. -/
def IsFrobenius (φ : Gal(L/ℚ_[p])) : Prop :=
  ∀ b : (target p L).valuationSubringˣ,
    residueUnit (dvfValuationSubringUnitAut (unique p L) φ b) = (residueUnit b) ^ p

section Radicals

variable {p L}

theorem integral_of_sq_int (x : L) (d : ℤ) (hx : x ^ 2 = d) :
    x ∈ (target p L).valuation.valuationSubring :=
  PadicFiniteGalois.radical_integral p L x d hx

theorem unit_of_sq_int (x : L) (d : ℤ) (hx : x ^ 2 = d) (hd : ¬(p : ℤ) ∣ d) :
    IsUnit (⟨x, integral_of_sq_int x d hx⟩ : (target p L).valuationSubring) :=
  PadicFiniteGalois.radical_isUnit p L _ d (Subtype.ext hx) hd

/-- Inertia fixes every unit square root of an integer. -/
theorem inertia_fixes_unit (hp : p ≠ 2) (σ : inertia p L) (x : L) (d : ℤ) (hx : x ^ 2 = d)
    (hd : ¬(p : ℤ) ∣ d) : (σ : Gal(L/ℚ_[p])) x = x := by
  let h := unit_of_sq_int x d hx hd
  have hs : ((h.unit : (target p L).valuationSubring)) ^ 2 = d := by
    rw [h.unit_spec]
    exact Subtype.ext hx
  have hv := congrArg Subtype.val
    (inertia_fixes_unit_radical (unique p L) (PadicFiniteGalois.two_residue_ne_zero p L hp)
      σ h.unit _ hs)
  change (σ : Gal(L/ℚ_[p])) ((h.unit : (target p L).valuationSubring) : L) =
    ((h.unit : (target p L).valuationSubring) : L) at hv
  rw [h.unit_spec] at hv
  exact hv

/-- A Frobenius lift multiplies a unit square root of `d` by the Euler sign of `d`. -/
theorem frobenius_unit (hp : p ≠ 2) (φ : Gal(L/ℚ_[p])) (hφ : IsFrobenius p L φ)
    (x : L) (d : ℤ) (hx : x ^ 2 = d) (hd : ¬(p : ℤ) ∣ d) (ε : ℤ) (he : ε = 1 ∨ ε = -1)
    (hε : (d : ZMod p) ^ ((p - 1) / 2) = ε) : φ x = ε * x := by
  let h := unit_of_sq_int x d hx hd
  have hs : ((h.unit : (target p L).valuationSubring)) ^ 2 = d := by
    rw [h.unit_spec]
    exact Subtype.ext hx
  have hodd : p = 2 * ((p - 1) / 2) + 1 := by
    have h2 := (Fact.out : p.Prime).eq_one_or_self_of_dvd 2
    have hp1 := (Fact.out : p.Prime).two_le
    rcases Nat.even_or_odd p with ⟨k, hk⟩ | ⟨k, hk⟩
    · exfalso
      have hdv : 2 ∣ p := ⟨k, by omega⟩
      rcases h2 hdv with h | h <;> omega
    · omega
  have hdres : (d : (target p L).residueField) ^ ((p - 1) / 2) = ε := by
    have he := congrArg (PadicFiniteGalois.residueEmbedding p L) hε
    simpa only [map_pow, map_intCast] using he
  have hv := congrArg Subtype.val (frobenius_unit_radical (unique p L)
    (PadicFiniteGalois.two_residue_ne_zero p L hp) _ _ hodd φ hφ h.unit _ _ hs he hdres)
  change φ ((h.unit : (target p L).valuationSubring) : L) =
    (ε : L) * ((h.unit : (target p L).valuationSubring) : L) at hv
  rw [h.unit_spec] at hv
  exact hv

end Radicals

variable {p L}

theorem prime_mul_not_isSquare (d : ℤ) (hd : ¬(p : ℤ) ∣ d) :
    ¬IsSquare ((p : ℚ_[p]) * (d : ℚ_[p])) :=
  PadicOdd.prime_mul_unit_not_isSquare p d hd

/-- Inertia moves the ramified radical. -/
theorem inertia_moves_ramified (hp : p ≠ 2)
    (u : L) (du : ℤ) (hu : u ^ 2 = du) (hdu : ¬(p : ℤ) ∣ du)
    (hnr : (du : ZMod p) ^ ((p - 1) / 2) = -1)
    (w : L) (dw : ℤ) (hw : w ^ 2 = p * dw) (hdw : ¬(p : ℤ) ∣ dw)
    (φ : Gal(L/ℚ_[p])) (hφ : IsFrobenius p L φ)
    (hgen : ∀ σ, ∃ n : ℕ, completeResidueAction (base p) (target p L) σ =
      (completeResidueAction (base p) (target p L) φ) ^ n) :
    ∃ σ : inertia p L, (σ : Gal(L/ℚ_[p])) w = -w := by
  have hw' : w ^ 2 = algebraMap ℚ_[p] L ((p : ℚ_[p]) * (dw : ℚ_[p])) := by
    rw [hw, map_mul, map_natCast, map_intCast]
  have hu' : u ^ 2 = algebraMap ℚ_[p] L (du : ℚ_[p]) := by rw [hu, map_intCast]
  have hbi : ∀ σ ∈ (completeResidueAction (base p) (target p L)).ker, σ u = u := by
    intro σ hσ
    rw [← inertia_eq_ker_completeResidueAction] at hσ
    exact inertia_fixes_unit hp ⟨σ, hσ⟩ u du hu hdu
  have hbf : φ u = -u := by
    rw [frobenius_unit hp φ hφ u du hu hdu (-1) (Or.inr rfl) (by rw [hnr]; simp)]
    simp
  have hcd : ¬IsSquare ((p : ℚ_[p]) * (dw : ℚ_[p]) * (du : ℚ_[p])) := by
    have hprod : ¬(p : ℤ) ∣ dw * du := by
      intro h
      rcases (Int.Prime.dvd_mul' (Fact.out : p.Prime) h) with h | h
      · exact hdw h
      · exact hdu h
    have := prime_mul_not_isSquare (p := p) (dw * du) hprod
    simpa [mul_assoc] using this
  obtain ⟨σ, hσ, hs⟩ := exists_inertia_neg_radical
    (completeResidueAction (base p) (target p L)) φ hgen w u _ _ hw' hu'
    (prime_mul_not_isSquare dw hdw) hcd hbi hbf
  rw [← inertia_eq_ker_completeResidueAction] at hσ
  exact ⟨⟨σ, hσ⟩, hs⟩

/-- **Labelled generating tame pair.** In a finite Galois `2`-extension of `ℚ_p`
containing a nonresidue unit radical `u` and a ramified radical `w`, there are a
generator `τ` of inertia and a Frobenius lift `φ` fixing `w`, generating the Galois
group, with `φ τ φ⁻¹ = τ^p` and `τ w = -w`. -/
theorem exists_generating_tame_pair (hp : p ≠ 2) (hG : IsPGroup 2 Gal(L/ℚ_[p]))
    (u : L) (du : ℤ) (hu : u ^ 2 = du) (hdu : ¬(p : ℤ) ∣ du)
    (hnr : (du : ZMod p) ^ ((p - 1) / 2) = -1)
    (w : L) (dw : ℤ) (hw : w ^ 2 = p * dw) (hdw : ¬(p : ℤ) ∣ dw) :
    ∃ τ : inertia p L, ∃ φ : Gal(L/ℚ_[p]),
      Subgroup.zpowers (τ : Gal(L/ℚ_[p])) = inertia p L ∧
      Subgroup.closure ({(τ : Gal(L/ℚ_[p])), φ} : Set Gal(L/ℚ_[p])) = ⊤ ∧
      φ * (τ : Gal(L/ℚ_[p])) * φ⁻¹ = (τ : Gal(L/ℚ_[p])) ^ p ∧
      IsFrobenius p L φ ∧ (τ : Gal(L/ℚ_[p])) w = -w ∧ φ w = w := by
  have hpq : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime)).mpr
    (Ne.symm hp)
  have hq := PadicFiniteGalois.prime_mem_maximalIdeal p L
  obtain ⟨pi, hpi⟩ := (target p L).exists_uniformizer
  have := inertia_isCyclic (unique p L) 2 p hG hpq hq pi hpi
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := inertia p L)
  have hτgen : Subgroup.zpowers (τ : Gal(L/ℚ_[p])) = inertia p L := by
    apply le_antisymm
    · exact Subgroup.zpowers_le.mpr τ.property
    · intro σ hσ
      obtain ⟨n, hn⟩ := hτ ⟨σ, hσ⟩
      exact ⟨n, congrArg Subtype.val hn⟩
  obtain ⟨φ₀, hφ₀, hgen⟩ := exists_generating_frobenius (base p) (target p L)
  rw [PadicFiniteGalois.residue_card] at hφ₀
  -- τ moves w: some inertia element does, and τ generates inertia
  have hτw : (τ : Gal(L/ℚ_[p])) w = -w := by
    have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ_[p] L).injective
    have hs : ((τ : Gal(L/ℚ_[p])) w) ^ 2 = w ^ 2 := by
      rw [← map_pow, hw]
      simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hfix | hneg
    · obtain ⟨σ, hσ⟩ := inertia_moves_ramified hp u du hu hdu hnr w dw hw hdw φ₀ hφ₀ hgen
      have hstab : (τ : Gal(L/ℚ_[p])) ∈ MulAction.stabilizer (Gal(L/ℚ_[p])) w := hfix
      have hσmem : (σ : Gal(L/ℚ_[p])) ∈ Subgroup.zpowers (τ : Gal(L/ℚ_[p])) := by
        rw [hτgen]
        exact σ.property
      have hσfix := (Subgroup.zpowers_le.mpr hstab) hσmem
      change (σ : Gal(L/ℚ_[p])) w = w at hσfix
      have hw0 : w ≠ 0 := by
        intro hz
        have h0 : ((p : ℤ) * dw : ℤ) ≠ 0 :=
          mul_ne_zero (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
            (fun h => hdw (h ▸ dvd_zero _))
        apply h0
        have := hw
        rw [hz, zero_pow (by decide : (2 : ℕ) ≠ 0)] at this
        exact_mod_cast this.symm
      have htwo : (2 : L) * w = 0 := by linear_combination hσ - hσfix
      exact False.elim ((mul_ne_zero two_ne_zero hw0) htwo)
    · exact hneg
  have hτr : completeResidueAction (base p) (target p L) τ = 1 := by
    have he := inertia_eq_ker_completeResidueAction (base p) (target p L)
    exact (show (τ : Gal(L/ℚ_[p])) ∈ (completeResidueAction (base p) (target p L)).ker from
      he ▸ τ.property)
  -- normalize the Frobenius lift to fix w
  have hex : ∃ φ : Gal(L/ℚ_[p]), IsFrobenius p L φ ∧
      (∀ σ, ∃ n : ℕ, completeResidueAction (base p) (target p L) σ =
        (completeResidueAction (base p) (target p L) φ) ^ n) ∧ φ w = w := by
    have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ_[p] L).injective
    have hs : (φ₀ w) ^ 2 = w ^ 2 := by
      rw [← map_pow, hw]
      simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hf | hf
    · exact ⟨φ₀, hφ₀, hgen, hf⟩
    · refine ⟨(τ : Gal(L/ℚ_[p])) * φ₀, ?_, ?_, ?_⟩
      · intro b
        rw [valuationUnitAut_mul, residueUnit_aut_of_inertia (unique p L) τ, hφ₀]
      · simpa only [map_mul, hτr, one_mul] using hgen
      · rw [AlgEquiv.mul_apply, hf, map_neg, hτw, neg_neg]
  obtain ⟨φ, hφ, hφgen, hfix⟩ := hex
  refine ⟨τ, φ, hτgen, ?_, frobenius_conj_eq_pow (unique p L) 2 p hG hpq hq pi hpi φ hφ τ,
    hφ, hτw, hfix⟩
  exact closure_pair_eq_top (completeResidueAction (base p) (target p L)) τ φ
    (hτgen.trans (inertia_eq_ker_completeResidueAction (base p) (target p L))) hφgen

end UnitDistance.Sqrt241.Local.Tame
