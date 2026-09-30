module

public import UnitDistance.Sqrt241.Local.Place
public import UnitDistance.Sqrt241.Local.Conjugation
public import UnitDistance.Sqrt241.Local.TameLocal
public import UnitDistance.RationalLocalPairGeneration
public import UnitDistance.LocalInertiaFiniteImage
public import UnitDistance.LocalAbsoluteInertiaRestriction
public import UnitDistance.RationalGaloisBaseChange
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueGalois

@[expose] public section
set_option backward.privateInPublic true

/-!
# Labelled tame pairs in the chosen absolute decomposition groups at 3 and 5

Let `p` be an odd prime at which `241` is a square, and let the chosen place above
`p`, restricted to `B`, send the radicands to `c_k · z_k²` (a square-class table with
one ramified entry `c_r = p·d_w` and a nonresidue unit entry). For every finite
Galois `2`-extension `M/ℚ` embedded in the closure and containing the genus roots,
there are `t` in the chosen absolute inertia group and `s` in the chosen absolute
decomposition group such that

* `t` has genus label `e_r` and `s` has the Euler-sign label (`0` at `r`);
* after restriction to `M`: `s t s⁻¹ = t^p`, `t` generates the inertia image and
  `t, s` generate the decomposition image (`exists_absolute_tame_pair`).

This is the B-analogue of `ArithmeticOdd.exists_absolute_generating_tame_pair`.
The ℚ package computes labels through an abelian genus field
(`decomposition_label_independent`); `Gal(E/ℚ)` is not abelian, so here the
embedding change is absorbed into the local roots (`exists_embedding_change`):
the local roots are the preimages in the local field of the images of the genus
roots under the chosen place, whose squares are given by the Base tables.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Local

open NumberField CanonicalGenus Base UnitDistance.PrimeCompletion Multiquadratic
open scoped ValuativeRel
open RamificationTheory.HilbertRamification.Higher
open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField LocalClassFieldTheory
open ArithmeticProP

attribute [local instance] PrimeCompletion.primeFact PrimeCompletion.baseRationalAlgebra

/-! ## Intrinsic versus tame inertia (generic `p`) -/

section Intrinsic

variable (p : ℕ) [Fact p.Prime] (L : Type) [Field L] [Algebra ℚ_[p] L]
  [FiniteDimensional ℚ_[p] L] [IsGalois ℚ_[p] L]
  [ValuativeRel L] [(Tame.target p L).valuation.Compatible]
  (K : Type) [Field K] [ValuativeRel K] [Algebra K L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
  [IsIntegralClosure 𝒪[L] 𝒪[K] L]

theorem tame_inertia_mem_intrinsic (τ : Tame.inertia p L) (σ : Gal(L/K))
    (hσ : ∀ x : L, σ x = (τ : Gal(L/ℚ_[p])) x) :
    σ ∈ (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker := by
  rw [galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_sub_mem_maximalIdeal]
  intro x
  have hx : (Tame.target p L).valuation (x : L) ≤ 1 := by
    have h := (ValuativeRel.isEquiv (ValuativeRel.valuation L) (Tame.target p L).valuation)
      (x : L) 1
    simpa only [map_one] using h.mp x.property
  have hτ := (mem_lowerRamificationGroup_nat_iff (Tame.unique p L) 0 _).mp τ.property
  have hdiff := hτ ⟨(x : L), hx⟩
  have hlt : (Tame.target p L).valuation ((τ : Gal(L/ℚ_[p])) (x : L) - (x : L)) < 1 := by
    have hm : (valuationSubringAutOfUniqueExtension (Tame.unique p L)
        (τ : Gal(L/ℚ_[p]))) ⟨(x : L), hx⟩ - ⟨(x : L), hx⟩ ∈ (Tame.target p L).maximalIdeal := by
      simpa only [Nat.reduceAdd, pow_one] using hdiff
    exact (Tame.target p L).mem_maximalIdeal_iff _ |>.mp hm
  change ¬ IsUnit (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ x - x)
  rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  change (ValuativeRel.valuation L) (σ (x : L) - (x : L)) < 1
  rw [hσ]
  have h := (ValuativeRel.isEquiv (Tame.target p L).valuation (ValuativeRel.valuation L)).lt_iff_lt
    (x := (τ : Gal(L/ℚ_[p])) (x : L) - (x : L)) (y := 1)
  simp only [map_one] at h
  exact h.mp hlt

theorem tame_inertia_mem_of_intrinsic (τ : Gal(L/ℚ_[p])) (σ : Gal(L/K))
    (hσ : ∀ x : L, σ x = τ x)
    (hI : σ ∈ (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker) :
    τ ∈ Tame.inertia p L := by
  rw [galoisGroupResidueAlgEquivHomOfIsIntegralClosure_mem_ker_iff_sub_mem_maximalIdeal] at hI
  rw [mem_lowerRamificationGroup_nat_iff (Tame.unique p L) 0]
  intro x
  have hx : (ValuativeRel.valuation L) (x : L) ≤ 1 := by
    have he := ValuativeRel.isEquiv (Tame.target p L).valuation (ValuativeRel.valuation L)
      (x : L) 1
    simp only [map_one] at he
    exact he.mp x.property
  let xO : 𝒪[L] := ⟨(x : L), hx⟩
  have hd := hI xO
  change ¬IsUnit (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ xO - xO) at hd
  rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one] at hd
  have hd' : (ValuativeRel.valuation L) (σ (x : L) - (x : L)) < 1 := hd
  rw [hσ] at hd'
  have he := (ValuativeRel.isEquiv (ValuativeRel.valuation L) (Tame.target p L).valuation).lt_iff_lt
    (x := τ (x : L) - (x : L)) (y := 1)
  simp only [map_one] at he
  have hm : valuationSubringAutOfUniqueExtension (Tame.unique p L) τ x - x ∈
      (Tame.target p L).maximalIdeal :=
    (Tame.target p L).mem_maximalIdeal_iff _ |>.mpr (he.mp hd')
  simpa only [Nat.reduceAdd, pow_one] using hm

end Intrinsic

/-! ## The absolute finite-level tame pair -/

/-- Sign of an automorphism on the image of a genus root, transported to the
global genus root through the chosen place. -/
theorem decomposition_genusRoot_of_local (p : Nat.Primes) (d : AbsoluteDecomposition p)
    (k : Fin 8) (ε : ZMod 2)
    (h : decompositionEquiv p d (absoluteEmbedding p (genusRoot k)) =
      binarySign ε * absoluteEmbedding p (genusRoot k)) :
    d.val (genusRoot k) = binarySign ε * genusRoot k := by
  apply (absoluteEmbedding p).injective
  change absoluteEmbedding p (d.val (genusRoot k)) = absoluteEmbedding p (binarySign ε * genusRoot k)
  rw [← decomposition_commutes, h, map_mul]
  congr 1
  simp only [binarySign, map_intCast]

variable (p : Nat.Primes) (hsq : IsSquare (241 : ℚ_[p.val]))

set_option maxHeartbeats 800000 in
/-- **Finite-level labelled tame pair at an odd split prime.** -/
theorem exists_absolute_tame_pair (hp : p.val ≠ 2)
    (c : Fin 8 → ℤ)
    (hc : ∀ k, ∃ z : ℚ_[p.val], z ≠ 0 ∧ placeEmb p hsq (alphaB k) = (c k : ℚ_[p.val]) * z ^ 2)
    (r u : Fin 8) (dw : ℤ) (hr : c r = (p.val : ℤ) * dw) (hdw : ¬(p.val : ℤ) ∣ dw)
    (hunit : ∀ k, k ≠ r → ¬(p.val : ℤ) ∣ c k) (hur : u ≠ r)
    (hnr : (c u : ZMod p.val) ^ ((p.val - 1) / 2) = -1)
    (sv : Fin 8 → ZMod 2) (hsvr : sv r = 0)
    (hsv : ∀ k, k ≠ r → (c k : ZMod p.val) ^ ((p.val - 1) / 2) = binarySignInteger (sv k))
    (M : Type) [Field M] [NumberField M] [IsGalois ℚ M] (j : M →ₐ[ℚ] Closure)
    (hM : IsPGroup 2 Gal(M/ℚ)) (hE : ∀ k, genusRoot k ∈ Set.range j) :
    ∃ t : AbsoluteInertia p, ∃ s : AbsoluteDecomposition p,
      HasLabel t.val.val (Pi.single r 1) ∧ HasLabel s.val sv ∧
      decompositionRestriction p M j (s * t.val * s⁻¹ * (t.val ^ p.val)⁻¹) = 1 ∧
      (∀ x : AbsoluteInertia p, ∃ n : ℤ, decompositionRestriction p M j x.val =
        (decompositionRestriction p M j t.val) ^ n) ∧
      ∀ y : AbsoluteDecomposition p, decompositionRestriction p M j y ∈
        Subgroup.closure ({decompositionRestriction p M j t.val,
          decompositionRestriction p M j s} : Set Gal(M/ℚ)) := by
  classical
  let K := Base p
  let L := RationalGaloisBaseChange.Carrier M ℚ_[p.val]
  let : Algebra K L := PrimeCompletion.targetAlgebra p L
  let : Module.Finite K L := PrimeCompletion.targetFinite p L
  let : IsGalois K L := PrimeCompletion.targetGalois p L
  let : NontriviallyNormedField L := finiteExtensionSpectralNormedField K L
  let : ValuativeRel L := finiteExtensionSpectralValuativeRel K L
  let : IsNonarchimedeanLocalField L := finiteExtensionSpectralIsNonarchimedeanLocalField K L
  let : Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L) :=
    finiteExtensionSpectralValuation_hasExtension K L
  let : Algebra 𝒪[K] L := Algebra.ofSubsemiring (ValuativeRel.valuation K).integer
  let : IsIntegralClosure 𝒪[L] 𝒪[K] L := localCompleteDVF_integerRing_isIntegralClosure K L
  let : (PadicFiniteGalois.target p.val L).valuation.Compatible :=
    PrimeCompletion.intrinsicCompatible p L
  let e₀ : M →ₐ[ℚ] L := RationalGaloisBaseChange.embedding M ℚ_[p.val]
  let fL : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let fM : M →ₐ[ℚ] SeparableClosure K := fL.toRingHom.toRatAlgHom.comp e₀
  let f₀ : M →ₐ[ℚ] SeparableClosure K := (absoluteEmbedding p).comp j
  obtain ⟨a, ha⟩ := GaloisEmbedding.exists_embedding_change fM f₀
  -- preimages of the genus roots and the local roots
  choose m hm using hE
  let ρ : Fin 8 → L := fun k => e₀ (a (m k))
  have hρ (k : Fin 8) : fL (ρ k) = absoluteEmbedding p (genusRoot k) := by
    change fM (a (m k)) = _
    rw [ha, ← hm k]
    rfl
  have halg (x : ℚ_[p.val]) : fL (algebraMap ℚ_[p.val] L x) =
      algebraMap K (SeparableClosure K) ((equiv p).symm x) := by
    have hx : algebraMap ℚ_[p.val] L x = algebraMap K L ((equiv p).symm x) := by
      change _ = algebraMap ℚ_[p.val] L ((equiv p) ((equiv p).symm x))
      rw [ContinuousAlgEquiv.apply_symm_apply]
    rw [hx, fL.commutes]
  choose z hz0 hz using hc
  have hρsq (k : Fin 8) : (ρ k) ^ 2 = algebraMap ℚ_[p.val] L ((c k : ℚ_[p.val]) * z k ^ 2) := by
    apply fL.injective
    change fL ((ρ k) ^ 2) = fL (algebraMap ℚ_[p.val] L ((c k : ℚ_[p.val]) * z k ^ 2))
    rw [map_pow, hρ, halg, ← hz, ← map_pow, genusRoot_sq, ← coe_alphaB,
      absoluteEmbedding_coe p hsq]
  let x : Fin 8 → L := fun k => ρ k * (algebraMap ℚ_[p.val] L (z k))⁻¹
  have hzL (k : Fin 8) : algebraMap ℚ_[p.val] L (z k) ≠ 0 :=
    (map_ne_zero (algebraMap ℚ_[p.val] L)).mpr (hz0 k)
  have hxsq (k : Fin 8) : (x k) ^ 2 = (c k : L) := by
    change (ρ k * (algebraMap ℚ_[p.val] L (z k))⁻¹) ^ 2 = _
    rw [mul_pow, hρsq, inv_pow, map_mul, map_pow, map_intCast, mul_assoc, mul_inv_cancel₀
      (pow_ne_zero _ (hzL k)), mul_one]
  have hρx (k : Fin 8) : ρ k = algebraMap ℚ_[p.val] L (z k) * x k := by
    change _ = _ * (ρ k * _)
    rw [mul_comm (ρ k), ← mul_assoc, mul_inv_cancel₀ (hzL k), one_mul]
  -- the local tame pair
  have hG : IsPGroup 2 Gal(L/ℚ_[p.val]) := RationalGaloisBaseChange.isPGroup M ℚ_[p.val] hM
  have hwsq : (x r) ^ 2 = (p.val : L) * (dw : L) := by
    rw [hxsq, hr]
    push_cast
    rfl
  obtain ⟨τL, φL, hIgenL, hDgenL, hrelL, hφL, hτw, hφw⟩ :=
    Tame.exists_generating_tame_pair hp hG (x u) (c u) (hxsq u) (hunit u hur) hnr
      (x r) dw hwsq hdw
  -- actions of the local pair on the local roots
  have hτx (k : Fin 8) : (τL : Gal(L/ℚ_[p.val])) (x k) =
      binarySign ((Pi.single r (1 : ZMod 2) : Fin 8 → ZMod 2) k) * x k := by
    by_cases hk : k = r
    · subst hk
      rw [hτw, Pi.single_eq_same]
      simp [binarySign, binarySignInteger]
    · rw [Tame.inertia_fixes_unit hp τL (x k) (c k) (hxsq k) (hunit k hk),
        Pi.single_eq_of_ne hk, binarySign_zero, one_mul]
  have hφx (k : Fin 8) : φL (x k) = binarySign (sv k) * x k := by
    by_cases hk : k = r
    · subst hk
      rw [hφw, hsvr, binarySign_zero, one_mul]
    · rw [Tame.frobenius_unit hp φL hφL (x k) (c k) (hxsq k) (hunit k hk) (binarySignInteger (sv k))
        (by unfold binarySignInteger; split_ifs <;> simp) (hsv k hk)]
      rfl
  have hscalar (σ : Gal(L/ℚ_[p.val])) (k : Fin 8) (ε : ZMod 2)
      (h : σ (x k) = binarySign ε * x k) : σ (ρ k) = binarySign ε * ρ k := by
    rw [hρx, map_mul, AlgEquiv.commutes, h]
    ring
  have hfLsign (ε : ZMod 2) (y : L) :
      fL (binarySign ε * y) = binarySign ε * fL y := by
    rw [map_mul]
    congr 1
    simp only [binarySign, map_intCast]
  -- transport to the absolute local group
  let τK := (PrimeCompletion.galoisEquiv p L).symm τL.val
  let φK := (PrimeCompletion.galoisEquiv p L).symm φL
  have hτK : τK ∈ (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker :=
    tame_inertia_mem_intrinsic p.val L K τL τK (fun _ ↦ rfl)
  obtain ⟨τ, hτ, hτact⟩ := exists_absoluteInertia_lift K L fL τK hτK
  obtain ⟨φ, hφ⟩ := finiteAbsoluteRestriction_surjective K L fL φK
  have hφact (y : L) : φ (fL y) = fL (φK y) := by
    rw [finiteAbsoluteRestriction_commutes, hφ]
  let t := (decompositionEquiv p).symm τ
  let s := (decompositionEquiv p).symm φ
  have ht : t ∈ AbsoluteInertia p := by
    rw [← decomposition_mem_inertia_iff]
    simpa only [t, ContinuousMulEquiv.apply_symm_apply] using hτ
  -- finite restrictions through the local embedding
  have hτr : GaloisEmbedding.restriction fM (τ.restrictScalars ℚ) =
      RationalGaloisBaseChange.restriction M ℚ_[p.val] τL.val := by
    apply GaloisEmbedding.restriction_unique
    intro y
    change fL (e₀ (RationalGaloisBaseChange.restriction M ℚ_[p.val] τL.val y)) = τ (fL (e₀ y))
    rw [RationalGaloisBaseChange.restriction_commutes]
    exact (hτact (e₀ y)).symm
  have hφr : GaloisEmbedding.restriction fM (φ.restrictScalars ℚ) =
      RationalGaloisBaseChange.restriction M ℚ_[p.val] φL := by
    apply GaloisEmbedding.restriction_unique
    intro y
    change fL (e₀ (RationalGaloisBaseChange.restriction M ℚ_[p.val] φL y)) = φ (fL (e₀ y))
    rw [RationalGaloisBaseChange.restriction_commutes]
    exact (hφact (e₀ y)).symm
  have hr (σ : Gal(SeparableClosure K/K)) :
      GaloisEmbedding.restriction fM (σ.restrictScalars ℚ) =
        RationalGaloisBaseChange.restriction M ℚ_[p.val]
          (PrimeCompletion.galoisEquiv p L (finiteAbsoluteRestriction K L fL σ)) := by
    apply GaloisEmbedding.restriction_unique
    intro y
    change fL (e₀ (RationalGaloisBaseChange.restriction M ℚ_[p.val]
        (PrimeCompletion.galoisEquiv p L (finiteAbsoluteRestriction K L fL σ)) y)) = σ (fL (e₀ y))
    rw [RationalGaloisBaseChange.restriction_commutes]
    exact (finiteAbsoluteRestriction_commutes K L fL σ (e₀ y)).symm
  let rloc : Gal(SeparableClosure K/K) →* Gal(M/ℚ) :=
    (GaloisEmbedding.restriction fM).toMonoidHom.comp (AlgEquiv.restrictScalarsHom ℚ)
  let rj := localRestriction p M j
  have hker : rloc.ker ≤ rj.ker := by
    intro σ hσ
    exact GaloisEmbedding.restriction_eq_one_of_embedding_change fM
      ((absoluteEmbedding p).comp j) (σ.restrictScalars ℚ) hσ
  have hτj : rj τ = decompositionRestriction p M j t := by
    have h := localRestriction_decomposition p M j t
    simpa only [t, ContinuousMulEquiv.apply_symm_apply] using h
  have hφj : rj φ = decompositionRestriction p M j s := by
    have h := localRestriction_decomposition p M j s
    simpa only [s, ContinuousMulEquiv.apply_symm_apply] using h
  refine ⟨⟨t, ht⟩, s, ?_, ?_, ?_, ?_, ?_⟩
  · -- label of t
    intro k
    apply decomposition_genusRoot_of_local p t k
    change decompositionEquiv p ((decompositionEquiv p).symm τ) (absoluteEmbedding p (genusRoot k)) = _
    rw [ContinuousMulEquiv.apply_symm_apply, ← hρ, hτact]
    change fL ((τL : Gal(L/ℚ_[p.val])) (ρ k)) = _
    rw [hscalar _ k _ (hτx k), hfLsign]
  · -- label of s
    intro k
    apply decomposition_genusRoot_of_local p s k
    change decompositionEquiv p ((decompositionEquiv p).symm φ) (absoluteEmbedding p (genusRoot k)) = _
    rw [ContinuousMulEquiv.apply_symm_apply, ← hρ, hφact]
    change fL (φL (ρ k)) = _
    rw [hscalar _ k _ (hφx k), hfLsign]
  · -- the tame relation after restriction to M
    apply (decompositionRestriction_eq_one_iff p M j fM _).mpr
    change rloc (decompositionEquiv p (s * t * s⁻¹ * (t ^ p.val)⁻¹)) = 1
    simp only [map_mul, map_inv, map_pow, s, t, ContinuousMulEquiv.apply_symm_apply]
    apply mul_inv_eq_one.mpr
    change GaloisEmbedding.restriction fM (φ.restrictScalars ℚ) *
      GaloisEmbedding.restriction fM (τ.restrictScalars ℚ) *
      (GaloisEmbedding.restriction fM (φ.restrictScalars ℚ))⁻¹ =
        (GaloisEmbedding.restriction fM (τ.restrictScalars ℚ)) ^ p.val
    rw [hτr, hφr]
    simpa only [map_mul, map_inv, map_pow] using
      congrArg (RationalGaloisBaseChange.restriction M ℚ_[p.val]) hrelL
  · -- inertia generation
    intro xI
    have hIgen : ∀ σ : Gal(SeparableClosure K/K),
        σ ∈ (localResidueDegree K).toMonoidHom.ker →
        ∃ n : ℤ, rloc σ = (rloc τ) ^ n := by
      intro σ hσ
      let σK := finiteAbsoluteRestriction K L fL σ
      let σP := PrimeCompletion.galoisEquiv p L σK
      have hσK : σK ∈ (galoisGroupResidueAlgEquivHomOfIsIntegralClosure K L).ker :=
        finiteResidueInertia_of_absoluteInertia K L fL σ hσ σK
          (fun y ↦ finiteAbsoluteRestriction_commutes K L fL σ y)
      have hσP : σP ∈ Tame.inertia p.val L :=
        tame_inertia_mem_of_intrinsic p.val L K σP σK (fun _ ↦ rfl) hσK
      have hz : σP ∈ Subgroup.zpowers τL.val := by rw [hIgenL]; exact hσP
      obtain ⟨n, hn⟩ := hz
      refine ⟨n, ?_⟩
      change GaloisEmbedding.restriction fM (σ.restrictScalars ℚ) =
        (GaloisEmbedding.restriction fM (τ.restrictScalars ℚ)) ^ n
      rw [hr σ, hτr]
      simpa only [map_zpow] using congrArg (RationalGaloisBaseChange.restriction M ℚ_[p.val]) hn.symm
    obtain ⟨n, hn⟩ := hIgen (decompositionEquiv p xI.val)
      ((decomposition_mem_inertia_iff p xI.val).mpr xI.property)
    refine ⟨n, ?_⟩
    have hg := HomKernelTransfer.eq_zpow_of_eq_zpow rloc rj hker
      (x := decompositionEquiv p xI.val) (t := τ) (n := n) hn
    rw [show rj (decompositionEquiv p xI.val) = decompositionRestriction p M j xI.val from
      localRestriction_decomposition p M j xI.val, hτj] at hg
    exact hg
  · -- decomposition generation
    intro y
    have hDgen : ∀ σ : Gal(SeparableClosure K/K),
        rloc σ ∈ Subgroup.closure ({rloc τ, rloc φ} : Set Gal(M/ℚ)) := by
      intro σ
      change GaloisEmbedding.restriction fM (σ.restrictScalars ℚ) ∈
        Subgroup.closure ({GaloisEmbedding.restriction fM (τ.restrictScalars ℚ),
          GaloisEmbedding.restriction fM (φ.restrictScalars ℚ)} : Set Gal(M/ℚ))
      rw [hr σ, hτr, hφr]
      let σP := PrimeCompletion.galoisEquiv p L (finiteAbsoluteRestriction K L fL σ)
      have hm : σP ∈ Subgroup.closure ({τL.val, φL} : Set Gal(L/ℚ_[p.val])) := by
        rw [hDgenL]
        trivial
      have hmap : RationalGaloisBaseChange.restriction M ℚ_[p.val] σP ∈
          (Subgroup.closure ({τL.val, φL} : Set Gal(L/ℚ_[p.val]))).map
            (RationalGaloisBaseChange.restriction M ℚ_[p.val]) := ⟨σP, hm, rfl⟩
      simpa only [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton] using hmap
    have hrr : rloc (decompositionEquiv p y) ∈ Subgroup.closure (rloc '' ({τ, φ} : Set _)) := by
      have h := hDgen (decompositionEquiv p y)
      simpa only [Set.image_insert_eq, Set.image_singleton] using h
    have hg := HomKernelTransfer.mem_closure_image rloc rj hker
      (S := ({τ, φ} : Set _)) (x := decompositionEquiv p y) hrr
    rw [Set.image_insert_eq, Set.image_singleton, hτj, hφj] at hg
    rw [show decompositionRestriction p M j y = rj (decompositionEquiv p y) from
      (localRestriction_decomposition p M j y).symm]
    exact hg

end UnitDistance.Sqrt241.Local
