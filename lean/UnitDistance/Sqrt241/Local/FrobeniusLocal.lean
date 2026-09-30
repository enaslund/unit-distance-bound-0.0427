module

public import UnitDistance.Sqrt241.Local.TameAbsolute
public import UnitDistance.Sqrt241.Genus.Integers
public import UnitDistance.Sqrt241.Base.Residues

@[expose] public section
set_option backward.privateInPublic true

/-!
# Labelled Frobenius elements at `29` (split) and `7` (inert), finite level

* **Split prime.** At an odd prime where `241` is a square and all radicands are
  units, a Frobenius lift of the local field of a finite Galois `M ⊇ E` multiplies
  each genus root by the Euler sign of its square class at the chosen place
  (`exists_absolute_frobenius_split`; same absorption of the embedding change as
  `TameAbsolute.lean`).
* **Inert prime `7`.** `241` is not a square mod `7`, so a Frobenius lift `φ` moves
  `√241`, and `φ²` fixes `B`. For a radicand `α` (a unit in the valuation ring, but
  not a rational integer: no integer represents the non-square unit class of
  `ℚ₄₉`), `φ²(√α) = ε √α` with `ε ≡ α^24 (mod 7)` (`Tame.frobenius_unit_radical'`,
  a valuation-ring version of `OddTame.frobenius_unit_radical`). The signs come from
  the kernel-checked identities `α_k^24 = ε_k + 7 β_k` in `ℚ(√241)`, `β_k` with
  denominators prime to `7` (`radQ_pow_24`, `betaQ_den`): `ε = (+,−,−,−,+,+,+,+)`,
  i.e. label `01110000` (`exists_absolute_frobenius_seven`).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Local

open NumberField CanonicalGenus Base UnitDistance.PrimeCompletion Multiquadratic
open RamificationTheory.HilbertRamification.Higher
open ValuationTheory.DiscreteValuationField.ResidueField
open UnitDistance.OddTame
open ArithmeticProP

attribute [local instance] PrimeCompletion.primeFact PrimeCompletion.baseRationalAlgebra

/-! ## A valuation-ring version of the Frobenius radical lemma -/

namespace Tame

variable {p : ℕ} [Fact p.Prime] {L : Type} [Field L] [Algebra ℚ_[p] L]
  [FiniteDimensional ℚ_[p] L] [IsGalois ℚ_[p] L]

/-- Euler's criterion for a square root of a valuation-ring element fixed by an
automorphism with residue action `x ↦ x^q`, `q = 2k + 1`. -/
theorem frobenius_unit_radical' (hp : p ≠ 2) (q k : ℕ) (hq : q = 2 * k + 1)
    (ψ : Gal(L/ℚ_[p]))
    (hψ : ∀ b : (target p L).valuationSubringˣ,
      residueUnit (dvfValuationSubringUnitAut (unique p L) ψ b) = (residueUnit b) ^ q)
    (a : (target p L).valuationSubringˣ) (D : (target p L).valuationSubring)
    (ha : (a : (target p L).valuationSubring) ^ 2 = D)
    (hD : valuationSubringAutOfUniqueExtension (unique p L) ψ D = D)
    (ε : ℤ) (he : ε = 1 ∨ ε = -1) (hd : ((target p L).residueMap D) ^ k = ε) :
    valuationSubringAutOfUniqueExtension (unique p L) ψ a = ε * (a : (target p L).valuationSubring) := by
  have h2 := PadicFiniteGalois.two_residue_ne_zero p L hp
  have hε : (ε : (target p L).residueField) ≠ 0 := by rcases he with rfl | rfl <;> norm_num
  apply squareRoot_eq_of_residue_eq h2 _ _
  · simpa using mul_ne_zero hε (Units.ne_zero (residueUnit a))
  · rw [← map_pow, ha, hD, mul_pow, ha]
    rcases he with rfl | rfl <;> simp
  · have hres := congrArg Units.val (hψ a)
    change (target p L).residueMap (valuationSubringAutOfUniqueExtension (unique p L) ψ a) =
      ((target p L).residueMap a) ^ q at hres
    rw [hres, map_mul, map_intCast, hq, pow_add, pow_mul, pow_one, ← map_pow, ha, hd]

/-- The square of a Frobenius lift acts on residues of units by `x ↦ x^(p²)`. -/
theorem isFrobenius_sq (φ : Gal(L/ℚ_[p])) (hφ : IsFrobenius p L φ)
    (b : (target p L).valuationSubringˣ) :
    residueUnit (dvfValuationSubringUnitAut (unique p L) (φ * φ) b) = (residueUnit b) ^ (p * p) := by
  rw [valuationUnitAut_mul, hφ, hφ, ← pow_mul]

/-- A rational number with denominator prime to `p` is integral in `L`. -/
theorem rat_mem_valuationSubring (r : ℚ) (hr : ¬(p : ℤ) ∣ (r.den : ℤ)) :
    (r : L) ∈ (target p L).valuation.valuationSubring := by
  obtain ⟨u, hu⟩ := PadicFiniteGalois.integer_isUnit p L (r.den : ℤ) hr
  have hu' : ((u : (target p L).valuationSubring) : L) = (r.den : L) := by
    rw [hu]
    push_cast
    rfl
  have h1 : ((u⁻¹ : (target p L).valuationSubringˣ) : (target p L).valuationSubring) *
      (u : (target p L).valuationSubring) = 1 := u.inv_mul
  have h2 : (((u⁻¹ : (target p L).valuationSubringˣ) : (target p L).valuationSubring) : L) *
      ((u : (target p L).valuationSubring) : L) = 1 := congrArg Subtype.val h1
  rw [hu'] at h2
  have hinv : (((u⁻¹ : (target p L).valuationSubringˣ) : (target p L).valuationSubring) : L) =
      (r.den : L)⁻¹ := eq_inv_of_mul_eq_one_left h2
  have hr' : (r : L) = ((r.num : (target p L).valuationSubring) : L) *
      (((u⁻¹ : (target p L).valuationSubringˣ) : (target p L).valuationSubring) : L) := by
    rw [hinv, Rat.cast_def, div_eq_mul_inv]
    push_cast
    rfl
  rw [hr']
  exact ((r.num : (target p L).valuationSubring) *
    ((u⁻¹ : (target p L).valuationSubringˣ) : (target p L).valuationSubring)).property

end Tame

/-! ## Split primes -/

/-- **Finite-level labelled Frobenius at an odd split prime with a unit table.** -/
theorem exists_absolute_frobenius_split (p : Nat.Primes) (hsq : IsSquare (241 : ℚ_[p.val]))
    (hp : p.val ≠ 2) (c : Fin 8 → ℤ)
    (hc : ∀ k, ∃ z : ℚ_[p.val], z ≠ 0 ∧ placeEmb p hsq (alphaB k) = (c k : ℚ_[p.val]) * z ^ 2)
    (hunit : ∀ k, ¬(p.val : ℤ) ∣ c k)
    (sv : Fin 8 → ZMod 2)
    (hsv : ∀ k, (c k : ZMod p.val) ^ ((p.val - 1) / 2) = binarySignInteger (sv k))
    (M : Type) [Field M] [NumberField M] [IsGalois ℚ M] (j : M →ₐ[ℚ] Closure)
    (hE : ∀ k, genusRoot k ∈ Set.range j) :
    ∃ d : AbsoluteDecomposition p, HasLabel d.val sv := by
  classical
  let K := Base p
  let L := RationalGaloisBaseChange.Carrier M ℚ_[p.val]
  let : Algebra K L := PrimeCompletion.targetAlgebra p L
  let : Module.Finite K L := PrimeCompletion.targetFinite p L
  let : IsGalois K L := PrimeCompletion.targetGalois p L
  let e₀ : M →ₐ[ℚ] L := RationalGaloisBaseChange.embedding M ℚ_[p.val]
  let fL : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let fM : M →ₐ[ℚ] SeparableClosure K := fL.toRingHom.toRatAlgHom.comp e₀
  let f₀ : M →ₐ[ℚ] SeparableClosure K := (absoluteEmbedding p).comp j
  obtain ⟨a, ha⟩ := GaloisEmbedding.exists_embedding_change fM f₀
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
  -- a Frobenius lift of the local field
  obtain ⟨φL, hφL, -⟩ := exists_generating_frobenius (Tame.base p.val) (Tame.target p.val L)
  rw [PadicFiniteGalois.residue_card] at hφL
  have hφx (k : Fin 8) : φL (x k) = binarySign (sv k) * x k := by
    rw [Tame.frobenius_unit hp φL hφL (x k) (c k) (hxsq k) (hunit k) (binarySignInteger (sv k))
      (by unfold binarySignInteger; split_ifs <;> simp) (hsv k)]
    rfl
  have hφρ (k : Fin 8) : φL (ρ k) = binarySign (sv k) * ρ k := by
    rw [hρx, map_mul, AlgEquiv.commutes, hφx]
    ring
  let φK := (PrimeCompletion.galoisEquiv p L).symm φL
  obtain ⟨φ, hφ⟩ := finiteAbsoluteRestriction_surjective K L fL φK
  have hφact (y : L) : φ (fL y) = fL (φK y) := by
    rw [finiteAbsoluteRestriction_commutes, hφ]
  refine ⟨(decompositionEquiv p).symm φ, fun k => ?_⟩
  apply decomposition_genusRoot_of_local p _ k
  rw [ContinuousMulEquiv.apply_symm_apply, ← hρ, hφact]
  change fL (φL (ρ k)) = _
  rw [hφρ, map_mul]
  congr 1
  simp only [binarySign]
  exact map_intCast fL _

/-! ## The inert prime `7` -/

/-- Signs `α_k^24 mod 7`: `+1` for squares of `𝔽₄₉`, `-1` for non-squares. -/
def frob7Sign : Fin 8 → ℤ := ![1, -1, -1, -1, 1, 1, 1, 1]

theorem frob7Sign_eq : ∀ k, frob7Sign k = binarySignInteger (Base.frob7 k) := by decide +kernel

/-- `β_k = (α_k^24 - ε_k)/7`. -/
def betaQ (k : Fin 8) : Genus.Q241 := (1 / 7 : ℚ) • (Genus.radQ k ^ 24 - (frob7Sign k : Genus.Q241))

theorem radQ_pow_24 (k : Fin 8) :
    Genus.radQ k ^ 24 = (frob7Sign k : Genus.Q241) + 7 * betaQ k := by
  unfold betaQ
  rw [Algebra.smul_def, ← mul_assoc, ← map_ofNat (algebraMap ℚ Genus.Q241) 7, ← map_mul]
  norm_num

theorem betaQ_den : ∀ k : Fin 8,
    ¬((7 : ℕ) : ℤ) ∣ ((betaQ k).re.den : ℤ) ∧ ¬((7 : ℕ) : ℤ) ∣ ((betaQ k).im.den : ℤ) := by
  decide +kernel

abbrev prime7 : Nat.Primes := ⟨7, by norm_num⟩

theorem radQ_den : ∀ k : Fin 8,
    ¬((prime7.val : ℕ) : ℤ) ∣ ((Genus.radQ k).re.den : ℤ) ∧
      ¬((prime7.val : ℕ) : ℤ) ∣ ((Genus.radQ k).im.den : ℤ) := by
  decide +kernel

theorem not_seven_dvd_241 : ¬((prime7.val : ℕ) : ℤ) ∣ 241 := by decide

theorem euler_241_seven : ((241 : ℤ) : ZMod prime7.val) ^ ((prime7.val - 1) / 2) = -1 := by decide

/-- **Finite-level labelled Frobenius at `7`**: an element of the chosen decomposition group
moving `√241` whose square has label `01110000` (`Base.frob7`). -/
theorem exists_absolute_frobenius_seven
    (M : Type) [Field M] [NumberField M] [IsGalois ℚ M] (j : M →ₐ[ℚ] Closure)
    (hE : ∀ k, genusRoot k ∈ Set.range j) (hB : baseRoot ∈ Set.range j) :
    ∃ d : AbsoluteDecomposition prime7,
      d.val baseRoot = -baseRoot ∧ HasLabel (d.val ^ 2) Base.frob7 := by
  classical
  let p := prime7
  have hp : p.val ≠ 2 := by decide
  let K := Base p
  let L := RationalGaloisBaseChange.Carrier M ℚ_[p.val]
  let : Algebra K L := PrimeCompletion.targetAlgebra p L
  let : Module.Finite K L := PrimeCompletion.targetFinite p L
  let : IsGalois K L := PrimeCompletion.targetGalois p L
  let e₀ : M →ₐ[ℚ] L := RationalGaloisBaseChange.embedding M ℚ_[p.val]
  let fL : L →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let fM : M →ₐ[ℚ] SeparableClosure K := fL.toRingHom.toRatAlgHom.comp e₀
  let f₀ : M →ₐ[ℚ] SeparableClosure K := (absoluteEmbedding p).comp j
  obtain ⟨a, ha⟩ := GaloisEmbedding.exists_embedding_change fM f₀
  choose m hm using hE
  obtain ⟨ms, hms⟩ := hB
  let ρ : M →ₐ[ℚ] L := e₀.comp (a : M →ₐ[ℚ] M)
  have hρ (y : M) : fL (ρ y) = absoluteEmbedding p (j y) := by
    change fM (a y) = _
    rw [ha]
    rfl
  -- relations in M
  have hms2 : ms ^ 2 = 241 := by
    apply j.injective
    change j (ms ^ 2) = j 241
    rw [map_pow, hms, baseRoot_sq, map_ofNat]
  have hmk (k : Fin 8) : m k ^ 2 = (radicandA k : M) + (radicandB k : M) * ms := by
    apply j.injective
    change j (m k ^ 2) = j ((radicandA k : M) + (radicandB k : M) * ms)
    rw [map_pow, hm k, genusRoot_sq, map_add, map_mul, map_ratCast, map_ratCast, hms]
    rfl
  let s : L := ρ ms
  have hs2 : s ^ 2 = (241 : ℤ) := by
    change (ρ ms) ^ 2 = _
    rw [← map_pow, hms2, map_ofNat]
    norm_num
  let xk : Fin 8 → L := fun k => ρ (m k)
  have hxk (k : Fin 8) : xk k ^ 2 = (radicandA k : L) + (radicandB k : L) * s := by
    change (ρ (m k)) ^ 2 = _
    rw [← map_pow, hmk, map_add, map_mul, map_ratCast, map_ratCast]
  -- the evaluation of `ℚ(√241)` at `s`
  have hsmul : s * s = (241 : ℚ) • (1 : L) + (0 : ℚ) • s := by
    rw [← sq, hs2]
    simp [Algebra.smul_def]
  let lam : Genus.Q241 →ₐ[ℚ] L := QuadraticAlgebra.lift ⟨s, hsmul⟩
  have hlam (w : Genus.Q241) : lam w = (w.re : L) + (w.im : L) * s := by
    simp [lam, QuadraticAlgebra.lift_apply_apply, Algebra.smul_def]
  have hlamrad (k : Fin 8) : lam (Genus.radQ k) = xk k ^ 2 := by
    rw [hlam, hxk]
    rfl
  -- integrality
  have hsint : s ∈ (Tame.target p.val L).valuation.valuationSubring :=
    PadicFiniteGalois.radical_integral p.val L s 241 hs2
  have hlamint (w : Genus.Q241) (hre : ¬(p.val : ℤ) ∣ (w.re.den : ℤ))
      (him : ¬(p.val : ℤ) ∣ (w.im.den : ℤ)) :
      lam w ∈ (Tame.target p.val L).valuation.valuationSubring := by
    rw [hlam]
    exact add_mem (Tame.rat_mem_valuationSubring _ hre)
      (mul_mem (Tame.rat_mem_valuationSubring _ him) hsint)
  -- a Frobenius lift of the local field
  obtain ⟨φL, hφL, -⟩ := exists_generating_frobenius (Tame.base p.val) (Tame.target p.val L)
  rw [PadicFiniteGalois.residue_card] at hφL
  have hφs : φL s = -s := by
    rw [Tame.frobenius_unit hp φL hφL s 241 hs2 not_seven_dvd_241 (-1) (Or.inr rfl)
      euler_241_seven]
    push_cast
    ring
  have hφφs : (φL * φL) s = s := by
    rw [AlgEquiv.mul_apply, hφs, map_neg, hφs, neg_neg]
  have hφφlam (w : Genus.Q241) : (φL * φL) (lam w) = lam w := by
    rw [hlam, map_add, map_mul, map_ratCast, map_ratCast, hφφs]
  -- action of φ² on the genus roots
  have hφφx (k : Fin 8) : (φL * φL) (xk k) = (frob7Sign k : L) * xk k := by
    let D : (Tame.target p.val L).valuationSubring :=
      ⟨lam (Genus.radQ k), hlamint _ (radQ_den k).1 (radQ_den k).2⟩
    have hxint : xk k ∈ (Tame.target p.val L).valuation.valuationSubring := by
      change (Tame.target p.val L).valuation (xk k) ≤ 1
      apply (pow_le_one_iff_of_nonneg (zero_le) (by decide : (2 : ℕ) ≠ 0)).mp
      rw [← map_pow, ← hlamrad]
      exact D.property
    let X : (Tame.target p.val L).valuationSubring := ⟨xk k, hxint⟩
    have hX2 : X ^ 2 = D := Subtype.ext (hlamrad k).symm
    -- the residue of D^24
    have hβ := betaQ_den k
    let Bβ : (Tame.target p.val L).valuationSubring := ⟨lam (betaQ k), hlamint _ hβ.1 hβ.2⟩
    have hD24 : D ^ 24 = (frob7Sign k : (Tame.target p.val L).valuationSubring) + 7 * Bβ := by
      apply Subtype.ext
      change (lam (Genus.radQ k)) ^ 24 = ((frob7Sign k : ℤ) : L) + 7 * lam (betaQ k)
      rw [← map_pow, radQ_pow_24, map_add, map_mul, map_intCast, map_ofNat]
    have hres : ((Tame.target p.val L).residueMap D) ^ ((p.val * p.val - 1) / 2) = frob7Sign k := by
      have h24 : (p.val * p.val - 1) / 2 = 24 := by decide
      rw [h24, ← map_pow, hD24, map_add, map_mul, map_intCast]
      have h7 : (Tame.target p.val L).residueMap (7 : (Tame.target p.val L).valuationSubring) = 0 := by
        rw [IsLocalRing.residue_eq_zero_iff]
        exact_mod_cast PadicFiniteGalois.prime_mem_maximalIdeal p.val L
      rw [h7, zero_mul, add_zero]
    have hDunit : IsUnit D := by
      rw [← isUnit_pow_iff (by decide : (24 : ℕ) ≠ 0), hD24]
      apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
      rw [map_add, map_mul, map_intCast]
      have h7 : (Tame.target p.val L).residueMap (7 : (Tame.target p.val L).valuationSubring) = 0 := by
        rw [IsLocalRing.residue_eq_zero_iff]
        exact_mod_cast PadicFiniteGalois.prime_mem_maximalIdeal p.val L
      rw [h7, zero_mul, add_zero]
      have hs1 : frob7Sign k = 1 ∨ frob7Sign k = -1 := by fin_cases k <;> simp [frob7Sign]
      rcases hs1 with h | h <;> rw [h] <;> simp
    have hXunit : IsUnit X := (isUnit_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp (hX2 ▸ hDunit)
    have hDfix : valuationSubringAutOfUniqueExtension (Tame.unique p.val L) (φL * φL) D = D :=
      Subtype.ext (hφφlam _)
    have hsign : frob7Sign k = 1 ∨ frob7Sign k = -1 := by fin_cases k <;> simp [frob7Sign]
    have hv := congrArg Subtype.val (Tame.frobenius_unit_radical' hp (p.val * p.val)
      ((p.val * p.val - 1) / 2) (by decide) (φL * φL) (Tame.isFrobenius_sq φL hφL) hXunit.unit D
      (by rw [hXunit.unit_spec]; exact hX2) hDfix (frob7Sign k) hsign hres)
    change (φL * φL) ((hXunit.unit : (Tame.target p.val L).valuationSubring) : L) =
      ((frob7Sign k : (Tame.target p.val L).valuationSubring) : L) *
        ((hXunit.unit : (Tame.target p.val L).valuationSubring) : L) at hv
    rw [hXunit.unit_spec] at hv
    simpa using hv
  -- absolute lift
  let φK := (PrimeCompletion.galoisEquiv p L).symm φL
  obtain ⟨φ, hφ⟩ := finiteAbsoluteRestriction_surjective K L fL φK
  have hφact (y : L) : φ (fL y) = fL (φK y) := by
    rw [finiteAbsoluteRestriction_commutes, hφ]
  let d := (decompositionEquiv p).symm φ
  have hdφ : decompositionEquiv p d = φ := ContinuousMulEquiv.apply_symm_apply _ _
  refine ⟨d, ?_, fun k => ?_⟩
  · apply (absoluteEmbedding p).injective
    change absoluteEmbedding p (d.val baseRoot) = absoluteEmbedding p (-baseRoot)
    rw [← decomposition_commutes, hdφ, map_neg, ← hms, ← hρ, hφact]
    change fL (φL s) = -fL s
    rw [hφs, map_neg]
  · have h := decomposition_genusRoot_of_local p (d ^ 2) k (Base.frob7 k)
    change (d ^ 2).val (genusRoot k) = _
    apply h
    rw [map_pow, hdφ, ← hm k, ← hρ, sq, AlgEquiv.mul_apply, hφact, hφact]
    change fL (φL (φL (xk k))) = _
    rw [← AlgEquiv.mul_apply, hφφx, map_mul]
    congr 1
    rw [frob7Sign_eq]
    simp only [binarySign]
    exact map_intCast fL _

end UnitDistance.Sqrt241.Local
