module

public import UnitDistance.Sqrt241.V2.Cap41Prime

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Version 2: the window at `41`

The window element `√241 − r ∈ 𝓞 K_j` (`window41`) is fixed by `c_j` (`c₁ ∈ G_B` fixes `B`).
The primes of `K_j` of norm `41⁴` containing it are exactly the primes above the prime
`𝔭 = Pcap ∩ B` of `B` (`mem_window41_iff`): such a prime lies under a `G_B`-translate of `Pcap`
(`eq_smul_Pcap`), and `G_B` fixes `B`; conversely every prime above `𝔭` contains `√241 − r`
and `41`, hence has norm `41⁴` (`absNorm_capped`).

`41` splits in `B` (the chosen decomposition group fixes `B`), so `e(𝔭 | 41) = f(𝔭 | 41) = 1`,
and every prime of `K_j` above `𝔭` has `e = 1`, `f = 4` over `𝔭`. The fundamental identity over
`B` gives `4 · #window = [K_j : B]`, hence **`#window · (2 · 4) = [K_j : ℚ]`**
(`level_window_count_41`), the effective type `(2, 4)` of `Witness` at `41`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.V2

open Tower Retained UnitDistance.NumberFieldAnalysis IsDedekindDomain NumberField
open UnitDistance.PrimeCompletion _root_.UnitDistance.Sqrt241.Local
open scoped Pointwise

attribute [local instance] PrimeCompletion.primeFact PrimeCompletion.baseRationalAlgebra

/-! ### `B` inside `Ω` and the prime `41` -/

theorem BinOmega_finite_galois : FiniteDimensional ℚ BinOmega ∧ IsGalois ℚ BinOmega := by
  apply (InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois BinOmega).mp
  exact ⟨GB_isOpen, GB_normal⟩

instance BinOmega_isGalois : IsGalois ℚ BinOmega := BinOmega_finite_galois.2

instance BinOmega_numberField : NumberField BinOmega := NumberField.of_module_finite ℚ _

/-- `41` splits in `B`: `e = f = 1`. -/
theorem BinOmega_types_41 :
    (rationalPrimeIdeal 41).ramificationIdxIn (𝓞 BinOmega) = 1 ∧
      (rationalPrimeIdeal 41).inertiaDegIn (𝓞 BinOmega) = 1 := by
  have hb : (decompositionRestriction prime41 BinOmega (jK BinOmega)).range = ⊥ := by
    apply le_antisymm _ bot_le
    rintro _ ⟨σ, rfl⟩
    rw [Subgroup.mem_bot, decompositionRestriction_eq, res_eq_one_iff]
    exact decompositionMap_mem_GB prime41 isSquare_241_41 σ
  have hi : (inertiaRestriction prime41 BinOmega (jK BinOmega)).range = ⊥ := by
    apply le_antisymm _ bot_le
    rintro _ ⟨σ, rfl⟩
    rw [Subgroup.mem_bot, inertiaRestriction_eq, res_eq_one_iff]
    exact decompositionMap_mem_GB prime41 isSquare_241_41 σ.val
  exact ramification_residue_of_absolute_image_cards prime41 BinOmega (jK BinOmega) 1 1 one_pos
    (by rw [hi, Subgroup.card_bot]) (by rw [hb, Subgroup.card_bot])

/-! ### The window element is fixed by `c_j` -/

theorem levelConjInt_window41 (j : ℕ) : levelConjInt j (window41 j) = window41 j := by
  apply toOmega_injective
  change cHat (toOmega (level j) (window41 j)) = toOmega (level j) (window41 j)
  rw [toOmega_window41, map_sub, map_intCast, (mem_GB_iff cHat).mp cHat_mem_GB]

/-! ### The base prime `𝔭` of `B` -/

section Base

variable (j : ℕ)

/-- `Pcap` as a nonzero prime. -/
def PcapSpec : HeightOneSpectrum (𝓞 (levelClosure j)) :=
  ⟨Pcap j, inferInstance, Ideal.ne_bot_of_liesOver_of_ne_bot
    (rationalPrimeIdeal_ne_bot_of_prime (p := 41) (by norm_num)) (Pcap j)⟩

/-- `√241 − r` in `𝓞 B`. -/
def windowB : 𝓞 BinOmega := sqrtInt BinOmega le_rfl - (capRoot j : 𝓞 BinOmega)

theorem toOmega_windowB : toOmega BinOmega (windowB j) = rootOmega - (capRoot j : Omega) := by
  rw [windowB, map_sub, map_intCast]
  rfl

end Base

section Count

variable (j : ℕ)

/-- `Bω → K_j → K̃_j`. -/
abbrev algBK : Algebra BinOmega (level j) := algebraOfLe (BinOmega_le_level j)
abbrev algBL : Algebra BinOmega (levelClosure j) :=
  algebraOfLe ((BinOmega_le_level j).trans (level_le_levelClosure j))
abbrev algKL : Algebra (level j) (levelClosure j) := algebraOfLe (level_le_levelClosure j)

/-- **The base prime `𝔭 = Pcap ∩ B`.** -/
def basePrime : HeightOneSpectrum (𝓞 BinOmega) :=
  let := algBL j
  (PcapSpec j).under (𝓞 BinOmega)

theorem mem_basePrime_iff (b : 𝓞 BinOmega) :
    b ∈ (basePrime j).asIdeal ↔
      (letI := algBL j; algebraMap (𝓞 BinOmega) (𝓞 (levelClosure j)) b) ∈ Pcap j := by
  let := algBL j
  rfl

theorem toOmega_algebraMap_BL (b : 𝓞 BinOmega) :
    (letI := algBL j; toOmega (levelClosure j) (algebraMap (𝓞 BinOmega) _ b)) =
      toOmega BinOmega b := rfl

theorem toOmega_algebraMap_BK (b : 𝓞 BinOmega) :
    (letI := algBK j; toOmega (level j) (algebraMap (𝓞 BinOmega) _ b)) =
      toOmega BinOmega b := rfl

theorem toOmega_algebraMap_KL (x : 𝓞 (level j)) :
    (letI := algKL j; toOmega (levelClosure j) (algebraMap (𝓞 (level j)) _ x)) =
      toOmega (level j) x := rfl

theorem windowB_mem : windowB j ∈ (basePrime j).asIdeal := by
  rw [mem_basePrime_iff]
  let := algBL j
  have he : algebraMap (𝓞 BinOmega) (𝓞 (levelClosure j)) (windowB j) =
      sqrtClosure j - (capRoot j : 𝓞 (levelClosure j)) := by
    apply toOmega_injective
    rw [toOmega_algebraMap_BL, toOmega_windowB, map_sub, map_intCast, toOmega_sqrtInt]
  rw [he]
  exact capRoot_mem j

theorem algebraMap_windowB : (letI := algBK j; algebraMap (𝓞 BinOmega) (𝓞 (level j)) (windowB j)) =
    window41 j := by
  let := algBK j
  apply toOmega_injective
  rw [toOmega_algebraMap_BK, toOmega_windowB, toOmega_window41]

theorem fortyone_mem_basePrime : ((41 : ℤ) : 𝓞 BinOmega) ∈ (basePrime j).asIdeal := by
  rw [mem_basePrime_iff, map_intCast, Genus.intCast_mem_iff (p := 41)]
  norm_num

theorem liesOver_of_mem_41 {F : Type*} [Field F] [NumberField F] (P : Ideal (𝓞 F)) [P.IsPrime]
    (h : ((41 : ℤ) : 𝓞 F) ∈ P) : P.LiesOver (rationalPrimeIdeal 41) := by
  constructor
  apply Ideal.IsMaximal.eq_of_le (rationalPrimeIdeal_isMaximal_of_prime (p := 41) (by norm_num))
    (Ideal.IsPrime.ne_top (Ideal.IsPrime.under ℤ P))
  rw [rationalPrimeIdeal, Ideal.span_singleton_le_iff_mem]
  change algebraMap ℤ (𝓞 F) ((41 : ℕ) : ℤ) ∈ P
  simpa using h

/-- **The window at `41` is the fiber above `𝔭`.** -/
theorem mem_window41_iff (P : HeightOneSpectrum (𝓞 (level j))) :
    (letI := algBK j; P.under (𝓞 BinOmega) = basePrime j) ↔
      (Ideal.absNorm P.asIdeal = 41 ^ 4 ∧ window41 j ∈ P.asIdeal) := by
  let := algBK j
  have : P.asIdeal.IsPrime := P.isPrime
  constructor
  · intro h
    have hmem : ∀ b, b ∈ (basePrime j).asIdeal → algebraMap (𝓞 BinOmega) _ b ∈ P.asIdeal := by
      intro b hb
      rw [← h] at hb
      exact hb
    have hw : window41 j ∈ P.asIdeal := by
      rw [← algebraMap_windowB]
      exact hmem _ (windowB_mem j)
    have h41 : ((41 : ℤ) : 𝓞 (level j)) ∈ P.asIdeal := by
      have := hmem _ (fortyone_mem_basePrime j)
      rwa [map_intCast] at this
    have := liesOver_of_mem_41 P.asIdeal h41
    exact ⟨(absNorm_capped j P.asIdeal hw).1, hw⟩
  · rintro ⟨hn, hw⟩
    have hlies : P.asIdeal.LiesOver (rationalPrimeIdeal 41) := by
      have h := primeNormFiber_liesOver (level j) (q := 41 ^ 4) (by norm_num) ⟨P, hn⟩
      have h41 : (41 ^ 4 : ℕ).minFac = 41 := by norm_num
      simpa only [h41] using h
    let := algKL j
    have hP0 : P.asIdeal ≠ ⊥ := P.ne_bot
    have : P.asIdeal.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hP0
    obtain ⟨Q, hQ, hQP⟩ := exists_maximal_liesOver (L := levelClosure j) P.asIdeal
    have : Q.LiesOver (rationalPrimeIdeal 41) := Ideal.LiesOver.trans Q P.asIdeal _
    have hunder : ∀ y : 𝓞 (level j), y ∈ P.asIdeal ↔ algebraMap (𝓞 (level j)) _ y ∈ Q := by
      intro y
      rw [Ideal.over_def Q P.asIdeal]
      rfl
    have hwQ : sqrtClosure j - (capRoot j : 𝓞 (levelClosure j)) ∈ Q := by
      have h := (hunder _).mp hw
      have he : algebraMap (𝓞 (level j)) (𝓞 (levelClosure j)) (window41 j) =
          sqrtClosure j - (capRoot j : 𝓞 (levelClosure j)) := by
        apply toOmega_injective
        rw [toOmega_algebraMap_KL, toOmega_window41, map_sub, map_intCast, toOmega_sqrtInt]
      rwa [he] at h
    obtain ⟨s, hs, rfl⟩ := eq_smul_Pcap j Q hwQ
    apply HeightOneSpectrum.ext
    ext b
    change algebraMap (𝓞 BinOmega) (𝓞 (level j)) b ∈ P.asIdeal ↔ b ∈ (basePrime j).asIdeal
    rw [hunder, mem_basePrime_iff, Ideal.mem_pointwise_smul_iff_inv_smul_mem]
    let := algBL j
    have he : (Input.res (levelClosure j) s)⁻¹ •
        algebraMap (𝓞 (level j)) (𝓞 (levelClosure j)) (algebraMap (𝓞 BinOmega) _ b) =
          algebraMap (𝓞 BinOmega) (𝓞 (levelClosure j)) b := by
      apply toOmega_injective
      rw [← map_inv, toOmega_res_smul, toOmega_algebraMap_KL, toOmega_algebraMap_BK,
        toOmega_algebraMap_BL]
      have hs' : s⁻¹ ∈ BinOmega.fixingSubgroup := GB.inv_mem hs
      exact hs' ⟨toOmega BinOmega b, (b : BinOmega).2⟩
    rw [he]

instance algBK_isScalarTower : letI := algBK j; IsScalarTower ℚ BinOmega (level j) :=
  let := algBK j
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

theorem finrank_level_eq_two_mul :
    let := algBK j
    Module.finrank ℚ (level j) = 2 * Module.finrank BinOmega (level j) := by
  let := algBK j
  have : Module.Free BinOmega (level j) := Module.Free.of_divisionRing _ _
  rw [← Module.finrank_mul_finrank ℚ BinOmega (level j), finrank_BinOmega]

/-- The window at `41` as the fiber above `𝔭`. -/
def window41Equiv :
    let := algBK j
    WindowFiber (level j) (Witness.primeNorm 4) (window41 j) ≃ PrimeFiber BinOmega (level j)
      (basePrime j) :=
  let := algBK j
  Equiv.subtypeEquivRight (fun P => (mem_window41_iff j P).symm)

/-- **The window count at `41`.** -/
theorem level_window_count_41 :
    Nat.card (WindowFiber (level j) (Witness.primeNorm 4) (window41 j)) *
      (Witness.ramification 4 * Witness.residueDegree 4) = Module.finrank ℚ (level j) := by
  let := algBK j
  have hcount := primeFiber_card_mul_of_uniform BinOmega (level j) (basePrime j) 1 4 (by
    intro P
    have : P.1.asIdeal.IsPrime := P.1.isPrime
    have := primeFiber_liesOver BinOmega (level j) (basePrime j) P
    have : (basePrime j).asIdeal.IsPrime := (basePrime j).isPrime
    have h41 : ((41 : ℤ) : 𝓞 (level j)) ∈ P.1.asIdeal := by
      have := Ideal.mem_map_of_mem (algebraMap (𝓞 BinOmega) (𝓞 (level j)))
        (fortyone_mem_basePrime j)
      rw [map_intCast] at this
      exact (Ideal.map_le_of_le_comap (le_of_eq (Ideal.over_def P.1.asIdeal
        (basePrime j).asIdeal))) this
    have : (basePrime j).asIdeal.LiesOver (rationalPrimeIdeal 41) :=
      liesOver_of_mem_41 _ (fortyone_mem_basePrime j)
    have : P.1.asIdeal.LiesOver (rationalPrimeIdeal 41) := liesOver_of_mem_41 _ h41
    have hw : window41 j ∈ P.1.asIdeal := ((mem_window41_iff j P.1).mp P.2).2
    have hBe : (basePrime j).asIdeal.ramificationIdx ℤ = 1 := by
      rw [ramificationIdx_eq_ramificationIdxIn 41]
      exact BinOmega_types_41.1
    have hBf : (basePrime j).asIdeal.inertiaDeg ℤ = 1 := by
      rw [inertiaDeg_eq_inertiaDegIn 41]
      exact BinOmega_types_41.2
    have he := Ideal.ramificationIdx_tower (R := ℤ) (basePrime j).asIdeal P.1.asIdeal
    have hf := Ideal.inertiaDeg_tower (R := ℤ) (basePrime j).asIdeal P.1.asIdeal
    rw [ramificationIdx_41 j P.1.asIdeal, hBe, one_mul] at he
    rw [(absNorm_capped j P.1.asIdeal hw).2, hBf, one_mul] at hf
    exact ⟨he.symm, hf.symm⟩)
  rw [Nat.card_congr (window41Equiv j), Nat.card_eq_fintype_card, finrank_level_eq_two_mul]
  change Fintype.card _ * (2 * 4) = 2 * _
  rw [← hcount]
  ring

end Count

end UnitDistance.Sqrt241.V2
