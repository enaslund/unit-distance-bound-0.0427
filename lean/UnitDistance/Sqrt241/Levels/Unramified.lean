module

public import UnitDistance.Sqrt241.Levels.LocalData
public import UnitDistance.Sqrt241.Local.Unramified
public import UnitDistance.RelativeUnramifiedIndices
public import UnitDistance.Sqrt241.Genus.Frobenius

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Ramification away from `2, 3, 5` and `K_j / M` unramified

For a finite Galois `K ≤ Ω`:

* `ramificationIdxIn_eq_one_away`: `e_K(p) = 1` for every prime `p ∉ {2, 3, 5, 241}`
  (`Local.inertia_killed`: the absolute inertia group at `p` fixes `Ω`);
* `ramificationIdxIn_241`: `e_K(241) = 2` when `B ≤ K`: `K/B` is unramified at the prime
  `(√241)` (`Local.layer_unramified`, transported to `K` with its `B`-algebra structure),
  and `e_B(241) = 2` (`(241) = (√241)²`, `Base.span_241_eq`); ramification indices are
  multiplicative in the tower `ℤ → 𝓞 B → 𝓞 K`.

Hence for admissible `M ≤ K` (`M` and the levels), `e_K(p) = e_M(p)` for every prime
`p` (at `2, 3, 5` by the exact local types), and `K/M` is unramified at every finite
place (`finiteUnramified_of_le`, via the ℚ package's
`NumberFieldAnalysis.finiteUnramified_of_absolute_ramificationIdx_eq`).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Retained

open Tower Presentation Cut GroupData ProCGroups UnitDistance.PrimeCompletion
open _root_.UnitDistance.Sqrt241.Local IsDedekindDomain NumberFieldAnalysis
open Base (B)
open scoped NumberField

attribute [local instance] PrimeCompletion.primeFact PrimeCompletion.baseRationalAlgebra

/-! ### Away from `2, 3, 5, 241` -/

theorem ramificationIdxIn_eq_one_away (K : IntermediateField ℚ Omega) [FiniteDimensional ℚ K]
    [IsGalois ℚ K] (p : Nat.Primes) (hp : p.val ∉ ({2, 3, 5, 241} : Finset ℕ)) :
    (rationalPrimeIdeal p.val).ramificationIdxIn (𝓞 K) = 1 := by
  rw [← inertiaRestriction_card p K (jK K)]
  have hb : (inertiaRestriction p K (jK K)).range = ⊥ := by
    apply le_antisymm _ bot_le
    rintro _ ⟨σ, rfl⟩
    rw [Subgroup.mem_bot, inertiaRestriction_eq, inertia_killed p hp σ, map_one]
  rw [hb, Subgroup.card_bot]

/-! ### At `241` -/

theorem map_rationalPrimeIdeal_241 :
    (rationalPrimeIdeal 241).map (algebraMap ℤ (𝓞 Base.B)) = Base.P241 ^ 2 := by
  rw [Ideal.map_span, Set.image_singleton, ← Base.span_241_eq]
  congr 1

theorem ramificationIdx_P241 : Base.P241.ramificationIdx ℤ = 2 := by
  have hne : (rationalPrimeIdeal 241).map (algebraMap ℤ (𝓞 Base.B)) ≠ ⊥ := by
    rw [map_rationalPrimeIdeal_241]
    exact pow_ne_zero 2 Base.P241_ne_bot
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity (rationalPrimeIdeal 241) Base.P241 hne,
    map_rationalPrimeIdeal_241]
  exact multiplicity_pow_self_of_prime (Ideal.prime_of_isPrime Base.P241_ne_bot inferInstance) 2

section BAlgebra

variable (K : IntermediateField ℚ Omega)

theorem B_le_lift (hB : BinOmega ≤ K) : B ≤ IntermediateField.lift K := by
  intro x hx
  exact ⟨⟨x, B_le_Omega hx⟩, hB ((mem_BinOmega_iff _).mpr hx), rfl⟩

/-- `B → K` for `B ≤ K ≤ Ω`. -/
def toK (hB : BinOmega ≤ K) : B →+* K where
  toFun b := ⟨⟨(b : CanonicalGenus.Closure), B_le_Omega b.2⟩, hB ((mem_BinOmega_iff _).mpr b.2)⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The `B`-algebra structure of `K ⊇ B`. -/
abbrev algebraBK (hB : BinOmega ≤ K) : Algebra B K := (toK K hB).toAlgebra

/-- `K` as an intermediate field of `Closure / B`. -/
abbrev extK (hB : BinOmega ≤ K) : IntermediateField B CanonicalGenus.Closure :=
  IntermediateField.extendScalars (B_le_lift K hB)

/-- `extK ≃ K` as `B`-algebras. -/
def extEquiv (hB : BinOmega ≤ K) : letI := algebraBK K hB; extK K hB ≃ₐ[B] K :=
  letI := algebraBK K hB
  AlgEquiv.ofRingEquiv (f := (extendScalarsRingEquiv (IntermediateField.lift K)
    (B_le_lift K hB)).symm.trans (IntermediateField.liftAlgEquiv K).symm.toRingEquiv)
    (fun _ => rfl)

theorem extK_le_OmegaBcl (hB : BinOmega ≤ K) : extK K hB ≤ OmegaBcl := by
  rintro _ ⟨z, -, rfl⟩
  exact z.2

end BAlgebra

section Ramification241

variable (K : IntermediateField ℚ Omega) [FiniteDimensional ℚ K] [IsGalois ℚ K]

instance finiteDimensional_extK (hB : BinOmega ≤ K) : FiniteDimensional B (extK K hB) := by
  have : FiniteDimensional ℚ (IntermediateField.lift K) :=
    (IntermediateField.liftAlgEquiv K).toLinearEquiv.finiteDimensional
  exact Module.Finite.of_restrictScalars_finite ℚ B (extK K hB)

instance numberField_extK (hB : BinOmega ≤ K) : NumberField (extK K hB) :=
  NumberField.of_module_finite B _

omit [IsGalois ℚ K] in
theorem unramified_B (hB : BinOmega ≤ K) : letI := algebraBK K hB
    ClassFieldTower.Sawin.IsUnramifiedAtFinitePlacesOutside B K Base.S := by
  let := algebraBK K hB
  exact ClassFieldTower.Sawin.IsUnramifiedAtFinitePlacesOutside.congrTop (extEquiv K hB)
    (layer_unramified (extK K hB) (extK_le_OmegaBcl K hB))

theorem thirty_not_mem_P241 : (30 : 𝓞 B) ∉ Base.P241 := by
  rw [Base.mem_P241, map_ofNat]
  decide

/-- **`e_K(241) = 2`** for a finite Galois `B ≤ K ≤ Ω`. -/
theorem ramificationIdxIn_241 (hB : BinOmega ≤ K) :
    (rationalPrimeIdeal 241).ramificationIdxIn (𝓞 K) = 2 := by
  let := algebraBK K hB
  have : Fact (Nat.Prime 241) := ⟨by norm_num⟩
  obtain ⟨P, hP, hPl⟩ := Genus.exists_prime_liesOver K 241
  have hP0 : P ≠ ⊥ := by
    intro h
    have h241 : ((241 : ℤ) : 𝓞 K) ∈ P := (Genus.intCast_mem_iff P 241).mpr dvd_rfl
    rw [h, Ideal.mem_bot] at h241
    exact absurd h241 (by exact_mod_cast (by norm_num : (241 : ℤ) ≠ 0))
  let W : IsDedekindDomain.HeightOneSpectrum (𝓞 K) := ⟨P, hP, hP0⟩
  let V : Ideal (𝓞 B) := P.under (𝓞 B)
  have hPV : P.LiesOver V := ⟨rfl⟩
  have h241V : (241 : 𝓞 B) ∈ V := by
    change algebraMap (𝓞 B) (𝓞 K) 241 ∈ P
    rw [map_ofNat]
    have h := (Genus.intCast_mem_iff P 241).mpr dvd_rfl
    exact_mod_cast h
  have hVprime : V.IsPrime := Ideal.IsPrime.under (𝓞 B) P
  have hV : V = Base.P241 := Base.eq_P241 h241V
  have hWS : finitePlaceBelow (K := B) W ∉ Base.S := by
    intro h30
    change (30 : 𝓞 B) ∈ V at h30
    rw [hV] at h30
    exact thirty_not_mem_P241 h30
  have hunr : Algebra.IsUnramifiedAt (𝓞 B) P := unramified_B K hB W hWS
  have h1 : P.ramificationIdx (𝓞 B) = 1 := Ideal.ramificationIdx_eq_one P (𝓞 B)
  have htower := Ideal.ramificationIdx_tower (R := ℤ) V P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (rationalPrimeIdeal 241) P Gal(K/ℚ), htower, h1,
    hV, ramificationIdx_P241]

end Ramification241

/-! ### Equal ramification indices give relative unramifiedness -/

/-- If two Galois number fields `M ⊆ K` have the same absolute ramification index at every
rational prime, then `K/M` is unramified at every finite place. -/
theorem finiteUnramified_of_ramificationIdxIn_eq (M K : Type*) [Field M] [NumberField M]
    [IsGalois ℚ M] [Field K] [NumberField K] [IsGalois ℚ K] [Algebra M K]
    (he : ∀ p : ℕ, p.Prime → (rationalPrimeIdeal p).ramificationIdxIn (𝓞 K) =
      (rationalPrimeIdeal p).ramificationIdxIn (𝓞 M)) : FiniteUnramified M K := by
  apply finiteUnramified_of_absolute_ramificationIdx_eq M K
  intro P
  let V := P.under (𝓞 M)
  let : P.asIdeal.IsPrime := P.isPrime
  let : V.asIdeal.IsPrime := V.isPrime
  let p := (P.asIdeal.under ℤ).absNorm
  let : NeZero P.asIdeal := ⟨P.ne_bot⟩
  have hp : p.Prime := Nat.absNorm_under_prime P.asIdeal
  have hspan : rationalPrimeIdeal p = P.asIdeal.under ℤ := Int.ideal_span_absNorm_eq_self _
  let : Fact p.Prime := ⟨hp⟩
  let : P.asIdeal.LiesOver (rationalPrimeIdeal p) := hspan ▸ inferInstance
  let : P.asIdeal.LiesOver V.asIdeal := ⟨rfl⟩
  let : V.asIdeal.LiesOver (rationalPrimeIdeal p) := by
    constructor
    change rationalPrimeIdeal p = (P.asIdeal.under (𝓞 M)).under ℤ
    rw [Ideal.under_under]
    exact hspan
  rw [← Ideal.ramificationIdxIn_eq_ramificationIdx (rationalPrimeIdeal p) P.asIdeal Gal(K/ℚ),
    ← Ideal.ramificationIdxIn_eq_ramificationIdx (rationalPrimeIdeal p) V.asIdeal Gal(M/ℚ)]
  exact he p hp

theorem BinOmega_le_of_admissible {K : IntermediateField ℚ Omega} (hK : input.Admissible K) :
    BinOmega ≤ K :=
  BinOmega_le_EOmega.trans (input.EOmega_le_M.trans hK.M_le)

/-- **The same ramification index at every prime** in all admissible fields. -/
theorem ramificationIdxIn_eq_of_admissible {K L : IntermediateField ℚ Omega}
    [FiniteDimensional ℚ K] [IsGalois ℚ K] [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (hK : input.Admissible K) (hL : input.Admissible L) (p : ℕ) (hp : p.Prime) :
    (rationalPrimeIdeal p).ramificationIdxIn (𝓞 K) =
      (rationalPrimeIdeal p).ramificationIdxIn (𝓞 L) := by
  have hKt := admissible_ramification_residue hK.kernelHat_le hK.fixing_le_core
  have hLt := admissible_ramification_residue hL.kernelHat_le hL.fixing_le_core
  by_cases h2 : p = 2
  · subst h2
    exact (hKt 0).1.trans (hLt 0).1.symm
  by_cases h3 : p = 3
  · subst h3
    exact (hKt 1).1.trans (hLt 1).1.symm
  by_cases h5 : p = 5
  · subst h5
    exact (hKt 2).1.trans (hLt 2).1.symm
  by_cases h241 : p = 241
  · subst h241
    rw [ramificationIdxIn_241 K (BinOmega_le_of_admissible hK),
      ramificationIdxIn_241 L (BinOmega_le_of_admissible hL)]
  have hmem : (⟨p, hp⟩ : Nat.Primes).val ∉ ({2, 3, 5, 241} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨h2, h3, h5, h241⟩
  have hK1 := ramificationIdxIn_eq_one_away K ⟨p, hp⟩ hmem
  have hL1 := ramificationIdxIn_eq_one_away L ⟨p, hp⟩ hmem
  exact hK1.trans hL1.symm

/-- The algebra structure `M → K` for `M ≤ K`. -/
abbrev algebraOfLe {M K : IntermediateField ℚ Omega} (h : M ≤ K) : Algebra M K :=
  (IntermediateField.inclusion h).toRingHom.toAlgebra

/-- **`K/M` is unramified at every finite place** for admissible `K`. -/
theorem finiteUnramified_of_admissible {K : IntermediateField ℚ Omega} [FiniteDimensional ℚ K]
    [IsGalois ℚ K] (hK : input.Admissible K) :
    letI := algebraOfLe hK.M_le
    FiniteUnramified input.M K := by
  let := algebraOfLe hK.M_le
  exact finiteUnramified_of_ramificationIdxIn_eq input.M K
    (fun p hp => ramificationIdxIn_eq_of_admissible hK input.admissible_M p hp)

end UnitDistance.Sqrt241.Retained
