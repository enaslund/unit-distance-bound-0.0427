module

public import UnitDistance.Sqrt241.Generators.Label

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# The dyadic radical `√β₁` lies in `Ω` (dyadic link, step 1)

`β₁ = a + b √π₂'` with `a = -25 + 2√241`, `b = -139 - 9√241` (`√π₂' = genusRoot 3`)
and `β̄₁ = a - b √π₂'` satisfy `β₁ β̄₁ = π₃' = α₅` (`beta_mul_betaBar`). Let
`F₁ = B(√α₃, √α₅)` (an admissible layer: compositum of two `quadField`s) and
`t = √β₁`. If `t ∉ F₁`, then `K = F₁(t)` is Galois over `B` (every `B`-conjugate of
`t` is `±t` or `±√α₅/t`), its Galois group is a 2-group (`[K:F₁] = 2`), and it is
unramified outside `S`: `F₁/B` is, and `K/F₁` is unramified at every prime not above
`30` because `2` and `β₁` are units there (`β₁ β̄₁ = α₅`,
`QuadraticRamification.isUnramifiedAt_of_not_mem`). Hence `K ≤ Ω`
(`Tower.le_OmegaBcl_of_admissible`) and `√β₁ ∈ Ω` (`sqrtBeta_mem_Omega`).
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace UnitDistance.Sqrt241.DyadicLink

open Tower Base CanonicalGenus IntermediateField ClassFieldTower.Sawin Polynomial

/-! ### Transitivity of unramifiedness outside a set -/

/-- A tower `k → K → F`: if `K/k` is unramified outside `T` and `F/K` is unramified
at every prime of `F` whose restriction to `k` lies outside `T`, then `F/k` is
unramified outside `T`. -/
theorem isUnramifiedAtFinitePlacesOutside_trans {k K F : Type*} [Field k] [NumberField k]
    [Field K] [NumberField K] [Field F] [NumberField F] [Algebra k K] [Algebra k F]
    [Algebra K F] [IsScalarTower k K F] {T : Set (HeightOneSpectrum (𝓞 k))}
    (hkK : IsUnramifiedAtFinitePlacesOutside k K T)
    (hKF : ∀ P : HeightOneSpectrum (𝓞 F), finitePlaceBelow (K := k) P ∉ T →
      Algebra.IsUnramifiedAt (𝓞 K) P.asIdeal) :
    IsUnramifiedAtFinitePlacesOutside k F T := by
  intro P hP
  let p : HeightOneSpectrum (𝓞 K) := finitePlaceBelow (K := K) P
  have hlies : P.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  have hp : finitePlaceBelow (K := k) p ∉ T := by
    rw [finitePlaceBelow_finitePlaceBelow]
    exact hP
  have h1 : Algebra.IsUnramifiedAt (𝓞 k) p.asIdeal := hkK p hp
  have h2 : Algebra.IsUnramifiedAt (𝓞 K) P.asIdeal := hKF P hP
  exact Algebra.IsUnramifiedAt.comp (R := 𝓞 k) p.asIdeal P.asIdeal

/-! ### The radicand -/

/-- `a = -25 + 2√241 ∈ 𝓞 B`. -/
def aInt : 𝓞 B := -25 + 2 * sqrt241Int

/-- `b = -139 - 9√241 ∈ 𝓞 B`. -/
def bInt : 𝓞 B := -139 - 9 * sqrt241Int

theorem coe_sqrt241 : ((sqrt241 : B) : Closure) = baseRoot := rfl

theorem coe_aInt : (((aInt : 𝓞 B) : B) : Closure) = -25 + 2 * baseRoot := by
  simp only [aInt, map_add, map_mul, map_neg, map_ofNat, coe_sqrt241Int]
  push_cast
  rfl

theorem coe_bInt : (((bInt : 𝓞 B) : B) : Closure) = -139 - 9 * baseRoot := by
  simp only [bInt, map_sub, map_mul, map_neg, map_ofNat, coe_sqrt241Int]
  push_cast
  rfl

/-- `β₁ = (-25 + 2√241) + (-139 - 9√241) √π₂'` in the closure. -/
def beta : Closure := (-25 + 2 * baseRoot) + (-139 - 9 * baseRoot) * genusRoot 3

/-- `β̄₁ = (-25 + 2√241) - (-139 - 9√241) √π₂'` in the closure. -/
def betaBar : Closure := (-25 + 2 * baseRoot) - (-139 - 9 * baseRoot) * genusRoot 3

/-- **The norm identity** `β₁ β̄₁ = π₃' = α₅`. -/
theorem beta_mul_betaBar : beta * betaBar = radicand 5 := by
  have hγ := genusRoot_sq 3
  have hr := baseRoot_sq
  simp only [radicand, radicandA, radicandB, Fin.isValue, Matrix.cons_val] at hγ ⊢
  unfold beta betaBar
  push_cast at hγ ⊢
  linear_combination (-(-139 - 9 * baseRoot) ^ 2) * hγ +
    (31833 / 2 * baseRoot + 489113 / 2) * hr

theorem beta_mul_betaBar' : beta * betaBar = genusRoot 5 ^ 2 := by
  rw [beta_mul_betaBar, genusRoot_sq]

theorem beta_ne_zero : beta ≠ 0 := by
  intro h
  apply Genus.radicand_ne_zero 5
  rw [← beta_mul_betaBar, h, zero_mul]

/-- A chosen square root `t = √β₁` in the closure. -/
def sqrtBeta : Closure := squareRoot beta

theorem sqrtBeta_sq : sqrtBeta ^ 2 = beta := squareRoot_sq beta

theorem sqrtBeta_ne_zero : sqrtBeta ≠ 0 := by
  intro h
  apply beta_ne_zero
  rw [← sqrtBeta_sq, h]
  ring

/-- `(√α₅ / t)² = β̄₁`. -/
theorem sq_genusRoot_div_sqrtBeta : (genusRoot 5 / sqrtBeta) ^ 2 = betaBar := by
  rw [div_pow, sqrtBeta_sq, ← beta_mul_betaBar']
  field_simp [beta_ne_zero]

/-! ### The admissible layer `F₁ = B(√α₃, √α₅)` -/

/-- `F₁ = B(√π₂', √π₃')`. -/
def F1 : IntermediateField B Closure := quadField 3 ⊔ quadField 5

instance F1_finiteDimensional : FiniteDimensional B F1 :=
  IntermediateField.finiteDimensional_sup _ _

instance F1_isGalois : IsGalois B F1 := inferInstanceAs (IsGalois B ↥(quadField 3 ⊔ quadField 5))

instance F1_numberField : NumberField F1 := NumberField.of_module_finite B F1

theorem F1_isPGroup : IsPGroup 2 (F1 ≃ₐ[B] F1) :=
  isPGroup_galois_sup (quadField 3) (quadField 5) (quadField_isPGroup 3) (quadField_isPGroup 5)

theorem F1_unramified : IsUnramifiedAtFinitePlacesOutside B F1 S :=
  IsUnramifiedAtFinitePlacesOutside.sup (quadField 3) (quadField 5) S
    (quadField_unramified 3) (quadField_unramified 5)

theorem F1_le_OmegaBcl : F1 ≤ OmegaBcl :=
  sup_le (quadField_le_OmegaBcl 3) (quadField_le_OmegaBcl 5)

theorem genusRoot_three_mem_F1 : genusRoot 3 ∈ F1 :=
  (le_sup_left : quadField 3 ≤ F1) (genusRoot_mem_quadField 3)

theorem genusRoot_five_mem_F1 : genusRoot 5 ∈ F1 :=
  (le_sup_right : quadField 5 ≤ F1) (genusRoot_mem_quadField 5)

theorem baseRoot_mem_F1 : baseRoot ∈ F1 := by
  have h : algebraMap B Closure sqrt241 ∈ F1 := F1.algebraMap_mem sqrt241
  exact h

/-- `√π₂'` as an algebraic integer of `F₁`. -/
def gammaO : 𝓞 F1 :=
  ⟨⟨genusRoot 3, genusRoot_three_mem_F1⟩, by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    have h : (⟨genusRoot 3, genusRoot_three_mem_F1⟩ : F1) ^ 2 =
        algebraMap B F1 ((alpha 3 : 𝓞 B) : B) := by
      apply Subtype.ext
      change genusRoot 3 ^ 2 = _
      rw [genusRoot_sq_alpha]
      rfl
    rw [h]
    exact ((alpha 3).2).map (IsScalarTower.toAlgHom ℤ B F1)⟩

theorem coe_gammaO : (((gammaO : 𝓞 F1) : F1) : Closure) = genusRoot 3 := rfl

/-- `β₁ ∈ 𝓞 F₁`. -/
def betaO : 𝓞 F1 := algebraMap (𝓞 B) (𝓞 F1) aInt + algebraMap (𝓞 B) (𝓞 F1) bInt * gammaO

/-- `β̄₁ ∈ 𝓞 F₁`. -/
def betaBarO : 𝓞 F1 := algebraMap (𝓞 B) (𝓞 F1) aInt - algebraMap (𝓞 B) (𝓞 F1) bInt * gammaO

theorem coe_algebraMap_O (x : 𝓞 B) :
    (((algebraMap (𝓞 B) (𝓞 F1) x : 𝓞 F1) : F1) : Closure) = (((x : 𝓞 B) : B) : Closure) := rfl

theorem coe_betaO : (((betaO : 𝓞 F1) : F1) : Closure) = beta := by
  simp only [betaO, map_add, map_mul]
  change (((algebraMap (𝓞 B) (𝓞 F1) aInt : 𝓞 F1) : F1) : Closure) +
    (((algebraMap (𝓞 B) (𝓞 F1) bInt : 𝓞 F1) : F1) : Closure) *
      (((gammaO : 𝓞 F1) : F1) : Closure) = beta
  rw [coe_algebraMap_O, coe_algebraMap_O, coe_gammaO, coe_aInt, coe_bInt]
  rfl

theorem coe_betaBarO : (((betaBarO : 𝓞 F1) : F1) : Closure) = betaBar := by
  simp only [betaBarO, map_sub, map_mul]
  change (((algebraMap (𝓞 B) (𝓞 F1) aInt : 𝓞 F1) : F1) : Closure) -
    (((algebraMap (𝓞 B) (𝓞 F1) bInt : 𝓞 F1) : F1) : Closure) *
      (((gammaO : 𝓞 F1) : F1) : Closure) = betaBar
  rw [coe_algebraMap_O, coe_algebraMap_O, coe_gammaO, coe_aInt, coe_bInt]
  rfl

theorem coe_O_injective : Function.Injective (fun x : 𝓞 F1 => ((x : F1) : Closure)) :=
  Subtype.val_injective.comp RingOfIntegers.coe_injective

theorem betaO_mul_betaBarO : betaO * betaBarO = algebraMap (𝓞 B) (𝓞 F1) (alpha 5) := by
  apply coe_O_injective
  change (((betaO : 𝓞 F1) : F1) : Closure) * (((betaBarO : 𝓞 F1) : F1) : Closure) =
    (((algebraMap (𝓞 B) (𝓞 F1) (alpha 5) : 𝓞 F1) : F1) : Closure)
  rw [coe_betaO, coe_betaBarO, beta_mul_betaBar, coe_algebraMap_O, coe_alpha]

theorem beta_mem_F1 : beta ∈ F1 := coe_betaO ▸ ((betaO : 𝓞 F1) : F1).2

/-! ### The quadratic extension `K₁ = F₁(√β₁)` -/

theorem isIntegral_sqrtBeta : IsIntegral F1 sqrtBeta :=
  (Algebra.IsIntegral.isIntegral (R := B) sqrtBeta).tower_top

/-- `K₁ = F₁(√β₁)`, as an intermediate field over `F₁`. -/
def K1 : IntermediateField F1 Closure := IntermediateField.adjoin F1 {sqrtBeta}

instance K1_finiteDimensional : FiniteDimensional F1 K1 :=
  IntermediateField.adjoin.finiteDimensional isIntegral_sqrtBeta

instance K1_numberField : NumberField K1 := NumberField.of_module_finite F1 K1

theorem sqrtBeta_mem_K1 : sqrtBeta ∈ K1 := IntermediateField.mem_adjoin_simple_self F1 sqrtBeta

/-- If `√β₁ ∉ F₁`, then `β₁` is not a square in `F₁`. -/
theorem nonsquare_beta (h : sqrtBeta ∉ F1) : KummerInvariant.Nonsquare ((betaO : 𝓞 F1) : F1) := by
  intro u hu
  apply h
  have hu' : (u : Closure) ^ 2 = sqrtBeta ^ 2 := by
    rw [sqrtBeta_sq, ← coe_betaO, ← hu]
    rfl
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hu' with h1 | h1
  · rw [← h1]
    exact u.2
  · rw [← neg_neg sqrtBeta, ← h1]
    exact neg_mem u.2

/-- `√β₁` as an element of `K₁`. -/
def tK1 : K1 := AdjoinSimple.gen F1 sqrtBeta

theorem coe_tK1 : (tK1 : Closure) = sqrtBeta := AdjoinSimple.coe_gen F1 sqrtBeta

theorem tK1_sq : tK1 ^ 2 = algebraMap F1 K1 ((betaO : 𝓞 F1) : F1) := by
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow, coe_tK1, IntermediateField.coe_algebraMap_apply,
    IntermediateField.algebraMap_apply, sqrtBeta_sq, coe_betaO]

/-- The generator `√β₁` of `K₁` as an algebraic integer. -/
def tO : 𝓞 K1 :=
  ⟨tK1, by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [tK1_sq]
    exact ((betaO : 𝓞 F1).2).map (IsScalarTower.toAlgHom ℤ F1 K1)⟩

theorem coe_tO : ((tO : 𝓞 K1) : K1) = tK1 := rfl

theorem tO_sq : tO ^ 2 = algebraMap (𝓞 F1) (𝓞 K1) betaO := by
  apply RingOfIntegers.ext
  rw [RingOfIntegers.coe_eq_algebraMap, map_pow, ← RingOfIntegers.coe_eq_algebraMap, coe_tO,
    tK1_sq, RingOfIntegers.coe_eq_algebraMap, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply (𝓞 F1) F1 K1]
  rfl

theorem tO_adjoin : Algebra.adjoin F1 {((tO : 𝓞 K1) : K1)} = ⊤ := by
  rw [coe_tO]
  exact (IntermediateField.adjoin.powerBasis isIntegral_sqrtBeta).adjoin_gen_eq_top

/-- **Kummer step.** At every prime of `K₁` not above `30`, `K₁/F₁` is unramified. -/
theorem K1_unramifiedAt (h : sqrtBeta ∉ F1) (P : HeightOneSpectrum (𝓞 K1))
    (hP : finitePlaceBelow (K := B) P ∉ S) : Algebra.IsUnramifiedAt (𝓞 F1) P.asIdeal := by
  have h30 : (30 : 𝓞 B) ∉ P.asIdeal.under (𝓞 B) := hP
  apply QuadraticRamification.isUnramifiedAt_of_not_mem F1 K1 betaO (nonsquare_beta h) tO tO_sq
    tO_adjoin P.asIdeal
  · intro h2
    apply h30
    rw [Ideal.mem_under, map_ofNat]
    have h15 : (30 : 𝓞 K1) = 15 * 2 := by norm_num
    rw [h15]
    exact P.asIdeal.mul_mem_left 15 h2
  · intro hb
    apply h30
    apply thirty_mem_of_alpha_mem 5 (P := P.asIdeal.under (𝓞 B))
    rw [Ideal.mem_under]
    have he : algebraMap (𝓞 B) (𝓞 K1) (alpha 5) =
        algebraMap (𝓞 F1) (𝓞 K1) betaO * algebraMap (𝓞 F1) (𝓞 K1) betaBarO := by
      rw [← map_mul, betaO_mul_betaBarO, ← IsScalarTower.algebraMap_apply]
    rw [he]
    exact P.asIdeal.mul_mem_right _ hb

theorem K1_unramified (h : sqrtBeta ∉ F1) : IsUnramifiedAtFinitePlacesOutside B K1 S :=
  isUnramifiedAtFinitePlacesOutside_trans F1_unramified (K1_unramifiedAt h)

/-! ### The field `K = F₁(√β₁)` over `B` -/

/-- `K = F₁(√β₁)` as an intermediate field over `B`. -/
def Kfield : IntermediateField B Closure := K1.restrictScalars B

theorem mem_Kfield {x : Closure} : x ∈ Kfield ↔ x ∈ K1 := IntermediateField.mem_restrictScalars B

theorem Kfield_eq : Kfield = IntermediateField.adjoin B ((F1 : Set Closure) ∪ {sqrtBeta}) :=
  IntermediateField.restrictScalars_adjoin B F1 {sqrtBeta}

theorem F1_le_Kfield : F1 ≤ Kfield := by
  rw [Kfield_eq]
  exact fun x hx => IntermediateField.subset_adjoin B _ (Or.inl hx)

theorem sqrtBeta_mem_Kfield : sqrtBeta ∈ Kfield := mem_Kfield.mpr sqrtBeta_mem_K1

/-- `K₁` and `K` are the same field (identity on elements). -/
def K1equiv : K1 ≃ₐ[B] Kfield where
  toFun x := ⟨x.1, mem_Kfield.mpr x.2⟩
  invFun x := ⟨x.1, mem_Kfield.mp x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

instance K1_finiteDimensional_B : FiniteDimensional B K1 := FiniteDimensional.trans B F1 K1

instance Kfield_finiteDimensional : FiniteDimensional B Kfield :=
  K1equiv.toLinearEquiv.finiteDimensional

instance Kfield_numberField : NumberField Kfield := NumberField.of_module_finite B Kfield

theorem Kfield_unramified (h : sqrtBeta ∉ F1) : IsUnramifiedAtFinitePlacesOutside B Kfield S :=
  IsUnramifiedAtFinitePlacesOutside.congrTop K1equiv (K1_unramified h)

/-- Every `B`-conjugate of `√β₁` lies in `K`: it is `±√β₁` or `±√α₅/√β₁`. -/
theorem sigma_sqrtBeta_mem (σ : Closure ≃ₐ[B] Closure) : σ sqrtBeta ∈ Kfield := by
  have hr : σ baseRoot = baseRoot := by
    have h := σ.commutes sqrt241
    rwa [IntermediateField.algebraMap_apply, coe_sqrt241] at h
  have hγ : σ (genusRoot 3) = genusRoot 3 ∨ σ (genusRoot 3) = -genusRoot 3 := by
    apply sq_eq_sq_iff_eq_or_eq_neg.mp
    rw [← map_pow, genusRoot_sq_alpha, AlgEquiv.commutes]
  have hsq : σ sqrtBeta ^ 2 = σ beta := by rw [← map_pow, sqrtBeta_sq]
  have hK : sqrtBeta ∈ Kfield := sqrtBeta_mem_Kfield
  have h5 : genusRoot 5 ∈ Kfield := F1_le_Kfield genusRoot_five_mem_F1
  rcases hγ with hγ | hγ
  · have hb : σ beta = beta := by
      simp only [beta, map_add, map_sub, map_mul, map_neg, map_ofNat, hr, hγ]
    have h2 : σ sqrtBeta ^ 2 = sqrtBeta ^ 2 := by rw [hsq, hb, sqrtBeta_sq]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h | h <;> rw [h]
    · exact hK
    · exact neg_mem hK
  · have hb : σ beta = betaBar := by
      simp only [beta, betaBar, map_add, map_sub, map_mul, map_neg, map_ofNat, hr, hγ]
      ring
    have h2 : σ sqrtBeta ^ 2 = (genusRoot 5 / sqrtBeta) ^ 2 := by
      rw [hsq, hb, sq_genusRoot_div_sqrtBeta]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h | h <;> rw [h]
    · exact div_mem h5 hK
    · exact neg_mem (div_mem h5 hK)

instance Kfield_normal : Normal B Kfield := by
  rw [normal_iff_forall_map_le']
  intro σ
  have hgen : ∀ x ∈ ((F1 : Set Closure) ∪ {sqrtBeta}), σ x ∈ Kfield := by
    rintro x (hx | hx)
    · have hF : F1.map (σ : Closure →ₐ[B] Closure) ≤ F1 :=
        normal_iff_forall_map_le'.mp inferInstance σ
      exact F1_le_Kfield (hF ⟨x, hx, rfl⟩)
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact sigma_sqrtBeta_mem σ
  have hK := Kfield_eq
  rw [hK, IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
  rintro _ ⟨x, hx, rfl⟩
  have := hgen x hx
  rw [hK] at this
  exact this

instance Kfield_isGalois : IsGalois B Kfield where

theorem minpoly_sqrtBeta (h : sqrtBeta ∉ F1) :
    minpoly F1 sqrtBeta = X ^ 2 - C ((betaO : 𝓞 F1) : F1) := by
  symm
  apply minpoly.eq_of_irreducible_of_monic
  · exact X_pow_sub_C_irreducible_of_prime Nat.prime_two (nonsquare_beta h)
  · rw [map_sub, map_pow, aeval_X, aeval_C, IntermediateField.algebraMap_apply, coe_betaO,
      sqrtBeta_sq, sub_self]
  · exact monic_X_pow_sub_C _ (by norm_num)

theorem finrank_K1 (h : sqrtBeta ∉ F1) : Module.finrank F1 K1 = 2 := by
  rw [K1, IntermediateField.adjoin.finrank isIntegral_sqrtBeta, minpoly_sqrtBeta h,
    natDegree_X_pow_sub_C]

theorem finrank_Kfield (h : sqrtBeta ∉ F1) :
    Module.finrank B Kfield = Module.finrank B F1 * 2 := by
  rw [← K1equiv.toLinearEquiv.finrank_eq, ← Module.finrank_mul_finrank B F1 K1, finrank_K1 h]

theorem Kfield_isPGroup (h : sqrtBeta ∉ F1) : IsPGroup 2 (Kfield ≃ₐ[B] Kfield) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp F1_isPGroup
  apply IsPGroup.of_card (n := n + 1)
  rw [IsGalois.card_aut_eq_finrank, finrank_Kfield h, ← IsGalois.card_aut_eq_finrank B F1, hn,
    pow_succ]

/-! ### Conclusion -/

/-- **`√β₁ ∈ Ω`** (in the `B`-form `Ω = χ⁻¹(Ω_B)`). -/
theorem sqrtBeta_mem_OmegaBcl : sqrtBeta ∈ OmegaBcl := by
  by_cases h : sqrtBeta ∈ F1
  · exact F1_le_OmegaBcl h
  · exact le_OmegaBcl_of_admissible Kfield (Kfield_isPGroup h) (Kfield_unramified h)
      sqrtBeta_mem_Kfield

/-- **`√β₁ ∈ Ω`.** -/
theorem sqrtBeta_mem_Omega : sqrtBeta ∈ Omega := sqrtBeta_mem_OmegaBcl

end UnitDistance.Sqrt241.DyadicLink
