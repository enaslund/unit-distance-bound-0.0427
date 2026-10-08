module

public import UnitDistance.Sqrt241.DyadicLink.Radical

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Square roots of `S`-units of an admissible layer lie in `Ω`

Generalization of `DyadicLink/Radical.lean`. Let `F/B` be a finite Galois 2-extension inside the
closure, unramified outside `S` and contained in `Ω`, and let `β ∈ 𝓞 F` with

* `β X = m` for some `X ∈ 𝓞 F` and an integer `m` all of whose prime divisors divide `30`
  (so `β` is an `S`-unit), and
* `σ(β) = u_σ² β` with `u_σ ∈ F` for every `B`-automorphism `σ` of the closure.

Then `F(√β)/B` is a finite Galois 2-extension unramified outside `S`, so `√β ∈ Ω`
(`squareRoot_mem_OmegaBcl`). The genus field over `B` (`genusB`, the compositum of the eight
`quadField k`) is such an `F`.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace UnitDistance.Sqrt241.Wide

open Tower Base CanonicalGenus IntermediateField ClassFieldTower.Sawin Polynomial
open DyadicLink (isUnramifiedAtFinitePlacesOutside_trans)

/-! ### Admissible layers inside the closure -/

/-- A finite Galois 2-extension of `B` in the closure, unramified outside `S`, inside `Ω`. -/
structure Admissible (E : IntermediateField B Closure) : Prop where
  finite : FiniteDimensional B E
  galois : IsGalois B E
  pgroup : IsPGroup 2 (E ≃ₐ[B] E)
  unramified : letI := finite; letI : NumberField E := NumberField.of_module_finite B E
    IsUnramifiedAtFinitePlacesOutside B E S
  le_Omega : E ≤ OmegaBcl

theorem Admissible.sup {E₁ E₂ : IntermediateField B Closure} (h₁ : Admissible E₁)
    (h₂ : Admissible E₂) : Admissible (E₁ ⊔ E₂) := by
  haveI := h₁.finite
  haveI := h₂.finite
  haveI := h₁.galois
  haveI := h₂.galois
  haveI : NumberField E₁ := NumberField.of_module_finite B E₁
  haveI : NumberField E₂ := NumberField.of_module_finite B E₂
  refine ⟨inferInstance, inferInstance, isPGroup_galois_sup E₁ E₂ h₁.pgroup h₂.pgroup, ?_,
    sup_le h₁.le_Omega h₂.le_Omega⟩
  exact IsUnramifiedAtFinitePlacesOutside.sup E₁ E₂ S h₁.unramified h₂.unramified

theorem admissible_quadField (k : Fin 8) : Admissible (quadField k) :=
  ⟨inferInstance, inferInstance, quadField_isPGroup k, quadField_unramified k,
    quadField_le_OmegaBcl k⟩

/-- The genus field over `B`: the compositum of the eight quadratic fields `B(√α_k)`. -/
def genusB : IntermediateField B Closure :=
  quadField 0 ⊔ quadField 1 ⊔ quadField 2 ⊔ quadField 3 ⊔ quadField 4 ⊔ quadField 5 ⊔
    quadField 6 ⊔ quadField 7

set_option maxHeartbeats 2000000 in
theorem admissible_genusB : Admissible genusB := by
  have h1 := (admissible_quadField 0).sup (admissible_quadField 1)
  have h2 := h1.sup (admissible_quadField 2)
  have h3 := h2.sup (admissible_quadField 3)
  have h4 := h3.sup (admissible_quadField 4)
  have h5 := h4.sup (admissible_quadField 5)
  have h6 := h5.sup (admissible_quadField 6)
  exact h6.sup (admissible_quadField 7)

instance genusB_finiteDimensional : FiniteDimensional B genusB := admissible_genusB.finite
instance genusB_isGalois : IsGalois B genusB := admissible_genusB.galois
instance genusB_numberField : NumberField genusB := NumberField.of_module_finite B genusB

theorem quadField_le_genusB : ∀ k : Fin 8, quadField k ≤ genusB
  | 0 => le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
      (le_sup_of_le_left (le_sup_of_le_left le_sup_left)))))
  | 1 => le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
      (le_sup_of_le_left (le_sup_of_le_left le_sup_right)))))
  | 2 => le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
      (le_sup_of_le_left le_sup_right))))
  | 3 => le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
      le_sup_right)))
  | 4 => le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_right))
  | 5 => le_sup_of_le_left (le_sup_of_le_left le_sup_right)
  | 6 => le_sup_of_le_left le_sup_right
  | 7 => le_sup_right

theorem genusRoot_mem_genusB (k : Fin 8) : genusRoot k ∈ genusB :=
  quadField_le_genusB k (genusRoot_mem_quadField k)

theorem baseRoot_mem_genusB : baseRoot ∈ genusB := by
  have h : algebraMap B Closure sqrt241 ∈ genusB := genusB.algebraMap_mem sqrt241
  exact h

/-! ### The Kummer step over an admissible layer -/

section Generic

variable (F : IntermediateField B Closure) [FiniteDimensional B F] [IsGalois B F]

/-- The square-root extension `F(t)` over `F`. -/
def kummer (t : Closure) : IntermediateField F Closure := IntermediateField.adjoin F {t}

theorem isIntegral_over (t : Closure) : IsIntegral F t :=
  (Algebra.IsIntegral.isIntegral (R := B) t).tower_top

instance kummer_finiteDimensional (t : Closure) : FiniteDimensional F (kummer F t) :=
  IntermediateField.adjoin.finiteDimensional (isIntegral_over F t)

/-- `F(t)` as an intermediate field over `B`. -/
def kummerB (t : Closure) : IntermediateField B Closure := (kummer F t).restrictScalars B

theorem kummerB_eq (t : Closure) :
    kummerB F t = IntermediateField.adjoin B ((F : Set Closure) ∪ {t}) :=
  IntermediateField.restrictScalars_adjoin B F {t}

theorem mem_kummerB {t x : Closure} : x ∈ kummerB F t ↔ x ∈ kummer F t :=
  IntermediateField.mem_restrictScalars B

theorem le_kummerB (t : Closure) : F ≤ kummerB F t := by
  rw [kummerB_eq]
  exact fun x hx => IntermediateField.subset_adjoin B _ (Or.inl hx)

theorem self_mem_kummerB (t : Closure) : t ∈ kummerB F t :=
  (mem_kummerB F).mpr (IntermediateField.mem_adjoin_simple_self F t)

/-- `F(t)` over `F` and over `B` are the same field. -/
def kummerEquiv (t : Closure) : kummer F t ≃ₐ[B] kummerB F t where
  toFun x := ⟨x.1, (mem_kummerB F).mpr x.2⟩
  invFun x := ⟨x.1, (mem_kummerB F).mp x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

instance kummer_finiteDimensional_B (t : Closure) : FiniteDimensional B (kummer F t) :=
  FiniteDimensional.trans B F (kummer F t)

instance kummerB_finiteDimensional (t : Closure) : FiniteDimensional B (kummerB F t) :=
  (kummerEquiv F t).toLinearEquiv.finiteDimensional

/-- If every `B`-conjugate of `t` lies in `F(t)`, then `F(t)/B` is normal. -/
theorem kummerB_normal (t : Closure) (ht : ∀ σ : Closure ≃ₐ[B] Closure, σ t ∈ kummerB F t) :
    Normal B (kummerB F t) := by
  rw [normal_iff_forall_map_le']
  intro σ
  have hgen : ∀ x ∈ ((F : Set Closure) ∪ {t}), σ x ∈ kummerB F t := by
    rintro x (hx | hx)
    · have hF : F.map (σ : Closure →ₐ[B] Closure) ≤ F :=
        normal_iff_forall_map_le'.mp inferInstance σ
      exact le_kummerB F t (hF ⟨x, hx, rfl⟩)
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact ht σ
  have hK := kummerB_eq F t
  rw [hK, IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
  rintro _ ⟨x, hx, rfl⟩
  have := hgen x hx
  rw [hK] at this
  exact this

variable [NumberField F]

instance kummer_numberField (t : Closure) : NumberField (kummer F t) :=
  NumberField.of_module_finite F (kummer F t)

instance kummerB_numberField (t : Closure) : NumberField (kummerB F t) :=
  NumberField.of_module_finite B (kummerB F t)

/-- **Square roots of `S`-units.** -/
theorem squareRoot_mem_OmegaBcl (hF : Admissible F) (β cof : 𝓞 F) (m : ℤ)
    (hm : β * cof = (m : 𝓞 F))
    (hm30 : ∀ P : Ideal ℤ, P.IsPrime → m ∈ P → (30 : ℤ) ∈ P)
    (hconj : ∀ σ : Closure ≃ₐ[B] Closure,
      ∃ u ∈ F, σ ((β : F) : Closure) = u ^ 2 * ((β : F) : Closure)) :
    squareRoot ((β : F) : Closure) ∈ OmegaBcl := by
  set t : Closure := squareRoot ((β : F) : Closure) with ht_def
  have ht : t ^ 2 = ((β : F) : Closure) := squareRoot_sq _
  by_cases hmem : t ∈ F
  · exact hF.le_Omega hmem
  -- `β` is not a square in `F`
  have hns : KummerInvariant.Nonsquare ((β : 𝓞 F) : F) := by
    intro u hu
    apply hmem
    have hu' : (u : Closure) ^ 2 = t ^ 2 := by
      rw [ht, ← hu]
      rfl
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hu' with h1 | h1
    · rw [← h1]
      exact u.2
    · rw [← neg_neg t, ← h1]
      exact neg_mem u.2
  -- the generator of `F(t)` as an algebraic integer
  let tK : kummer F t := AdjoinSimple.gen F t
  have coe_tK : (tK : Closure) = t := AdjoinSimple.coe_gen F t
  have tK_sq : tK ^ 2 = algebraMap F (kummer F t) ((β : 𝓞 F) : F) := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, coe_tK, IntermediateField.coe_algebraMap_apply,
      IntermediateField.algebraMap_apply, ht]
  let tO : 𝓞 (kummer F t) :=
    ⟨tK, by
      apply IsIntegral.of_pow (n := 2) (by norm_num)
      rw [tK_sq]
      exact ((β : 𝓞 F).2).map (IsScalarTower.toAlgHom ℤ F (kummer F t))⟩
  have tO_sq : tO ^ 2 = algebraMap (𝓞 F) (𝓞 (kummer F t)) β := by
    apply RingOfIntegers.ext
    rw [RingOfIntegers.coe_eq_algebraMap, map_pow, ← RingOfIntegers.coe_eq_algebraMap]
    change tK ^ 2 = _
    rw [tK_sq, RingOfIntegers.coe_eq_algebraMap, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (𝓞 F) F (kummer F t)]
    rfl
  have tO_adjoin : Algebra.adjoin F {((tO : 𝓞 (kummer F t)) : kummer F t)} = ⊤ := by
    change Algebra.adjoin F {tK} = ⊤
    exact (IntermediateField.adjoin.powerBasis (isIntegral_over F t)).adjoin_gen_eq_top
  -- Kummer step
  have hstep : ∀ P : HeightOneSpectrum (𝓞 (kummer F t)), finitePlaceBelow (K := B) P ∉ S →
      Algebra.IsUnramifiedAt (𝓞 F) P.asIdeal := by
    intro P hP
    have h30 : (30 : 𝓞 B) ∉ P.asIdeal.under (𝓞 B) := hP
    have h30K : (30 : 𝓞 (kummer F t)) ∉ P.asIdeal := by
      intro h
      apply h30
      rw [Ideal.mem_under, map_ofNat]
      exact h
    apply QuadraticRamification.isUnramifiedAt_of_not_mem F (kummer F t) β hns tO tO_sq
      tO_adjoin P.asIdeal
    · intro h2
      apply h30K
      have h15 : (30 : 𝓞 (kummer F t)) = 15 * 2 := by norm_num
      rw [h15]
      exact P.asIdeal.mul_mem_left 15 h2
    · intro hb
      apply h30K
      have hmK : ((m : ℤ) : 𝓞 (kummer F t)) ∈ P.asIdeal := by
        have he : ((m : ℤ) : 𝓞 (kummer F t)) =
            algebraMap (𝓞 F) (𝓞 (kummer F t)) β * algebraMap (𝓞 F) (𝓞 (kummer F t)) cof := by
          rw [← map_mul, hm, map_intCast]
        rw [he]
        exact P.asIdeal.mul_mem_right _ hb
      let Q : Ideal ℤ := P.asIdeal.comap (algebraMap ℤ (𝓞 (kummer F t)))
      have hQ : Q.IsPrime := Ideal.comap_isPrime _ _
      have hmQ : m ∈ Q := by
        change algebraMap ℤ (𝓞 (kummer F t)) m ∈ P.asIdeal
        rwa [eq_intCast]
      have h30Q := hm30 Q hQ hmQ
      change algebraMap ℤ (𝓞 (kummer F t)) 30 ∈ P.asIdeal at h30Q
      simpa using h30Q
  have hunr : IsUnramifiedAtFinitePlacesOutside B (kummer F t) S :=
    isUnramifiedAtFinitePlacesOutside_trans hF.unramified hstep
  have hunrB : IsUnramifiedAtFinitePlacesOutside B (kummerB F t) S :=
    IsUnramifiedAtFinitePlacesOutside.congrTop (kummerEquiv F t) hunr
  -- conjugates
  have hconjK : ∀ σ : Closure ≃ₐ[B] Closure, σ t ∈ kummerB F t := by
    intro σ
    obtain ⟨u, hu, hσ⟩ := hconj σ
    have h2 : σ t ^ 2 = (u * t) ^ 2 := by rw [← map_pow, ht, hσ, mul_pow, ht]
    have huK : u * t ∈ kummerB F t := mul_mem (le_kummerB F t hu) (self_mem_kummerB F t)
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h | h <;> rw [h]
    · exact huK
    · exact neg_mem huK
  haveI : Normal B (kummerB F t) := kummerB_normal F t hconjK
  haveI : IsGalois B (kummerB F t) := ⟨⟩
  -- degree
  have hmin : minpoly F t = X ^ 2 - C ((β : 𝓞 F) : F) := by
    symm
    apply minpoly.eq_of_irreducible_of_monic
    · exact X_pow_sub_C_irreducible_of_prime Nat.prime_two hns
    · rw [map_sub, map_pow, aeval_X, aeval_C, IntermediateField.algebraMap_apply, ht, sub_self]
    · exact monic_X_pow_sub_C _ (by norm_num)
  have hfin : Module.finrank F (kummer F t) = 2 := by
    rw [kummer, IntermediateField.adjoin.finrank (isIntegral_over F t), hmin, natDegree_X_pow_sub_C]
  have hfinB : Module.finrank B (kummerB F t) = Module.finrank B F * 2 := by
    rw [← (kummerEquiv F t).toLinearEquiv.finrank_eq, ← Module.finrank_mul_finrank B F (kummer F t),
      hfin]
  have hp : IsPGroup 2 (kummerB F t ≃ₐ[B] kummerB F t) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hF.pgroup
    apply IsPGroup.of_card (n := n + 1)
    rw [IsGalois.card_aut_eq_finrank, hfinB, ← IsGalois.card_aut_eq_finrank B F, hn, pow_succ]
  exact le_OmegaBcl_of_admissible (kummerB F t) hp hunrB (self_mem_kummerB F t)

end Generic

end UnitDistance.Sqrt241.Wide
