module

public import UnitDistance.GaloisConjugationFixedField
public import UnitDistance.Sqrt241.Witness
public import Mathlib.FieldTheory.PrimitiveElement
public import UnitDistance.RelativeArithmeticAmplitude
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# The signature of a conjugation-fixed field through a Galois subfield

Version 1 bounds the real places of `F = K^c` by the centralizer of `c` in `Gal(K/ℚ)`,
which needs `K` Galois over `ℚ`. Here `K` is any totally complex number field with a
nontrivial automorphism `c` that is the complex conjugation of an embedding `φ`, and `D`
is a subfield of `K` (through `algebraMap D K`) that is Galois over `ℚ`, on which `c`
restricts to `cD`. Then

* `2 · r₁(F)` is the number of embeddings `ψ : K → ℂ` whose complex conjugation is `c`
  (`two_mul_nrRealPlaces_eq_card_isConj`);
* restriction to `D` maps these to embeddings with complex conjugation `cD`, each of which
  has exactly `[K:D]` extensions to `K` (`card_extensions`);
* since `D` is Galois over `ℚ`, the embeddings of `D` with complex conjugation `cD` are
  the translates of one of them by the centralizer of `cD` (`card_isConj_galois`).

Hence `r₁(F) · [Gal(D/ℚ) : C(cD)] ≤ [F:ℚ]` (`nrRealPlaces_mul_index_le`), and an index of
at least `2^16` gives `Witness.thetaMin ≤ signatureRatio F` (`thetaMin_le_signatureRatio`).
-/

noncomputable section

open NumberField NumberField.ComplexEmbedding NumberField.InfinitePlace Module

namespace UnitDistance.Sqrt241.V2

/-! ### Extensions of an embedding -/

section Extensions

variable {D K : Type*} [Field D] [Field K] [NumberField D] [NumberField K] [Algebra D K]

/-- The embeddings of `K` that extend a given embedding of `D` correspond to the
`D`-algebra maps `K → ℂ` for the `D`-algebra structure of `ℂ` given by the embedding. -/
def extensionsEquiv (χ : D →+* ℂ) :
    letI : Algebra D ℂ := χ.toAlgebra
    {ψ : K →+* ℂ // ψ.comp (algebraMap D K) = χ} ≃ (K →ₐ[D] ℂ) :=
  letI : Algebra D ℂ := χ.toAlgebra
  { toFun := fun ψ =>
      { ψ.1 with
        commutes' := fun r => by
          change ψ.1 (algebraMap D K r) = χ r
          exact RingHom.congr_fun ψ.2 r }
    invFun := fun f => ⟨f.toRingHom, by
      ext r
      exact f.commutes r⟩
    left_inv := fun ψ => rfl
    right_inv := fun f => rfl }

/-- An embedding of `D` has exactly `[K:D]` extensions to `K`. -/
theorem card_extensions [FiniteDimensional D K] (χ : D →+* ℂ) :
    Nat.card {ψ : K →+* ℂ // ψ.comp (algebraMap D K) = χ} = finrank D K := by
  letI : Algebra D ℂ := χ.toAlgebra
  rw [Nat.card_congr (extensionsEquiv χ), Nat.card_eq_fintype_card, AlgHom.card]

end Extensions

/-! ### Embeddings whose complex conjugation is `c` -/

section Conj

variable {K : Type*} [Field K] [NumberField K]

/-- An embedding whose complex conjugation is a nontrivial automorphism is not real. -/
theorem not_isReal_of_isConj {ψ : K →+* ℂ} {c : K ≃ₐ[ℚ] K} (hc : IsConj ψ c) (hc1 : c ≠ 1) :
    ¬ IsReal ψ := by
  intro hr
  apply hc1
  ext x
  apply ψ.injective
  have h := hc.eq x
  have hx : star (ψ x) = ψ x := RingHom.congr_fun hr x
  change ψ (c x) = ψ x
  rw [h]
  exact hx

/-- Each embedding of the fixed field extends to exactly two embeddings of `K`. -/
theorem card_fixedField_extensions {φ : K →+* ℂ} {c : K ≃ₐ[ℚ] K} (hc : IsConj φ c)
    (hc1 : c ≠ 1) (χ : GaloisConjugation.fixedField K c →+* ℂ) :
    Nat.card {ψ : K →+* ℂ //
        ψ.comp (algebraMap (GaloisConjugation.fixedField K c) K) = χ} = 2 := by
  rw [card_extensions, GaloisConjugation.relativeDegree_eq_two φ c hc hc1]

/-- In a totally complex field, an embedding whose restriction to the fixed field of `c`
is real has complex conjugation `c`. -/
theorem isConj_of_isReal_restriction [IsTotallyComplex K] {φ : K →+* ℂ}
    {c : K ≃ₐ[ℚ] K} (hc : IsConj φ c) (hc1 : c ≠ 1) (ψ : K →+* ℂ)
    (hψ : IsReal (ψ.comp (algebraMap (GaloisConjugation.fixedField K c) K))) :
    IsConj ψ c := by
  classical
  set F := GaloisConjugation.fixedField K c
  -- `conj ∘ ψ` extends the same (real) embedding of `F`.
  have hext : (ComplexEmbedding.conjugate ψ).comp (algebraMap F K) = ψ.comp (algebraMap F K) := by
    ext x
    exact RingHom.congr_fun hψ x
  -- The two extensions of `ψ|F` are `ψ` and `ψ ∘ c`.
  have hc' : (ψ.comp c.toRingHom).comp (algebraMap F K) = ψ.comp (algebraMap F K) := by
    ext x
    change ψ (c (x : K)) = ψ (x : K)
    rw [GaloisConjugation.generator_fixes c x]
  have hne1 : ComplexEmbedding.conjugate ψ ≠ ψ := by
    intro h
    have hr : ComplexEmbedding.IsReal ψ := h
    exact (InfinitePlace.not_isReal_iff_isComplex.mpr
      (IsTotallyComplex.isComplex (InfinitePlace.mk ψ))) (InfinitePlace.isReal_mk_iff.mpr hr)
  have hne2 : ψ.comp c.toRingHom ≠ ψ := by
    intro h
    apply hc1
    ext x
    exact ψ.injective (RingHom.congr_fun h x)
  -- Three extensions `ψ`, `ψ ∘ c`, `conj ∘ ψ` of a two-element fiber: two coincide.
  have hcard := card_fixedField_extensions hc hc1 (ψ.comp (algebraMap F K))
  let a : {θ : K →+* ℂ // θ.comp (algebraMap F K) = ψ.comp (algebraMap F K)} := ⟨ψ, rfl⟩
  let b : {θ : K →+* ℂ // θ.comp (algebraMap F K) = ψ.comp (algebraMap F K)} := ⟨_, hc'⟩
  let d : {θ : K →+* ℂ // θ.comp (algebraMap F K) = ψ.comp (algebraMap F K)} := ⟨_, hext⟩
  have hab : a ≠ b := fun h => hne2 (congrArg Subtype.val h).symm
  have had : a ≠ d := fun h => hne1 (congrArg Subtype.val h).symm
  have hbd : b = d := by
    by_contra hbd
    have : 3 ≤ Nat.card {θ : K →+* ℂ // θ.comp (algebraMap F K) = ψ.comp (algebraMap F K)} := by
      have hfin : Finite {θ : K →+* ℂ // θ.comp (algebraMap F K) = ψ.comp (algebraMap F K)} :=
        Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
      haveI := Fintype.ofFinite {θ : K →+* ℂ // θ.comp (algebraMap F K) = ψ.comp (algebraMap F K)}
      rw [Nat.card_eq_fintype_card]
      have hsub : ({a, b, d} : Finset _).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hab, had]), Finset.card_pair hbd]
      rw [← hsub]
      exact Finset.card_le_univ _
    have h2 : Nat.card {θ : K →+* ℂ // θ.comp (algebraMap F K) = ψ.comp (algebraMap F K)} = 2 :=
      hcard
    rw [h2] at this
    norm_num at this
  -- `conj ∘ ψ = ψ ∘ c`.
  have h := congrArg Subtype.val hbd
  change ψ.comp c.toRingHom = ComplexEmbedding.conjugate ψ at h
  exact h.symm

end Conj

/-! ### Counting -/

section Count

variable {K : Type} [Field K] [NumberField K]

/-- An embedding has at most one complex conjugation. -/
theorem isConj_unique {ψ : K →+* ℂ} {a b : K ≃ₐ[ℚ] K} (ha : IsConj ψ a) (hb : IsConj ψ b) :
    a = b := by
  ext x
  apply ψ.injective
  rw [ha.eq, hb.eq]

/-- `2 r₁(K^c)` is the number of embeddings of `K` whose complex conjugation is `c`. -/
theorem two_mul_nrRealPlaces_eq_card_isConj [IsTotallyComplex K] {φ : K →+* ℂ}
    {c : K ≃ₐ[ℚ] K} (hc : IsConj φ c) (hc1 : c ≠ 1) :
    2 * nrRealPlaces (GaloisConjugation.fixedField K c) =
      Nat.card {ψ : K →+* ℂ // IsConj ψ c} := by
  classical
  set F := GaloisConjugation.fixedField K c
  let r : (K →+* ℂ) → (F →+* ℂ) := fun ψ => ψ.comp (algebraMap F K)
  have hreal : ∀ ψ : K →+* ℂ, IsConj ψ c ↔ ComplexEmbedding.IsReal (r ψ) := fun ψ =>
    ⟨fun h => GaloisConjugation.isReal_restriction ψ c h,
     fun h => isConj_of_isReal_restriction hc hc1 ψ h⟩
  let e := Equiv.sigmaSubtypeFiberEquivSubtype r hreal
  have hfiber : ∀ χ : {χ : F →+* ℂ // ComplexEmbedding.IsReal χ},
      Fintype.card {ψ : K →+* ℂ // r ψ = χ.1} = 2 := by
    intro χ
    rw [← Nat.card_eq_fintype_card]
    exact card_fixedField_extensions hc hc1 χ.1
  rw [Nat.card_eq_fintype_card, ← Fintype.card_congr e, Fintype.card_sigma]
  simp_rw [hfiber]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, InfinitePlace.card_real_embeddings,
    mul_comm]

/-- Restricting to `D`: at most `[K:D]` embeddings of `K` with complex conjugation `c` lie
over each embedding of `D` with complex conjugation `cD`. -/
theorem card_isConj_le {D : Type} [Field D] [NumberField D] [Algebra D K]
    {c : K ≃ₐ[ℚ] K} {cD : D ≃ₐ[ℚ] D}
    (hcD : ∀ x : D, c (algebraMap D K x) = algebraMap D K (cD x)) :
    Nat.card {ψ : K →+* ℂ // IsConj ψ c} ≤
      finrank D K * Nat.card {χ : D →+* ℂ // IsConj χ cD} := by
  classical
  haveI : FiniteDimensional D K := Module.Finite.of_restrictScalars_finite ℚ D K
  let r : {ψ : K →+* ℂ // IsConj ψ c} → {χ : D →+* ℂ // IsConj χ cD} := fun ψ =>
    ⟨ψ.1.comp (algebraMap D K), by
      ext x
      change star (ψ.1 (algebraMap D K x)) = ψ.1 (algebraMap D K (cD x))
      rw [← hcD, ψ.2.eq]⟩
  haveI := Fintype.ofFinite {ψ : K →+* ℂ // IsConj ψ c}
  haveI := Fintype.ofFinite {χ : D →+* ℂ // IsConj χ cD}
  have hfib : ∀ χ, Fintype.card {ψ // r ψ = χ} ≤ finrank D K := by
    intro χ
    rw [← card_extensions (K := K) χ.1, ← Nat.card_eq_fintype_card]
    apply Nat.card_le_card_of_injective
      (fun ψ : {ψ // r ψ = χ} => (⟨ψ.1.1, congrArg Subtype.val ψ.2⟩ :
        {θ : K →+* ℂ // θ.comp (algebraMap D K) = χ.1}))
    intro a b h
    have h' : a.1.1 = b.1.1 := by simpa using congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  calc Fintype.card {ψ : K →+* ℂ // IsConj ψ c}
      = ∑ χ, Fintype.card {ψ // r ψ = χ} := by
        rw [← Fintype.card_sigma]
        exact Fintype.card_congr (Equiv.sigmaFiberEquiv r).symm
    _ ≤ ∑ _χ : {χ : D →+* ℂ // IsConj χ cD}, finrank D K :=
        Finset.sum_le_sum fun χ _ => hfib χ
    _ = finrank D K * Fintype.card {χ : D →+* ℂ // IsConj χ cD} := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]

/-- For `D` Galois over `ℚ`, the embeddings of `D` with complex conjugation `cD` are at most
as many as the elements of the centralizer of `cD`. -/
theorem card_isConj_le_centralizer {D : Type} [Field D] [NumberField D] [IsGalois ℚ D]
    {cD : D ≃ₐ[ℚ] D} {χ0 : D →+* ℂ} (hχ0 : IsConj χ0 cD) :
    Nat.card {χ : D →+* ℂ // IsConj χ cD} ≤
      Nat.card (Subgroup.centralizer ({cD} : Set (D ≃ₐ[ℚ] D))) := by
  classical
  have hex : ∀ χ : {χ : D →+* ℂ // IsConj χ cD}, ∃ σ : D ≃ₐ[ℚ] D, χ0.comp σ.symm = χ.1 :=
    fun χ => NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq χ0 χ.1 (RingHom.ext_rat _ _)
  choose σ hσ using hex
  have hmem : ∀ χ, σ χ ∈ Subgroup.centralizer ({cD} : Set (D ≃ₐ[ℚ] D)) := by
    intro χ
    have h1 : IsConj (χ0.comp (σ χ).symm) ((σ χ).symm⁻¹ * cD * (σ χ).symm) := hχ0.comp _
    rw [hσ χ] at h1
    have h2 := isConj_unique h1 χ.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h3 : (σ χ) * cD * (σ χ)⁻¹ = cD := by
      simpa [AlgEquiv.aut_inv] using h2
    calc (σ χ) * cD = ((σ χ) * cD * (σ χ)⁻¹) * (σ χ) := by group
      _ = cD * (σ χ) := by rw [h3]
  apply Nat.card_le_card_of_injective (fun χ => (⟨σ χ, hmem χ⟩ :
    Subgroup.centralizer ({cD} : Set (D ≃ₐ[ℚ] D))))
  intro a b h
  have h' : σ a = σ b := congrArg Subtype.val h
  apply Subtype.ext
  rw [← hσ a, ← hσ b, h']

/-- **The real places of `K^c` through `D`**: `r₁(K^c) · [Gal(D/ℚ) : C(cD)] ≤ [K^c : ℚ]`. -/
theorem nrRealPlaces_mul_index_le [IsTotallyComplex K] {D : Type} [Field D] [NumberField D]
    [IsGalois ℚ D] [Algebra D K] {φ : K →+* ℂ} {c : K ≃ₐ[ℚ] K} (hc : IsConj φ c) (hc1 : c ≠ 1)
    {cD : D ≃ₐ[ℚ] D} (hcD : ∀ x : D, c (algebraMap D K x) = algebraMap D K (cD x)) :
    nrRealPlaces (GaloisConjugation.fixedField K c) *
        (Subgroup.centralizer ({cD} : Set (D ≃ₐ[ℚ] D))).index ≤
      finrank ℚ (GaloisConjugation.fixedField K c) := by
  classical
  set C := Subgroup.centralizer ({cD} : Set (D ≃ₐ[ℚ] D))
  have hχ0 : IsConj (φ.comp (algebraMap D K)) cD := by
    ext x
    change star (φ (algebraMap D K x)) = φ (algebraMap D K (cD x))
    rw [← hcD, hc.eq]
  have h1 := two_mul_nrRealPlaces_eq_card_isConj hc hc1
  have h2 := card_isConj_le (K := K) hcD
  have h3 := card_isConj_le_centralizer hχ0
  have h4 : Nat.card C * C.index = finrank ℚ D := by
    rw [Subgroup.card_mul_index, ← IsGalois.card_aut_eq_finrank ℚ D]
  have h5 : finrank ℚ D * finrank D K = finrank ℚ K := Module.finrank_mul_finrank ℚ D K
  have h6 := GaloisConjugation.absoluteDegree_eq_two_mul φ c hc hc1
  -- 2 r₁ · index ≤ [K:D] · |C| · index = [K:ℚ] = 2 [F:ℚ]
  have h7 : 2 * nrRealPlaces (GaloisConjugation.fixedField K c) * C.index ≤
      finrank D K * Nat.card C * C.index := by
    apply Nat.mul_le_mul_right
    rw [h1]
    exact h2.trans (Nat.mul_le_mul_left _ h3)
  have h8 : finrank D K * Nat.card C * C.index = 2 * finrank ℚ (GaloisConjugation.fixedField K c) := by
    rw [mul_assoc, h4, mul_comm, h5, h6]
  have h9 : 2 * (nrRealPlaces (GaloisConjugation.fixedField K c) * C.index) ≤
      2 * finrank ℚ (GaloisConjugation.fixedField K c) := by
    rw [← mul_assoc, ← h8]
    exact h7
  exact Nat.le_of_mul_le_mul_left h9 (by norm_num)

/-- **Signature bound** from a centralizer index of at least `2^16` in `Gal(D/ℚ)`. -/
theorem thetaMin_le_signatureRatio [IsTotallyComplex K] {D : Type} [Field D] [NumberField D]
    [IsGalois ℚ D] [Algebra D K] {φ : K →+* ℂ} {c : K ≃ₐ[ℚ] K} (hc : IsConj φ c) (hc1 : c ≠ 1)
    {cD : D ≃ₐ[ℚ] D} (hcD : ∀ x : D, c (algebraMap D K x) = algebraMap D K (cD x))
    (hindex : 65536 ≤ (Subgroup.centralizer ({cD} : Set (D ≃ₐ[ℚ] D))).index) :
    Witness.thetaMin ≤ UnitDistance.RelativeUnits.signatureRatio (GaloisConjugation.fixedField K c) := by
  set F := GaloisConjugation.fixedField K c
  have hle := nrRealPlaces_mul_index_le hc hc1 hcD
  have hr : (nrRealPlaces F : ℝ) * 65536 ≤ finrank ℚ F := by
    have : nrRealPlaces F * 65536 ≤ finrank ℚ F :=
      (Nat.mul_le_mul_left _ hindex).trans hle
    exact_mod_cast this
  have hsig : (nrRealPlaces F : ℝ) + 2 * nrComplexPlaces F = finrank ℚ F := by
    exact_mod_cast InfinitePlace.card_add_two_mul_card_eq_rank F
  have hd : (0 : ℝ) < finrank ℚ F := by exact_mod_cast Module.finrank_pos (R := ℚ) (M := F)
  rw [UnitDistance.RelativeUnits.signatureRatio, Witness.thetaMin, le_div_iff₀ hd]
  nlinarith

end Count

end UnitDistance.Sqrt241.V2
