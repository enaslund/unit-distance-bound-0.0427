module

public import UnitDistance.Sqrt241.CanonicalGenus
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.QuadraticFieldDiscriminant
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Data.Rat.Lemmas

@[expose] public section
set_option backward.privateInPublic true

/-!
# The base field `B = ℚ(√241)`

`B` is the intermediate field `ℚ⟮baseRoot⟯` of the fixed algebraic closure,
where `baseRoot = CanonicalGenus.baseRoot` is the chosen square root of `241`.
This module proves that `B` is a number field of degree two, Galois over `ℚ`
with nontrivial automorphism `σ : √241 ↦ -√241`, totally real, and gives the
rational coordinates, trace and norm of its elements and its two real
embeddings.
-/

noncomputable section

namespace UnitDistance.Sqrt241.Base

open CanonicalGenus IntermediateField Polynomial NumberField

/-- The base field `B = ℚ(√241)` inside the fixed algebraic closure. -/
abbrev B : IntermediateField ℚ Closure := ℚ⟮baseRoot⟯

/-- `241` is not the square of a rational number. -/
theorem not_isSquare_241 : ¬ IsSquare (241 : ℚ) := by
  rw [Rat.isSquare_ofNat_iff]
  rintro ⟨r, hr⟩
  have h1 : r ≤ 15 := by nlinarith
  interval_cases r <;> omega

theorem rat_sq_ne_241 (q : ℚ) : q ^ 2 ≠ 241 := by
  intro h
  exact not_isSquare_241 ⟨q, by rw [← h, sq]⟩

theorem isIntegral_baseRoot : IsIntegral ℚ baseRoot :=
  (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) baseRoot).isIntegral

theorem irreducible_X_sq_sub_241 : Irreducible (X ^ 2 - C (241 : ℚ)) :=
  X_pow_sub_C_irreducible_of_prime Nat.prime_two rat_sq_ne_241

theorem minpoly_baseRoot : minpoly ℚ baseRoot = X ^ 2 - C (241 : ℚ) := by
  symm
  apply minpoly.eq_of_irreducible_of_monic irreducible_X_sq_sub_241
  · simp only [map_sub, map_pow, aeval_X, baseRoot_sq, map_ofNat, sub_self]
  · exact monic_X_pow_sub_C _ (by decide)

instance finiteDimensional : FiniteDimensional ℚ B :=
  adjoin.finiteDimensional isIntegral_baseRoot

instance numberField : NumberField B where
  to_finiteDimensional := finiteDimensional

theorem finrank_eq_two : Module.finrank ℚ B = 2 := by
  rw [adjoin.finrank isIntegral_baseRoot, minpoly_baseRoot, natDegree_X_pow_sub_C]

instance isQuadraticExtension : Algebra.IsQuadraticExtension ℚ B :=
  ⟨finrank_eq_two⟩

instance isGalois : IsGalois ℚ B := inferInstance

theorem baseRoot_mem_B : baseRoot ∈ B := IntermediateField.mem_adjoin_simple_self ℚ baseRoot

/-- `B` is contained in the canonical genus field `E` of `CanonicalGenus`. -/
theorem B_le_field : B ≤ CanonicalGenus.field :=
  IntermediateField.adjoin_simple_le_iff.mpr CanonicalGenus.baseRoot_mem

/-- The generator `√241` of `B`. -/
def sqrt241 : B := AdjoinSimple.gen ℚ baseRoot

@[simp] theorem coe_sqrt241 : (sqrt241 : Closure) = baseRoot := rfl

theorem sqrt241_sq : sqrt241 ^ 2 = 241 := by
  apply Subtype.ext
  change baseRoot ^ 2 = ((241 : B) : Closure)
  rw [baseRoot_sq]
  rfl

theorem sqrt241_sq' : sqrt241 ^ 2 = algebraMap ℚ B 241 := by
  rw [sqrt241_sq, map_ofNat]

theorem sqrt241_mul_self : sqrt241 * sqrt241 = 241 := by
  rw [← sq, sqrt241_sq]

theorem adjoin_sqrt241_eq_top : IntermediateField.adjoin ℚ ({sqrt241} : Set B) = ⊤ := by
  apply (IntermediateField.adjoin_simple_eq_top_iff_of_isAlgebraic
    (IsAlgebraic.of_finite ℚ sqrt241)).mpr
  exact (adjoin.powerBasis isIntegral_baseRoot).adjoin_gen_eq_top

theorem minpoly_sqrt241 : minpoly ℚ sqrt241 = X ^ 2 - C (241 : ℚ) := by
  rw [sqrt241, minpoly_gen, minpoly_baseRoot]

theorem sqrt241_ne_zero : sqrt241 ≠ 0 := by
  intro h
  have := sqrt241_sq
  rw [h] at this
  norm_num at this

/-- Every element of `B` is `a + b√241` with rational `a`, `b`. -/
theorem exists_coords (x : B) :
    ∃ a b : ℚ, x = algebraMap ℚ B a + algebraMap ℚ B b * sqrt241 :=
  ClassFieldTower.Sawin.exists_rat_linear_combination_of_quadraticGenerator
    B sqrt241 adjoin_sqrt241_eq_top x

/-- The coordinates of an element in the basis `1, √241` are unique. -/
theorem coords_injective {a b c d : ℚ}
    (h : algebraMap ℚ B a + algebraMap ℚ B b * sqrt241 =
      algebraMap ℚ B c + algebraMap ℚ B d * sqrt241) : a = c ∧ b = d := by
  by_cases hbd : b = d
  · subst hbd
    exact ⟨(algebraMap ℚ B).injective (by simpa using h), rfl⟩
  · exfalso
    have hne : algebraMap ℚ B (b - d) ≠ 0 := (_root_.map_ne_zero _).mpr (sub_ne_zero.mpr hbd)
    have hmul : algebraMap ℚ B (b - d) * sqrt241 = algebraMap ℚ B (c - a) := by
      rw [map_sub, map_sub]
      linear_combination h
    have hs : sqrt241 = algebraMap ℚ B ((c - a) / (b - d)) := by
      rw [map_div₀, eq_div_iff hne, mul_comm, hmul]
    apply rat_sq_ne_241 ((c - a) / (b - d))
    apply (algebraMap ℚ B).injective
    rw [map_pow, ← hs, sqrt241_sq, map_ofNat]

/-- The trace of `a + b√241` is `2a`. -/
theorem trace_coords (a b : ℚ) :
    Algebra.trace ℚ B (algebraMap ℚ B a + algebraMap ℚ B b * sqrt241) = 2 * a :=
  ClassFieldTower.Sawin.trace_quadratic_coordinates B 241 a b sqrt241 sqrt241_sq'
    adjoin_sqrt241_eq_top

/-- The norm of `a + b√241` is `a² - 241 b²`. -/
theorem norm_coords (a b : ℚ) :
    Algebra.norm ℚ (algebraMap ℚ B a + algebraMap ℚ B b * sqrt241) = a ^ 2 - 241 * b ^ 2 :=
  ClassFieldTower.Sawin.norm_quadratic_coordinates B 241 a b sqrt241 sqrt241_sq'
    adjoin_sqrt241_eq_top

/-! ## The nontrivial automorphism -/

/-- The power basis `1, √241` of `B`. -/
abbrev powerBasis : PowerBasis ℚ B := adjoin.powerBasis isIntegral_baseRoot

@[simp] theorem powerBasis_gen : powerBasis.gen = sqrt241 := rfl

theorem aeval_neg_sqrt241 : aeval (-sqrt241) (minpoly ℚ powerBasis.gen) = 0 := by
  rw [powerBasis_gen, minpoly_sqrt241]
  simp [sqrt241_sq]

/-- The algebra endomorphism `√241 ↦ -√241`. -/
def sigmaHom : B →ₐ[ℚ] B := powerBasis.lift (-sqrt241) aeval_neg_sqrt241

/-- The nontrivial automorphism `σ : √241 ↦ -√241` of `B`. -/
def sigma : B ≃ₐ[ℚ] B :=
  AlgEquiv.ofBijective sigmaHom (Algebra.IsAlgebraic.algHom_bijective sigmaHom)

@[simp] theorem sigma_sqrt241 : sigma sqrt241 = -sqrt241 := by
  change sigmaHom powerBasis.gen = -sqrt241
  exact PowerBasis.lift_gen _ _ _

theorem sigma_coords (a b : ℚ) :
    sigma (algebraMap ℚ B a + algebraMap ℚ B b * sqrt241) =
      algebraMap ℚ B a - algebraMap ℚ B b * sqrt241 := by
  rw [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, sigma_sqrt241]
  ring

theorem sigma_sigma (x : B) : sigma (sigma x) = x := by
  obtain ⟨a, b, rfl⟩ := exists_coords x
  rw [sigma_coords, sub_eq_add_neg, ← neg_mul, ← map_neg, sigma_coords, map_neg]
  ring

theorem sigma_mul_self : sigma * sigma = 1 :=
  AlgEquiv.ext fun x ↦ by rw [AlgEquiv.mul_apply, sigma_sigma]; rfl

theorem sigma_ne_one : sigma ≠ 1 := by
  intro h
  have h1 : sigma sqrt241 = sqrt241 := by rw [h]; rfl
  rw [sigma_sqrt241] at h1
  have h2 : (2 : B) * sqrt241 = 0 := by linear_combination -h1
  rcases mul_eq_zero.mp h2 with h3 | h3
  · norm_num at h3
  · exact sqrt241_ne_zero h3

/-- Two algebra maps out of `B` agreeing on `√241` are equal. -/
theorem algHom_ext {A : Type*} [Ring A] [Algebra ℚ A] {f g : B →ₐ[ℚ] A}
    (h : f sqrt241 = g sqrt241) : f = g :=
  powerBasis.algHom_ext h

theorem algEquiv_eq_one_or_sigma (τ : B ≃ₐ[ℚ] B) : τ = 1 ∨ τ = sigma := by
  have hsq : τ sqrt241 ^ 2 = sqrt241 ^ 2 := by
    rw [← map_pow, sqrt241_sq, map_ofNat]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · left
    apply AlgEquiv.coe_toAlgHom_injective
    apply algHom_ext
    simpa using h
  · right
    apply AlgEquiv.coe_toAlgHom_injective
    apply algHom_ext
    simp [h]

/-- `x · σ(x)` is the norm of `x`. -/
theorem mul_sigma_eq_norm (x : B) : x * sigma x = algebraMap ℚ B (Algebra.norm ℚ x) := by
  obtain ⟨a, b, rfl⟩ := exists_coords x
  rw [sigma_coords, norm_coords]
  simp only [map_sub, map_mul, map_pow, map_ofNat]
  linear_combination (-(algebraMap ℚ B b) ^ 2) * sqrt241_sq

/-- `x + σ(x)` is the trace of `x`. -/
theorem add_sigma_eq_trace (x : B) : x + sigma x = algebraMap ℚ B (Algebra.trace ℚ B x) := by
  obtain ⟨a, b, rfl⟩ := exists_coords x
  rw [sigma_coords, trace_coords]
  simp only [map_mul, map_ofNat]
  ring

/-! ## Real embeddings -/

open scoped ComplexConjugate in
instance isTotallyReal : IsTotallyReal B := by
  refine ⟨fun w ↦ ?_⟩
  apply InfinitePlace.isReal_iff.mpr
  apply ComplexEmbedding.isReal_iff.mpr
  let φ : B →+* ℂ := w.embedding
  have hφsq : φ sqrt241 ^ 2 = ((Real.sqrt 241 : ℝ) : ℂ) ^ 2 := by
    rw [← map_pow, sqrt241_sq, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num), map_ofNat]
    norm_num
  have hreal : conj (φ sqrt241) = φ sqrt241 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hφsq with h | h
    · rw [h, Complex.conj_ofReal]
    · rw [h, map_neg, Complex.conj_ofReal]
  apply RingHom.ext
  intro x
  obtain ⟨a, b, rfl⟩ := exists_coords x
  change conj (φ _) = φ _
  simp only [map_add, map_mul, RingHom.map_rat_algebraMap, hreal]

theorem nrComplexPlaces_eq_zero : InfinitePlace.nrComplexPlaces B = 0 :=
  nrComplexPlaces_eq_zero_iff.mpr inferInstance

theorem nrRealPlaces_eq_two : InfinitePlace.nrRealPlaces B = 2 := by
  have h := InfinitePlace.card_add_two_mul_card_eq_rank B
  rw [nrComplexPlaces_eq_zero, finrank_eq_two] at h
  omega

theorem card_infinitePlace : Fintype.card (InfinitePlace B) = 2 := by
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, nrRealPlaces_eq_two,
    nrComplexPlaces_eq_zero]

theorem sqrt_241_sq : Real.sqrt 241 ^ 2 = 241 := Real.sq_sqrt (by norm_num)

theorem sqrt_241_pos : 0 < Real.sqrt 241 := Real.sqrt_pos.mpr (by norm_num)

theorem aeval_real_root {s : ℝ} (hs : s ^ 2 = 241) :
    aeval s (minpoly ℚ powerBasis.gen) = 0 := by
  rw [powerBasis_gen, minpoly_sqrt241]
  simp [hs]

/-- The real embedding `v₁ : √241 ↦ +√241` (PARI's first real place). -/
def embPlus : B →ₐ[ℚ] ℝ := powerBasis.lift (Real.sqrt 241) (aeval_real_root sqrt_241_sq)

/-- The real embedding `v₂ : √241 ↦ -√241`. -/
def embMinus : B →ₐ[ℚ] ℝ :=
  powerBasis.lift (-Real.sqrt 241) (aeval_real_root (by rw [neg_sq, sqrt_241_sq]))

@[simp] theorem embPlus_sqrt241 : embPlus sqrt241 = Real.sqrt 241 :=
  PowerBasis.lift_gen _ _ _

@[simp] theorem embMinus_sqrt241 : embMinus sqrt241 = -Real.sqrt 241 :=
  PowerBasis.lift_gen _ _ _

theorem embPlus_coords (a b : ℚ) :
    embPlus (algebraMap ℚ B a + algebraMap ℚ B b * sqrt241) = a + b * Real.sqrt 241 := by
  rw [map_add, map_mul, AlgHom.commutes, AlgHom.commutes, embPlus_sqrt241]
  simp

theorem embMinus_coords (a b : ℚ) :
    embMinus (algebraMap ℚ B a + algebraMap ℚ B b * sqrt241) = a - b * Real.sqrt 241 := by
  rw [map_add, map_mul, AlgHom.commutes, AlgHom.commutes, embMinus_sqrt241]
  simp only [eq_ratCast]
  ring

theorem embMinus_eq_comp_sigma : embMinus = embPlus.comp (sigma : B →ₐ[ℚ] B) :=
  algHom_ext (by simp)

theorem embMinus_apply (x : B) : embMinus x = embPlus (sigma x) := by
  rw [embMinus_eq_comp_sigma]
  rfl

theorem embPlus_ne_embMinus : embPlus ≠ embMinus := by
  intro h
  have h1 := congrArg (fun f : B →ₐ[ℚ] ℝ ↦ f sqrt241) h
  simp only [embPlus_sqrt241, embMinus_sqrt241] at h1
  linarith [sqrt_241_pos]

/-- Every algebra map `B → ℝ` is one of the two real embeddings. -/
theorem algHom_real_eq (f : B →ₐ[ℚ] ℝ) : f = embPlus ∨ f = embMinus := by
  have hsq : f sqrt241 ^ 2 = Real.sqrt 241 ^ 2 := by
    rw [← map_pow, sqrt241_sq, map_ofNat, sqrt_241_sq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact Or.inl (algHom_ext (by rw [h, embPlus_sqrt241]))
  · exact Or.inr (algHom_ext (by rw [h, embMinus_sqrt241]))

/-- Every ring homomorphism `B → ℝ` is one of the two real embeddings. -/
theorem ringHom_real_eq (f : B →+* ℝ) :
    f = (embPlus : B →+* ℝ) ∨ f = (embMinus : B →+* ℝ) := by
  rcases algHom_real_eq f.toRatAlgHom with h | h
  · left
    ext x
    exact congrArg (fun g : B →ₐ[ℚ] ℝ ↦ g x) h
  · right
    ext x
    exact congrArg (fun g : B →ₐ[ℚ] ℝ ↦ g x) h

/-- The complex embedding underlying `embPlus`. -/
def complexEmbPlus : B →+* ℂ := Complex.ofRealHom.comp (embPlus : B →+* ℝ)

/-- The complex embedding underlying `embMinus`. -/
def complexEmbMinus : B →+* ℂ := Complex.ofRealHom.comp (embMinus : B →+* ℝ)

/-- The real place `v₁` of `B` (`√241 ↦ +√241`). -/
def placePlus : InfinitePlace B := InfinitePlace.mk complexEmbPlus

/-- The real place `v₂` of `B` (`√241 ↦ -√241`). -/
def placeMinus : InfinitePlace B := InfinitePlace.mk complexEmbMinus

theorem complexEmbPlus_isReal : ComplexEmbedding.IsReal complexEmbPlus :=
  ComplexEmbedding.isReal_iff.mpr (RingHom.ext fun _ ↦ Complex.conj_ofReal _)

theorem complexEmbMinus_isReal : ComplexEmbedding.IsReal complexEmbMinus :=
  ComplexEmbedding.isReal_iff.mpr (RingHom.ext fun _ ↦ Complex.conj_ofReal _)

theorem placePlus_ne_placeMinus : placePlus ≠ placeMinus := by
  intro h
  rcases InfinitePlace.mk_eq_iff.mp h with h1 | h1
  · have h2 := RingHom.congr_fun h1 sqrt241
    simp only [complexEmbPlus, complexEmbMinus, RingHom.coe_comp, Function.comp_apply,
      AlgHom.coe_toRingHom, embPlus_sqrt241, embMinus_sqrt241, Complex.ofRealHom_eq_coe] at h2
    rw [Complex.ofReal_inj] at h2
    linarith [sqrt_241_pos]
  · rw [ComplexEmbedding.isReal_iff.mp complexEmbPlus_isReal] at h1
    have h2 := RingHom.congr_fun h1 sqrt241
    simp only [complexEmbPlus, complexEmbMinus, RingHom.coe_comp, Function.comp_apply,
      AlgHom.coe_toRingHom, embPlus_sqrt241, embMinus_sqrt241, Complex.ofRealHom_eq_coe] at h2
    rw [Complex.ofReal_inj] at h2
    linarith [sqrt_241_pos]

/-- The two infinite places of `B` are `v₁` and `v₂`. -/
theorem infinitePlace_eq (w : InfinitePlace B) : w = placePlus ∨ w = placeMinus := by
  have hw : ComplexEmbedding.IsReal w.embedding :=
    InfinitePlace.isReal_iff.mp (IsTotallyReal.isReal w)
  have hφ : w.embedding = Complex.ofRealHom.comp hw.embedding := by
    ext x
    simp
  rcases ringHom_real_eq hw.embedding with h | h
  · left
    rw [← InfinitePlace.mk_embedding w, hφ, h]
    rfl
  · right
    rw [← InfinitePlace.mk_embedding w, hφ, h]
    rfl

end UnitDistance.Sqrt241.Base
