/-
Generic quadratic characters `Gal(F̄/F) → ℤ/2` attached to square roots, over an
arbitrary number field `F`. The character construction and its inertia lemma are
copied (generic, private upstream) from Naganori Yamaguchi's
SawinTotallyRealTowers/NegativeThreeCharacter.lean, and the quadratic subfield
from SawinTotallyRealTowers/QuadraticClosure.lean (ℚ only upstream), commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4 (Apache-2.0). The real-place value
`sqrtCharacter_infinite_eq_one_iff` is new.
-/
module

public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.NegativeThreeCharacter
public import UnitDistance.QuadraticRamification

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Quadratic characters of square roots over a number field

For a nonsquare `a ∈ F`, `sqrtField a ha = F(√a)` inside `AlgebraicClosure F`
and `sqrtCharacter a ha : Gal(F̄/F) →ₜ* ℤ/2` is its character:
* `sqrtCharacter_eq_one_iff`: `σ ↦ 1` iff `σ` fixes the chosen `√a`;
* `sqrtCharacter_inertia`: for integral `a` it kills absolute inertia at every
  finite place not containing `2a`;
* `sqrtCharacter_infinite_eq_one_iff`: at a real place `v`, its value on the
  real Artin element `absoluteInfinitePlaceArtinNegOne F v` is trivial iff `a`
  is positive at `v`.
-/

open scoped NumberField
open NumberField IsDedekindDomain Polynomial

noncomputable section

namespace UnitDistance.Sqrt241.Relation

open ClassFieldTower.Sawin ClassFieldTower.Martinet.Shafarevich
open GlobalClassFieldTheory.Reciprocity AlgebraicNumberTheory.Valuations

section QuadraticCharacter

/-- The coordinate of a quadratic Galois group. -/
def quadraticCharacterCoordinate (F : Type) [Field F]
    (E : FiniteGaloisIntermediateField F (AlgebraicClosure F))
    (hd : Module.finrank F E = 2) :
    Gal(E/F) ≃* Multiplicative (ZMod 2) := by
  apply mulEquivOfPrimeCardEq (p := 2)
  · exact (IsGalois.card_aut_eq_finrank F E).trans hd
  · change Nat.card (ZMod 2) = 2
    exact Nat.card_zmod 2

/-- The continuous quadratic character cut out by a quadratic subfield. -/
def quadraticAbsoluteCharacter (F : Type) [Field F]
    (E : FiniteGaloisIntermediateField F (AlgebraicClosure F))
    (hd : Module.finrank F E = 2) :
    Field.absoluteGaloisGroup F →ₜ* Multiplicative (ZMod 2) := by
  let e := quadraticCharacterCoordinate F E hd
  let r : Field.absoluteGaloisGroup F →ₜ* Gal(E/F) :=
    { toMonoidHom := AlgEquiv.restrictNormalHom (F := F) (K₁ := AlgebraicClosure F)
        E.toIntermediateField
      continuous_toFun := InfiniteGalois.restrictNormalHom_continuous E.toIntermediateField }
  have he : Continuous e := continuous_of_discreteTopology
  exact
    { toMonoidHom := e.toMonoidHom.comp r.toMonoidHom
      continuous_toFun := he.comp r.continuous_toFun }

theorem quadraticAbsoluteCharacter_eq_one_iff (F : Type) [Field F]
    (E : FiniteGaloisIntermediateField F (AlgebraicClosure F))
    (hd : Module.finrank F E = 2) (σ : Field.absoluteGaloisGroup F) :
    quadraticAbsoluteCharacter F E hd σ = 1 ↔
      AlgEquiv.restrictNormalHom (F := F) (K₁ := AlgebraicClosure F) E.toIntermediateField σ =
        1 := by
  change quadraticCharacterCoordinate F E hd (AlgEquiv.restrictNormalHom (F := F)
    (K₁ := AlgebraicClosure F) E.toIntermediateField σ) = 1 ↔ _
  exact (quadraticCharacterCoordinate F E hd).map_eq_one_iff

theorem quadraticAbsoluteCharacter_inertia
    (F : Type) [Field F] [NumberField F]
    (E : FiniteGaloisIntermediateField F (AlgebraicClosure F)) [NumberField E]
    (hd : Module.finrank F E = 2) (T : Set (HeightOneSpectrum (𝓞 F)))
    (hUnramified : IsUnramifiedAtFinitePlacesOutside F E T)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ T)
    (σ : finitePlaceAbsoluteInertiaSubgroup F v) :
    quadraticAbsoluteCharacter F E hd
      (finitePlaceAbsoluteDecompositionInclusion F v
        (finitePlaceAbsoluteInertiaInclusion F v σ)) = 1 := by
  apply (quadraticAbsoluteCharacter_eq_one_iff F E hd _).mpr
  let w := restrictAbsoluteValueExtensionToIntermediate
    (HeightOneSpectrum.adicAbv F v) (finitePlaceAbsoluteValueExtension F v)
      E.toIntermediateField
  let P := finitePlaceExtensionCentre (K := F) (L := E) v w
  have hP : Algebra.IsUnramifiedAt (𝓞 F) P.asIdeal := by
    apply hUnramified P
    rw [finitePlaceBelow_finitePlaceExtensionCentre v w]
    exact hv
  have hmem : (σ.1.1 : Gal(AlgebraicClosure F/F)).restrictNormal E ∈
      HilbertRamification.Dedekind.inertiaGroup P.asIdeal Gal(E/F) :=
    finitePlaceAbsoluteInertia_restrictNormal_mem_finiteInertia F E.toIntermediateField v σ
  have hbot : HilbertRamification.Dedekind.inertiaGroup P.asIdeal Gal(E/F) = ⊥ :=
    HilbertRamification.Dedekind.inertiaGroup_eq_bot_of_isUnramifiedAt P.asIdeal hP
  have hRestricted : (σ.1.1 : Gal(AlgebraicClosure F/F)).restrictNormal E = 1 := by
    simpa only [hbot, Subgroup.mem_bot] using hmem
  rw [finitePlaceAbsoluteInertiaInclusion_apply, finitePlaceAbsoluteDecompositionInclusion_apply]
  change (σ.1.1 : Gal(AlgebraicClosure F/F)).restrictNormal E.toIntermediateField = 1
  exact hRestricted

end QuadraticCharacter

section SqrtField

variable {F : Type} [Field F]

/-- A chosen square root of `a` in `AlgebraicClosure F`. -/
def sqrtRoot (a : F) : AlgebraicClosure F :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq
    (algebraMap F (AlgebraicClosure F) a) (by decide : 0 < 2))

theorem sqrtRoot_sq (a : F) :
    sqrtRoot a ^ 2 = algebraMap F (AlgebraicClosure F) a :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq
    (algebraMap F (AlgebraicClosure F) a) (by decide : 0 < 2))

theorem sqrtRoot_isIntegral (a : F) : IsIntegral F (sqrtRoot a) := by
  refine ⟨X ^ 2 - C a, monic_X_pow_sub_C a (by decide : (2 : ℕ) ≠ 0), ?_⟩
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sqrtRoot_sq, sub_self]

theorem minpoly_sqrtRoot (a : F) (ha : ¬ IsSquare a) :
    minpoly F (sqrtRoot a) = X ^ 2 - C a := by
  apply Eq.symm
  apply minpoly.eq_of_irreducible_of_monic
  · apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
    intro b hb
    exact ha ((isSquare_iff_exists_sq a).mpr ⟨b, hb.symm⟩)
  · rw [map_sub, map_pow, aeval_X, aeval_C, sqrtRoot_sq, sub_self]
  · exact monic_X_pow_sub_C a (by decide : (2 : ℕ) ≠ 0)

theorem finrank_adjoin_sqrtRoot (a : F) (ha : ¬ IsSquare a) :
    Module.finrank F
      (IntermediateField.adjoin F ({sqrtRoot a} : Set (AlgebraicClosure F))) = 2 := by
  rw [IntermediateField.adjoin.finrank (sqrtRoot_isIntegral a),
    minpoly_sqrtRoot a ha, natDegree_X_pow_sub_C]

variable [NumberField F]

/-- The quadratic Galois subfield `F(√a)` of `AlgebraicClosure F`. -/
def sqrtField (a : F) (ha : ¬ IsSquare a) :
    FiniteGaloisIntermediateField F (AlgebraicClosure F) where
  toIntermediateField := IntermediateField.adjoin F {sqrtRoot a}
  finiteDimensional := IntermediateField.adjoin.finiteDimensional (sqrtRoot_isIntegral a)
  isGalois := by
    let : Algebra.IsQuadraticExtension F
        (IntermediateField.adjoin F ({sqrtRoot a} : Set (AlgebraicClosure F))) :=
      { finrank_eq_two' := finrank_adjoin_sqrtRoot a ha }
    exact Algebra.IsQuadraticExtension.isGalois F
      (IntermediateField.adjoin F ({sqrtRoot a} : Set (AlgebraicClosure F)))

theorem sqrtField_finrank (a : F) (ha : ¬ IsSquare a) :
    Module.finrank F (sqrtField a ha) = 2 :=
  finrank_adjoin_sqrtRoot a ha

instance sqrtField_numberField (a : F) (ha : ¬ IsSquare a) : NumberField (sqrtField a ha) :=
  NumberField.of_module_finite F (sqrtField a ha)

theorem sqrtRoot_mem (a : F) (ha : ¬ IsSquare a) :
    sqrtRoot a ∈ (sqrtField a ha).toIntermediateField :=
  IntermediateField.mem_adjoin_simple_self F (sqrtRoot a)

/-- The chosen square root inside its quadratic field. -/
def sqrtGenerator (a : F) (ha : ¬ IsSquare a) : sqrtField a ha :=
  ⟨sqrtRoot a, sqrtRoot_mem a ha⟩

theorem sqrtGenerator_sq (a : F) (ha : ¬ IsSquare a) :
    sqrtGenerator a ha ^ 2 = algebraMap F (sqrtField a ha) a := by
  apply (algebraMap (sqrtField a ha) (AlgebraicClosure F)).injective
  rw [map_pow, ← IsScalarTower.algebraMap_apply F (sqrtField a ha) (AlgebraicClosure F)]
  exact sqrtRoot_sq a

theorem sqrtGenerator_algebra_adjoin (a : F) (ha : ¬ IsSquare a) :
    Algebra.adjoin F ({(sqrtGenerator a ha : sqrtField a ha)} : Set (sqrtField a ha)) = ⊤ := by
  have h := (IntermediateField.adjoin.powerBasis (sqrtRoot_isIntegral a)).adjoin_gen_eq_top
  rw [IntermediateField.adjoin.powerBasis_gen] at h
  exact h

/-- The quadratic character of `F(√a)`. -/
def sqrtCharacter (a : F) (ha : ¬ IsSquare a) :
    Field.absoluteGaloisGroup F →ₜ* Multiplicative (ZMod 2) :=
  quadraticAbsoluteCharacter F (sqrtField a ha) (sqrtField_finrank a ha)

/-- The character is trivial exactly on the automorphisms fixing `√a`. -/
theorem sqrtCharacter_eq_one_iff (a : F) (ha : ¬ IsSquare a)
    (σ : Field.absoluteGaloisGroup F) :
    sqrtCharacter a ha σ = 1 ↔
      absoluteGaloisGroupContinuousMulEquiv F σ (sqrtRoot a) = sqrtRoot a := by
  rw [sqrtCharacter, quadraticAbsoluteCharacter_eq_one_iff]
  let E := (sqrtField a ha).toIntermediateField
  have hNormal : Normal F E := (sqrtField a ha).isGalois.to_normal
  constructor
  · intro h
    have hc := AlgEquiv.restrictNormal_commutes
      (absoluteGaloisGroupContinuousMulEquiv F σ) E (sqrtGenerator a ha)
    change algebraMap E (AlgebraicClosure F)
        ((AlgEquiv.restrictNormalHom (F := F) (K₁ := AlgebraicClosure F) E σ)
          (sqrtGenerator a ha)) = absoluteGaloisGroupContinuousMulEquiv F σ (sqrtRoot a) at hc
    rw [h] at hc
    exact hc.symm
  · intro h
    let s : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F := absoluteGaloisGroupContinuousMulEquiv F σ
    have hs : s (sqrtRoot a) = sqrtRoot a := h
    have hle : E ≤ IntermediateField.fixedField (Subgroup.zpowers s) := by
      change IntermediateField.adjoin F {sqrtRoot a} ≤ _
      rw [IntermediateField.adjoin_simple_le_iff]
      rintro ⟨τ, n, rfl⟩
      change (s ^ n) (sqrtRoot a) = sqrtRoot a
      induction n using Int.induction_on with
      | zero => rfl
      | succ k ih =>
        rw [zpow_add_one, AlgEquiv.mul_apply, hs, ih]
      | pred k ih =>
        rw [zpow_sub_one, AlgEquiv.mul_apply]
        have hinv : s⁻¹ (sqrtRoot a) = sqrtRoot a := by
          rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq, hs]
        rw [hinv, ih]
    have hfix : s ∈ E.fixingSubgroup :=
      ((IntermediateField.le_iff_le _ _).mp hle) (Subgroup.mem_zpowers s)
    rw [← IntermediateField.restrictNormalHom_ker E] at hfix
    exact hfix

/-- For an integral radicand, the quadratic field is unramified at every finite
place not containing `2a`. -/
theorem sqrtField_unramified (a : 𝓞 F) (ha : ¬ IsSquare (a : F)) :
    IsUnramifiedAtFinitePlacesOutside F (sqrtField (a : F) ha)
      {v : HeightOneSpectrum (𝓞 F) | 2 * a ∈ v.asIdeal} := by
  intro P hP
  let E := sqrtField (a : F) ha
  let x : 𝓞 E := ⟨sqrtGenerator (a : F) ha, by
    apply IsIntegral.of_pow (n := 2) (by decide)
    rw [sqrtGenerator_sq]
    exact map_isIntegral_int (algebraMap F E) a.property⟩
  have hx : x ^ 2 = algebraMap (𝓞 F) (𝓞 E) a := by
    apply RingOfIntegers.coe_injective
    change (sqrtGenerator (a : F) ha) ^ 2 = algebraMap F E (a : F)
    exact sqrtGenerator_sq (a : F) ha
  have hna : KummerInvariant.Nonsquare (a : F) := by
    intro s hs
    exact ha ⟨s, hs.symm.trans (sq s)⟩
  apply QuadraticRamification.isUnramifiedAt_of_not_mem_two_mul F E a hna x hx
    (sqrtGenerator_algebra_adjoin (a : F) ha) P.asIdeal
  intro hmem
  apply hP
  change 2 * a ∈ (finitePlaceBelow (K := F) P).asIdeal
  rw [finitePlaceBelow_asIdeal]
  exact hmem

/-- For an integral radicand, the character kills absolute inertia at every
finite place not containing `2a`. -/
theorem sqrtCharacter_inertia (a : 𝓞 F) (ha : ¬ IsSquare (a : F))
    (v : HeightOneSpectrum (𝓞 F)) (hv : 2 * a ∉ v.asIdeal)
    (σ : finitePlaceAbsoluteInertiaSubgroup F v) :
    sqrtCharacter (a : F) ha (finitePlaceAbsoluteDecompositionInclusion F v σ.1) = 1 :=
  quadraticAbsoluteCharacter_inertia F (sqrtField (a : F) ha) (sqrtField_finrank (a : F) ha)
    _ (sqrtField_unramified a ha) v hv σ

end SqrtField

section Infinite

variable {F : Type} [Field F] [NumberField F]

/-- The complex embedding of `AlgebraicClosure F` at the chosen place above `v`. -/
theorem chosenAbove_embedding_algebraMap (v : InfinitePlace F) (hv : v.IsReal) (x : F) :
    (chosenInfinitePlaceAbove (L := AlgebraicClosure F) v).embedding
        (algebraMap F (AlgebraicClosure F) x) =
      ((InfinitePlace.embedding_of_isReal hv x : ℝ) : ℂ) := by
  let W : InfinitePlace (AlgebraicClosure F) :=
    chosenInfinitePlaceAbove (L := AlgebraicClosure F) v
  let φ : F →+* ℂ := W.embedding.comp (algebraMap F (AlgebraicClosure F))
  have hφ : InfinitePlace.mk φ = v := by
    rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
    exact chosenInfinitePlaceAbove_comap (L := AlgebraicClosure F) v
  have hreal : ComplexEmbedding.IsReal φ := by
    apply InfinitePlace.isReal_of_mk_isReal
    rw [hφ]
    exact hv
  have hemb : v.embedding = φ := by
    rw [← hφ]
    exact InfinitePlace.embedding_mk_eq_of_isReal hreal
  rw [InfinitePlace.embedding_of_isReal_apply, hemb]
  rfl

theorem algebraicClosure_chosenAbove_isRamified (v : InfinitePlace F) (hv : v.IsReal) :
    (chosenInfinitePlaceAbove (L := AlgebraicClosure F) v).IsRamified F := by
  have hcomplex : (chosenInfinitePlaceAbove (L := AlgebraicClosure F) v).IsComplex := by
    apply InfinitePlace.not_isReal_iff_isComplex.mp
    intro hw
    let rho : AlgebraicClosure F →+* ℝ := (InfinitePlace.isReal_iff.mp hw).embedding
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : AlgebraicClosure F)
      (by decide : 0 < 2)
    have h : rho z ^ 2 = (-1 : ℝ) := by
      rw [← map_pow, hz, map_neg, map_one]
    have hn : 0 ≤ rho z ^ 2 := sq_nonneg (rho z)
    linarith
  refine InfinitePlace.isRamified_iff.mpr ⟨hcomplex, ?_⟩
  rw [chosenInfinitePlaceAbove_comap]
  exact hv

/-- At a real place, the real Artin element fixes `√a` iff `a` is positive there. -/
theorem sqrtCharacter_infinite_eq_one_iff (a : F) (ha : ¬ IsSquare a)
    (v : InfinitePlace F) (hv : v.IsReal) :
    sqrtCharacter a ha (absoluteInfinitePlaceArtinNegOne F v) = 1 ↔
      0 < InfinitePlace.embedding_of_isReal hv a := by
  rw [sqrtCharacter_eq_one_iff]
  let W : InfinitePlace (AlgebraicClosure F) :=
    chosenInfinitePlaceAbove (L := AlgebraicClosure F) v
  let c : Gal(AlgebraicClosure F/F) :=
    chosenInfinitePlaceArtinMonoidHom (K := F) (L := AlgebraicClosure F) v (-1 : v.Completionˣ)
  have hConj : ComplexEmbedding.IsConj W.embedding c :=
    chosenInfinitePlaceArtinMonoidHom_neg_one_isConj_of_ramified
      (K := F) (L := AlgebraicClosure F) v (algebraicClosure_chosenAbove_isRamified v hv)
  change c (sqrtRoot a) = sqrtRoot a ↔ _
  let z : ℂ := W.embedding (sqrtRoot a)
  let r : ℝ := InfinitePlace.embedding_of_isReal hv a
  have hz : z ^ 2 = (r : ℂ) := by
    change (W.embedding (sqrtRoot a)) ^ 2 = _
    rw [← map_pow, sqrtRoot_sq, chosenAbove_embedding_algebraMap v hv]
  have hcz : W.embedding (c (sqrtRoot a)) = star z := by
    rw [← hConj.eq]
  have hr0 : r ≠ 0 := by
    intro h0
    apply ha
    have : a = 0 := (InfinitePlace.embedding_of_isReal hv).injective (by
      change r = _
      rw [h0, map_zero])
    rw [this]
    exact ⟨0, by ring⟩
  have hre : z.re ^ 2 - z.im ^ 2 = r ∧ 2 * z.re * z.im = 0 := by
    have h1 := congrArg Complex.re hz
    have h2 := congrArg Complex.im hz
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im] at h1 h2
    constructor <;> nlinarith
  constructor
  · intro hfix
    have hstar : star z = z := by
      rw [← hcz, hfix]
    have him : z.im = 0 := by
      have := congrArg Complex.im hstar
      simp only [Complex.star_def, Complex.conj_im] at this
      linarith
    rw [him] at hre
    rcases lt_or_gt_of_ne hr0 with hneg | hpos
    · nlinarith [sq_nonneg z.re, hre.1]
    · exact hpos
  · intro hpos
    have him : z.im = 0 := by
      rcases mul_eq_zero.mp hre.2 with h | h
      · have hre0 : z.re = 0 := by linarith
        rw [hre0] at hre
        nlinarith [sq_nonneg z.im, hre.1]
      · exact h
    have hstar : star z = z := by
      apply Complex.ext
      · simp
      · simp only [Complex.star_def, Complex.conj_im]
        rw [him]
        simp
    apply W.embedding.injective
    rw [hcz, hstar]

end Infinite

end UnitDistance.Sqrt241.Relation
