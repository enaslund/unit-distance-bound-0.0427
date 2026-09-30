module

public import UnitDistance.RelativeUnitsHilbert90
public import UnitDistance.RelativeDiscriminant
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.RingTheory.ClassGroup.ExtendedHom

@[expose] public section
set_option backward.privateInPublic true


/-! Unramified descent of invariant integral ideals, using actual prime orbits. -/

noncomputable section
open NumberField
open scoped nonZeroDivisors

namespace UnitDistance.RelativeUnits

variable {F K : Type} [Field F] [Field K] [NumberField F] [NumberField K]
  [Algebra F K] [IsGalois F K]

/-- The actual Galois action on integral ideals via restriction to integers. -/
def InvariantIdeal (I : Ideal (𝓞 K)) : Prop :=
  ∀ g : K ≃ₐ[F] K, Ideal.map (galRestrict (𝓞 F) F K (𝓞 K) g) I = I

omit [NumberField K] in
lemma invariantIdeal_comap (I : Ideal (𝓞 K)) (hI : InvariantIdeal (F := F) I)
    (g : K ≃ₐ[F] K) : Ideal.comap (galRestrict (𝓞 F) F K (𝓞 K) g) I = I := by
  calc
    Ideal.comap (galRestrict (𝓞 F) F K (𝓞 K) g) I =
        Ideal.comap (galRestrict (𝓞 F) F K (𝓞 K) g)
          (Ideal.map (galRestrict (𝓞 F) F K (𝓞 K) g) I) := by rw [hI g]
    _ = I := Ideal.comap_map_of_bijective _ (galRestrict (𝓞 F) F K (𝓞 K) g).bijective

omit [IsGalois F K] in
/-- In an unramified extension, the extension of a nonzero base prime is the
product of its distinct prime orbit, without any repeated ramification factors. -/
theorem map_prime_eq_product (hunr : NumberFieldAnalysis.FiniteUnramified F K)
    (p : Ideal (𝓞 F)) [p.IsMaximal] (hp : p ≠ ⊥) :
    Ideal.map (algebraMap (𝓞 F) (𝓞 K)) p = ∏ P ∈ p.primesOver (𝓞 K), P := by
  classical
  rw [Ideal.map_algebraMap_eq_finsetProd_pow hp]
  apply Finset.prod_congr rfl
  intro P hP
  have hP := Set.mem_toFinset.mp hP
  letI := hP.1
  letI := hP.2
  have hPm : P.IsMaximal := hP.1.isMaximal
    (Ideal.ne_bot_of_liesOver_of_ne_bot hp P)
  letI := hPm
  letI := hunr P hPm
  rw [Ideal.ramificationIdx_eq_one_of_isUnramifiedAt, pow_one]

/-- If an invariant ideal lies below one prime above `p`, it lies below the
extended ideal `p 𝓞_K`, using Galois transitivity and no finite ramification. -/
theorem invariant_le_extended_prime (hunr : NumberFieldAnalysis.FiniteUnramified F K)
    (I : Ideal (𝓞 K)) (hI : InvariantIdeal (F := F) I)
    (p : Ideal (𝓞 F)) [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal (𝓞 K)) (hP : P ∈ p.primesOver (𝓞 K)) (hIP : I ≤ P) :
    I ≤ Ideal.map (algebraMap (𝓞 F) (𝓞 K)) p := by
  classical
  rw [map_prime_eq_product hunr p hp, Ideal.prod_eq_iInf_of_pairwise_isCoprime]
  · refine le_iInf fun Q ↦ le_iInf fun hQ ↦ ?_
    have hQ := Set.mem_toFinset.mp hQ
    obtain ⟨g, hg⟩ := Ideal.exists_comap_galRestrict_eq (𝓞 F) F K (𝓞 K) hP hQ
    rw [← hg]
    exact (invariantIdeal_comap I hI g).symm.le.trans (Ideal.comap_mono hIP)
  · intro P₁ hP₁ P₂ hP₂ hne
    have hP₁ := Set.mem_toFinset.mp hP₁
    have hP₂ := Set.mem_toFinset.mp hP₂
    letI := hP₁.1
    letI := hP₁.2
    letI := hP₂.1
    letI := hP₂.2
    letI : P₁.IsMaximal := hP₁.1.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot hp P₁)
    letI : P₂.IsMaximal := hP₂.1.isMaximal (Ideal.ne_bot_of_liesOver_of_ne_bot hp P₂)
    exact Ideal.isCoprime_of_isMaximal hne

omit [NumberField K] in
/-- Every extended base ideal is fixed by the actual Galois action. -/
theorem extendedIdeal_invariant (a : Ideal (𝓞 F)) :
    InvariantIdeal (F := F) (Ideal.map (algebraMap (𝓞 F) (𝓞 K)) a) := by
  intro g
  change Ideal.map (galRestrict (𝓞 F) F K (𝓞 K) g).toRingEquiv.toRingHom
    (Ideal.map (algebraMap (𝓞 F) (𝓞 K)) a) = _
  rw [Ideal.map_map]
  congr 1
  exact (galRestrict (𝓞 F) F K (𝓞 K) g).toAlgHom.comp_algebraMap

/-- An invariant integral ideal descends in an everywhere finite-unramified
Galois extension. The proof removes one complete prime orbit at a time and
uses Noetherian induction; no ideal-descent premise is assumed. -/
theorem invariantIdeal_descends (hunr : NumberFieldAnalysis.FiniteUnramified F K)
    (I : Ideal (𝓞 K)) (hI : InvariantIdeal (F := F) I) :
    ∃ a : Ideal (𝓞 F), Ideal.map (algebraMap (𝓞 F) (𝓞 K)) a = I := by
  classical
  revert hI
  induction I using (wellFounded_gt (α := Ideal (𝓞 K))).induction with
  | h I ih =>
    intro hI
    by_cases hI0 : I = 0
    · exact ⟨0, by simpa using hI0.symm⟩
    by_cases hI1 : I = ⊤
    · exact ⟨⊤, (Ideal.map_top _).trans hI1.symm⟩
    obtain ⟨P, hPm, hIP⟩ := Ideal.exists_le_maximal I hI1
    letI := hPm
    have hP0 : P ≠ ⊥ := by
      intro hP
      exact hI0 (le_bot_iff.mp (hP ▸ hIP))
    let p := P.under (𝓞 F)
    have hp0 : p ≠ ⊥ := Ideal.under_ne_bot (𝓞 F) hP0
    letI : p.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal P
    have hPover : P ∈ p.primesOver (𝓞 K) := ⟨hPm.isPrime, inferInstance⟩
    let A := Ideal.map (algebraMap (𝓞 F) (𝓞 K)) p
    have hIA : I ≤ A := invariant_le_extended_prime hunr I hI p hp0 P hPover hIP
    have hA0 : A ≠ 0 := Ideal.map_ne_bot_of_ne_bot hp0
    have hA1 : A ≠ 1 := by
      intro hA
      have hAP : A ≤ P := Ideal.map_comap_le
      rw [hA, Ideal.one_eq_top] at hAP
      exact hPm.ne_top (top_unique hAP)
    obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hIA
    have hJ0 : J ≠ 0 := by
      intro h
      exact hI0 (by simpa [h] using hJ)
    have hIJ : I < J := by
      refine lt_of_le_of_ne (hJ ▸ Ideal.mul_le_right) ?_
      intro he
      apply hA1
      apply mul_right_cancel₀ hJ0
      simpa only [one_mul] using hJ.symm.trans he
    have hJinv : InvariantIdeal (F := F) J := by
      intro g
      have he := congrArg (Ideal.map (galRestrict (𝓞 F) F K (𝓞 K) g)) hJ
      rw [hI g, Ideal.map_mul, extendedIdeal_invariant p g] at he
      exact mul_left_cancel₀ hA0 (he.symm.trans hJ)
    obtain ⟨a, ha⟩ := ih J hIJ hJinv
    refine ⟨p * a, ?_⟩
    rw [Ideal.map_mul, ha]
    exact hJ.symm

/-- Exact characterization of descended integral ideals. -/
theorem invariantIdeal_iff_descends (hunr : NumberFieldAnalysis.FiniteUnramified F K)
    (I : Ideal (𝓞 K)) : InvariantIdeal (F := F) I ↔
      ∃ a : Ideal (𝓞 F), Ideal.map (algebraMap (𝓞 F) (𝓞 K)) a = I := by
  refine ⟨invariantIdeal_descends hunr I, ?_⟩
  rintro ⟨a, rfl⟩
  exact extendedIdeal_invariant a

omit [NumberField K] in
lemma galRestrict_eq_integerMap (g : K ≃ₐ[F] K) :
    (galRestrict (𝓞 F) F K (𝓞 K) g).toRingEquiv.toRingHom =
      RingOfIntegers.mapRingHom g.toRingHom := by
  ext x
  change algebraMap (𝓞 K) K (galRestrict (𝓞 F) F K (𝓞 K) g x) = g (x : K)
  exact algebraMap_galRestrict_apply (𝓞 F) g x

omit [IsGalois F K] in
/-- Extension of actual integral ideals is injective. -/
theorem extendedIdeal_injective :
    Function.Injective (Ideal.map (algebraMap (𝓞 F) (𝓞 K))) := by
  intro a b hab
  apply FractionalIdeal.coeIdeal_injective (K := F)
  apply FractionalIdeal.extendedHom_injective (𝓞 F) F K (𝓞 K)
  simpa only [FractionalIdeal.extendedHom_coeIdeal_eq_map] using
    congrArg (fun I : Ideal (𝓞 K) ↦ (I : FractionalIdeal (𝓞 K)⁰ K)) hab

/-- Invariant integral ideals descend uniquely. -/
theorem invariantIdeal_descends_unique (hunr : NumberFieldAnalysis.FiniteUnramified F K)
    (I : Ideal (𝓞 K)) (hI : InvariantIdeal (F := F) I) :
    ∃! a : Ideal (𝓞 F), Ideal.map (algebraMap (𝓞 F) (𝓞 K)) a = I := by
  obtain ⟨a, ha⟩ := invariantIdeal_descends hunr I hI
  exact ⟨a, ha, fun b hb ↦ extendedIdeal_injective (hb.trans ha.symm)⟩

variable [Algebra.IsQuadraticExtension F K]

/-- Every actual norm-one unit is represented by a nonzero principal ideal
extended from the base field. This proves the arithmetic surjectivity input
for the later capitulation/cohomology equivalence without assuming descent. -/
theorem normOneUnit_from_capitulating_ideal
    (hunr : NumberFieldAnalysis.FiniteUnramified F K)
    (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (u : (𝓞 K)ˣ)
    (hu : u ∈ normOneUnits (F := F)) :
    ∃ (a : Ideal (𝓞 F)) (x : 𝓞 K), a ≠ ⊥ ∧ x ≠ 0 ∧
      Ideal.map (algebraMap (𝓞 F) (𝓞 K)) a = Ideal.span {x} ∧
      (u : 𝓞 K) * RingOfIntegers.mapRingHom ι.toRingHom x = x := by
  obtain ⟨x, hx, he, hinv⟩ := exists_invariant_principal_ideal ι hι u hu
  have hI : InvariantIdeal (F := F) (Ideal.span {x}) := by
    intro g
    change Ideal.map (galRestrict (𝓞 F) F K (𝓞 K) g).toRingEquiv.toRingHom _ = _
    rw [galRestrict_eq_integerMap]
    rcases automorphism_eq_one_or ι hι g with hg | hg
    · rw [hg, Ideal.map_span, Set.image_singleton]
      rfl
    · rw [hg]
      exact hinv
  obtain ⟨a, ha⟩ := invariantIdeal_descends hunr (Ideal.span {x}) hI
  refine ⟨a, x, ?_, hx, ha, he⟩
  intro ha0
  rw [ha0, Ideal.map_bot] at ha
  exact hx (Ideal.span_singleton_eq_bot.mp ha.symm)

/-- A norm-one unit comes from a representative in the actual kernel of the
ordinary ideal-class extension homomorphism. -/
theorem normOneUnit_from_capitulation_kernel
    (hunr : NumberFieldAnalysis.FiniteUnramified F K)
    (ι : K ≃ₐ[F] K) (hι : ι ≠ 1) (u : (𝓞 K)ˣ)
    (hu : u ∈ normOneUnits (F := F)) :
    ∃ (a : (Ideal (𝓞 F))⁰) (x : 𝓞 K),
      ClassGroup.mk0 a ∈ (ClassGroup.extendedHom (𝓞 F) (𝓞 K)).ker ∧
      x ≠ 0 ∧ Ideal.map (algebraMap (𝓞 F) (𝓞 K)) a.val = Ideal.span {x} ∧
      (u : 𝓞 K) * RingOfIntegers.mapRingHom ι.toRingHom x = x := by
  obtain ⟨a, x, ha0, hx, ha, he⟩ := normOneUnit_from_capitulating_ideal hunr ι hι u hu
  let a₀ : (Ideal (𝓞 F))⁰ := ⟨a, mem_nonZeroDivisors_iff_ne_zero.mpr ha0⟩
  refine ⟨a₀, x, ?_, hx, ha, he⟩
  change ClassGroup.extendedHom (𝓞 F) (𝓞 K) (ClassGroup.mk0 a₀) = 1
  rw [ClassGroup.extendedHom_mk0]
  apply (ClassGroup.mk0_eq_one_iff _).mpr
  change (Ideal.map (algebraMap (𝓞 F) (𝓞 K)) a).IsPrincipal
  rw [ha]
  infer_instance

end UnitDistance.RelativeUnits
