module

public import UnitDistance.QuadraticSevenField
public import UnitDistance.GaloisConjugationFixedField

@[expose] public section
set_option backward.privateInPublic true


/-! A displayed square root of seven lies in the actual conjugation fixed field. -/
noncomputable section
namespace UnitDistance.QuadraticSeven
open NumberField NumberField.ComplexEmbedding

 theorem complex_im_eq_zero_of_sq_eq_seven (z : ℂ) (hz : z^2=7) : z.im=0 := by
  have hre : z.re^2-z.im^2=7 := by
    have h := congrArg Complex.re hz
    simpa [pow_two,Complex.mul_re] using h
  have him : z.re*z.im=0 := by
    have h := congrArg Complex.im hz
    simp [pow_two,Complex.mul_im] at h
    linarith
  rcases mul_eq_zero.mp him with h | h
  · rw [h] at hre
    nlinarith [sq_nonneg z.im]
  · exact h

 theorem conjugation_fixes_root {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) (c : Gal(K/ℚ)) (hc : IsConj φ c)
    (r : K) (hr : r^2=7) : c r=r := by
  apply φ.injective
  rw [hc.eq]
  have hz : (φ r)^2=7 := by simpa only [map_pow,map_ofNat] using congrArg φ hr
  have him := complex_im_eq_zero_of_sq_eq_seven (φ r) hz
  apply Complex.ext <;> simp [him]

 theorem root_mem_fixedField {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) (c : Gal(K/ℚ)) (hc : IsConj φ c)
    (r : K) (hr : r^2=7) : r ∈ GaloisConjugation.fixedField K c := by
  apply (IntermediateField.mem_fixedField_iff _ _).mpr
  have hle : Subgroup.zpowers c ≤ MulAction.stabilizer Gal(K/ℚ) r :=
    Subgroup.zpowers_le.mpr (conjugation_fixes_root φ c hc r hr)
  intro g hg
  exact hle hg

/-- The actual displayed root in the actual fixed field. -/
def fixedRoot {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) (c : Gal(K/ℚ)) (hc : IsConj φ c)
    (r : K) (hr : r^2=7) : GaloisConjugation.fixedField K c :=
  ⟨r,root_mem_fixedField φ c hc r hr⟩

 theorem fixedRoot_sq {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) (c : Gal(K/ℚ)) (hc : IsConj φ c)
    (r : K) (hr : r^2=7) : (fixedRoot φ c hc r hr)^2=7 := by
  apply Subtype.ext
  exact hr

/-- Actual rational-algebra inclusion of Q(sqrt7) into the conjugation fixed field. -/
def embedding_fixedField {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) (c : Gal(K/ℚ)) (hc : IsConj φ c)
    (r : K) (hr : r^2=7) : SevenField →ₐ[ℚ] GaloisConjugation.fixedField K c :=
  embedding (fixedRoot φ c hc r hr) (fixedRoot_sq φ c hc r hr)

end UnitDistance.QuadraticSeven
