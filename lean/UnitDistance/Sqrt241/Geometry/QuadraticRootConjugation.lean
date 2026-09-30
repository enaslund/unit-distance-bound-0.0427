module

public import UnitDistance.Sqrt241.Geometry.QuadraticRootField
public import UnitDistance.QuadraticSevenConjugation

@[expose] public section
set_option backward.privateInPublic true


/-!
# A displayed square root of `d` lies in the conjugation fixed field

Copy of `UnitDistance.QuadraticSevenConjugation` for an admissible radicand
`d` in place of `7`: a square root of the positive rational `d` is fixed by
every complex conjugation.
-/

noncomputable section
set_option autoImplicit false
namespace UnitDistance.Sqrt241.QuadraticRoot
open NumberField NumberField.ComplexEmbedding

theorem complex_im_eq_zero_of_sq_eq_natCast (d : ℕ) (z : ℂ) (hz : z^2=(d : ℂ)) : z.im=0 := by
  have hre : z.re^2-z.im^2=(d : ℝ) := by
    have h := congrArg Complex.re hz
    simpa [pow_two,Complex.mul_re] using h
  have him : z.re*z.im=0 := by
    have h := congrArg Complex.im hz
    simp [pow_two,Complex.mul_im] at h
    linarith
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  rcases mul_eq_zero.mp him with h | h
  · rw [h] at hre
    nlinarith [sq_nonneg z.im]
  · exact h

theorem conjugation_fixes_root {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) (c : Gal(K/ℚ)) (hc : IsConj φ c)
    (r : K) (hr : r^2=(d : K)) : c r=r := by
  apply φ.injective
  rw [hc.eq]
  have hz : (φ r)^2=(d : ℂ) := by simpa only [map_pow,map_natCast] using congrArg φ hr
  have him := complex_im_eq_zero_of_sq_eq_natCast d (φ r) hz
  apply Complex.ext <;> simp [him]

theorem root_mem_fixedField {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) (c : Gal(K/ℚ)) (hc : IsConj φ c)
    (r : K) (hr : r^2=(d : K)) : r ∈ GaloisConjugation.fixedField K c := by
  apply (IntermediateField.mem_fixedField_iff _ _).mpr
  have hle : Subgroup.zpowers c ≤ MulAction.stabilizer Gal(K/ℚ) r :=
    Subgroup.zpowers_le.mpr (conjugation_fixes_root φ c hc r hr)
  intro g hg
  exact hle hg

/-- The actual displayed root in the actual fixed field. -/
def fixedRoot {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) (c : Gal(K/ℚ)) (hc : IsConj φ c)
    (r : K) (hr : r^2=(d : K)) : GaloisConjugation.fixedField K c :=
  ⟨r,root_mem_fixedField φ c hc r hr⟩

theorem fixedRoot_sq {d : ℕ} {K : Type*} [Field K] [NumberField K]
    (φ : K →+* ℂ) (c : Gal(K/ℚ)) (hc : IsConj φ c)
    (r : K) (hr : r^2=(d : K)) : (fixedRoot φ c hc r hr)^2=(d : GaloisConjugation.fixedField K c) := by
  apply Subtype.ext
  change r^2 = ((d : GaloisConjugation.fixedField K c) : K)
  rw [hr]
  exact (map_natCast (algebraMap (GaloisConjugation.fixedField K c) K) d).symm

end UnitDistance.Sqrt241.QuadraticRoot
