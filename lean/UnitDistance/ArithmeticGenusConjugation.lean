module

public import UnitDistance.ArithmeticChosenGenusRoots
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.Tactic

@[expose] public section
set_option backward.privateInPublic true


/-! Actual complex conjugation on the seven independently chosen genus roots. -/
noncomputable section
namespace UnitDistance.ArithmeticChosenGenus
open NumberField.ComplexEmbedding Multiquadratic

theorem complex_star_of_sq_pos (z : ℂ) (a : ℝ) (ha : 0 < a) (hz : z^2=(a : ℂ)) :
    star z = z := by
  have hre : z.re^2-z.im^2=a := by
    simpa [pow_two,Complex.mul_re] using congrArg Complex.re hz
  have him : z.re*z.im=0 := by
    have h := congrArg Complex.im hz
    simp [pow_two,Complex.mul_im] at h
    linarith
  have him0 : z.im=0 := by
    rcases mul_eq_zero.mp him with h | h
    · rw [h] at hre
      nlinarith [sq_nonneg z.im]
    · exact h
  apply Complex.ext <;> simp [him0]

theorem complex_star_of_sq_neg_one (z : ℂ) (hz : z^2= -1) : star z = -z := by
  have hsq : z^2=Complex.I^2 := hz.trans Complex.I_sq.symm
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hsq with rfl | rfl <;> simp

/-- Under every actual complex embedding, conjugation negates only the
imaginary genus radical and fixes all six positive rational radicals. -/
theorem conjugation_eq_sign (φ : GenusField →+* ℂ) (c : Gal(GenusField/ℚ))
    (hc : IsConj φ c) : c = signAutomorphism (Pi.single 0 1) := by
  apply automorphism_ext_roots
  intro i
  apply φ.injective
  rw [hc.eq, signAutomorphism_roots, map_mul]
  by_cases hi : i=0
  · subst i
    have hz : (φ (roots 0))^2= -1 := by
      have h := congrArg φ (roots_sq 0)
      simpa [radicands] using h
    simpa [binarySign,binarySignInteger] using complex_star_of_sq_neg_one (φ (roots 0)) hz
  · have hp : (0 : ℝ) < (radicands i : ℝ) := by
      fin_cases i <;> simp_all [radicands]
    have hz : (φ (roots i))^2=((radicands i : ℝ) : ℂ) := by
      simpa only [map_pow, map_ratCast, Complex.ofReal_ratCast] using congrArg φ (roots_sq i)
    simpa [Pi.single_apply,hi,Ne.symm hi,binarySign,binarySignInteger] using
      complex_star_of_sq_pos (φ (roots i)) (radicands i) hp hz

end UnitDistance.ArithmeticChosenGenus
