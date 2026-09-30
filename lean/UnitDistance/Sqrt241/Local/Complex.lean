module

public import UnitDistance.Sqrt241.Local.Maps
public import UnitDistance.Sqrt241.Base.Signs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings

@[expose] public section
set_option backward.privateInPublic true

/-!
# Complex conjugations `c₁`, `c₂`

`complexEmb : Closure →+* ℂ` extends the first real place `Base.complexEmbPlus`
(`√241 ↦ +√241`) of `B`; `conjAbs` is a complex conjugation for it
(`IsConj complexEmb conjAbs`). It fixes `√241` and multiplies `√α_k` by the sign of
`α_k` at the first real place, so its genus label is `Base.signPlus = 10111010`
(`conjAbs_hasLabel`). Its restriction to `Ω` is `conj₁ ∈ G_B`, and
`conj₂ = σ̂ c₁ σ̂⁻¹` has label `sigmaMatrix signPlus = signMinus = 11000101`.
Both have order dividing `2`; `conj₁` is a complex conjugation of
`phi₁ = complexEmb|_Ω` and `conj₂` one of `phi₂ = phi₁ ∘ σ̂⁻¹`, which restricts on `B`
to `Base.complexEmbMinus`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Local

open NumberField CanonicalGenus Base Multiquadratic Tower NumberField.ComplexEmbedding

/-! ## Complex numbers with real square -/

theorem conj_eq_self_of_sq_pos {z : ℂ} {r : ℝ} (h : z ^ 2 = r) (hr : 0 < r) :
    starRingEnd ℂ z = z := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at hre him
  rw [Complex.conj_eq_iff_im]
  rcases mul_eq_zero.mp (show z.im * z.re = 0 by linarith) with h0 | h0
  · exact h0
  · rw [h0] at hre
    nlinarith [sq_nonneg z.im]

theorem conj_eq_neg_of_sq_neg {z : ℂ} {r : ℝ} (h : z ^ 2 = r) (hr : r < 0) :
    starRingEnd ℂ z = -z := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [sq, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at hre him
  have hre0 : z.re = 0 := by
    rcases mul_eq_zero.mp (show z.re * z.im = 0 by linarith) with h0 | h0
    · exact h0
    · rw [h0] at hre
      nlinarith [sq_nonneg z.re]
  apply Complex.ext
  · simp [hre0]
  · simp

/-! ## A complex embedding of the closure above the first real place -/

theorem exists_complexEmb : ∃ φ : Closure →+* ℂ, ∀ b : B, φ (b : Closure) = complexEmbPlus b := by
  let : Algebra B ℂ := complexEmbPlus.toAlgebra
  have : Algebra.IsAlgebraic B Closure := Algebra.IsAlgebraic.tower_top (K := ℚ) B
  let f : Closure →ₐ[B] ℂ := IsAlgClosed.lift
  exact ⟨f.toRingHom, fun b => f.commutes b⟩

/-- A complex embedding of the closure restricting to `√241 ↦ +√241` on `B`. -/
def complexEmb : Closure →+* ℂ := exists_complexEmb.choose

theorem complexEmb_B (b : B) : complexEmb (b : Closure) = complexEmbPlus b :=
  exists_complexEmb.choose_spec b

theorem exists_complexConj (φ : Closure →+* ℂ) : ∃ c : Gal(Closure/ℚ), IsConj φ c := by
  obtain ⟨ν, hν⟩ := exists_comp_symm_eq_of_comp_eq (k := ℚ) φ (conjugate φ) (RingHom.ext_rat _ _)
  exact ⟨ν.symm, hν.symm⟩

/-- A complex conjugation of the closure for `complexEmb`. -/
def conjAbs : Gal(Closure/ℚ) := (exists_complexConj complexEmb).choose

theorem conjAbs_isConj : IsConj complexEmb conjAbs := (exists_complexConj complexEmb).choose_spec

theorem complexEmb_conjAbs (x : Closure) :
    complexEmb (conjAbs x) = starRingEnd ℂ (complexEmb x) :=
  conjAbs_isConj.eq x

theorem conjAbs_mul_self : conjAbs * conjAbs = 1 := by
  apply AlgEquiv.ext
  intro x
  exact isConj_apply_apply conjAbs_isConj x

theorem conjAbs_baseRoot : conjAbs baseRoot = baseRoot := by
  apply complexEmb.injective
  rw [complexEmb_conjAbs]
  have h := complexEmb_B sqrt241
  rw [coe_sqrt241] at h
  rw [h]
  simp [complexEmbPlus]

theorem complexEmb_genusRoot_sq (k : Fin 8) :
    (complexEmb (genusRoot k)) ^ 2 = ((embPlus ((alpha k : 𝓞 B) : B) : ℝ) : ℂ) := by
  rw [← map_pow, genusRoot_sq, ← coe_alphaB, complexEmb_B, alphaB_eq]
  rfl

/-- **Label of `c₁`**: the sign vector `signPlus = 10111010` of the first real place. -/
theorem conjAbs_hasLabel : HasLabel conjAbs signPlus := by
  intro k
  apply complexEmb.injective
  rw [complexEmb_conjAbs]
  rcases (show signPlus k = 0 ∨ signPlus k = 1 by fin_cases k <;> simp [signPlus]) with h | h
  · rw [conj_eq_self_of_sq_pos (complexEmb_genusRoot_sq k) ((embPlus_alpha_sign k).2 h), h,
      binarySign_zero, one_mul]
  · rw [conj_eq_neg_of_sq_neg (complexEmb_genusRoot_sq k) ((embPlus_alpha_sign k).1 h), h,
      map_mul]
    simp [binarySign, binarySignInteger]

/-! ## `c₁`, `c₂` in `G_B` -/

/-- The complex conjugation `c₁ ∈ G_B` at the first real place. -/
def conj₁ : GB := ⟨toGhat conjAbs, (toGhat_mem_GB_iff _).mpr conjAbs_baseRoot⟩

/-- The complex conjugation `c₂ = σ̂ c₁ σ̂⁻¹ ∈ G_B` at the second real place. -/
def conj₂ : GB := conjGB sigmaHat conj₁

theorem coe_conj₂ : (conj₂ : Ghat) = sigmaHat * conj₁ * sigmaHat⁻¹ := rfl

theorem signPlus_eq : signPlus = RetainedQuadratic.binaryVector 8 93 := by decide +kernel

theorem signMinus_eq : signMinus = RetainedQuadratic.binaryVector 8 163 := by decide +kernel

theorem sigmaMatrix_signPlus : sigmaMatrix signPlus = signMinus := by decide +kernel

theorem conj₁_hasLabel : HasLabelHat conj₁ (RetainedQuadratic.binaryVector 8 93) :=
  ⟨conjAbs, rfl, signPlus_eq ▸ conjAbs_hasLabel⟩

theorem conj₂_hasLabel : HasLabelHat conj₂ (RetainedQuadratic.binaryVector 8 163) := by
  have h := (show HasLabelHat conj₁ signPlus from ⟨conjAbs, rfl, conjAbs_hasLabel⟩).conj_sigmaHat
  rw [sigmaMatrix_signPlus, signMinus_eq] at h
  exact h

theorem conj₁_mul_self : conj₁ * conj₁ = 1 := by
  apply Subtype.ext
  change toGhat conjAbs * toGhat conjAbs = 1
  rw [← map_mul, conjAbs_mul_self, map_one]

theorem conj₁_sq : conj₁ ^ 2 = 1 := by rw [sq, conj₁_mul_self]

theorem conj₂_sq : conj₂ ^ 2 = 1 := by rw [conj₂, ← map_pow, conj₁_sq, map_one]

/-- The complex embedding of `Ω` at the first real place. -/
def phi₁ : Omega →+* ℂ := complexEmb.comp (algebraMap Omega Closure)

theorem phi₁_B (b : B) : phi₁ ⟨(b : Closure), B_le_Omega b.2⟩ = complexEmbPlus b :=
  complexEmb_B b

theorem conj₁_isConj : IsConj phi₁ (conj₁ : Ghat) := by
  apply RingHom.ext
  intro x
  change starRingEnd ℂ (complexEmb (x : Closure)) = complexEmb ((toGhat conjAbs x : Omega) : Closure)
  rw [toGhat_apply, complexEmb_conjAbs]

/-- The complex embedding of `Ω` at the second real place. -/
def phi₂ : Omega →+* ℂ := phi₁.comp (sigmaHat.symm : Omega ≃+* Omega).toRingHom

theorem conj₂_isConj : IsConj phi₂ (conj₂ : Ghat) := by
  apply RingHom.ext
  intro x
  change starRingEnd ℂ (phi₁ (sigmaHat.symm x)) = phi₁ (sigmaHat.symm ((sigmaHat * conj₁ * sigmaHat⁻¹) x))
  have h := congrArg (fun f : Omega →+* ℂ => f (sigmaHat.symm x)) conj₁_isConj
  simp only [RingHom.comp_apply] at h
  change starRingEnd ℂ (phi₁ (sigmaHat.symm x)) = phi₁ ((conj₁ : Ghat) (sigmaHat.symm x)) at h
  rw [h]
  congr 1
  simp only [AlgEquiv.mul_apply]
  change _ = sigmaHat.symm (sigmaHat ((conj₁ : Ghat) (sigmaHat.symm x)))
  rw [AlgEquiv.symm_apply_apply]

end UnitDistance.Sqrt241.Local
