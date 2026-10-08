module

public import UnitDistance.Sqrt241.Base.LocalRoots

@[expose] public section
set_option backward.privateInPublic true

/-!
# The `41`-adic embeddings of `B = ℚ(√241)` (version 2)

`41` splits in `B`: `X² − X − 60 ≡ (X − 24)(X − 18) (mod 41)`. The embedding `iota41`
(`ω ↦ root41 ≡ 24`) belongs to the prime `P41 = ker (ω ↦ 24)`, the prime of version 2's cap
(Frobenius vector `00111000`, `papers/0.042901/certificates/kummer41.gp`); `iota41'`
(`ω ↦ root41' ≡ 18`) belongs to the uncapped prime (`00110100`). As for `2, 3, 5, 29`
(`Base/Local.lean`, `Base/LocalRoots.lean`), every `ℚ`-algebra map `B → ℚ₄₁` is one of the
two, and the square classes of the eight radicands are given by representatives
(`squareclass41`, `squareclass41'`, with `3` a non-square mod `41`).
-/

noncomputable section

namespace UnitDistance.Sqrt241.Base

open NumberField CanonicalGenus

instance fact_prime_41 : Fact (Nat.Prime 41) := ⟨by norm_num⟩

/-- The root of `X² - X - 60` in `ℤ_41` with `r ≡ 24 (mod 41)`. -/
def root41 : ℤ_[41] := (exists_omegaRoot (p := 41) 24 (by decide) (by decide)).choose

theorem root41_mul_self : root41 * root41 = root41 + 60 :=
  (exists_omegaRoot (p := 41) 24 (by decide) (by decide)).choose_spec.1

theorem toZMod_root41 : PadicInt.toZMod root41 = 24 := by
  rw [root41, (exists_omegaRoot (p := 41) 24 (by decide) (by decide)).choose_spec.2]; decide

/-- The embedding `B → ℚ_41` at the capped prime (`ω ↦ root41`). -/
def iota41 : B →ₐ[ℚ] ℚ_[41] := iota root41 root41_mul_self

/-- The embedding `𝓞 B → ℤ_41` at the capped prime. -/
def iotaInt41 : 𝓞 B →+* ℤ_[41] := iotaInt root41 root41_mul_self

theorem iota41_coe (x : 𝓞 B) : iota41 (x : B) = (iotaInt41 x : ℚ_[41]) :=
  iota_coe _ _ x

/-- Square-class representatives of `iota41 (alpha i)` in `ℚ_41^×/ℚ_41^{×2}`. -/
def squareclass41 : Fin 8 → ℤ := ![1, 1, 3, 3, 3, 1, 1, 1]

theorem iota41_alpha (i : Fin 8) : ∃ z : ℚ_[41], z ≠ 0 ∧
    iota41 ((alpha i : 𝓞 B) : B) = (squareclass41 i : ℚ_[41]) * z ^ 2 := by
  fin_cases i
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root41 0 (1) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root41 1 (1) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root41 2 (3) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root41 3 (3) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root41 4 (3) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root41 5 (1) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root41 6 (1) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root41 7 (1) (by decide)

/-- The root of `X² - X - 60` in `ℤ_41` with `r ≡ 18 (mod 41)`. -/
def root41' : ℤ_[41] := (exists_omegaRoot (p := 41) 18 (by decide) (by decide)).choose

theorem root41'_mul_self : root41' * root41' = root41' + 60 :=
  (exists_omegaRoot (p := 41) 18 (by decide) (by decide)).choose_spec.1

theorem toZMod_root41' : PadicInt.toZMod root41' = 18 := by
  rw [root41', (exists_omegaRoot (p := 41) 18 (by decide) (by decide)).choose_spec.2]; decide

/-- The embedding `B → ℚ_41` at the uncapped prime (`ω ↦ root41'`). -/
def iota41' : B →ₐ[ℚ] ℚ_[41] := iota root41' root41'_mul_self

/-- Square-class representatives of `iota41' (alpha i)` in `ℚ_41^×/ℚ_41^{×2}`. -/
def squareclass41' : Fin 8 → ℤ := ![1, 1, 3, 3, 1, 3, 1, 1]

theorem iota41'_alpha (i : Fin 8) : ∃ z : ℚ_[41], z ≠ 0 ∧
    iota41' ((alpha i : 𝓞 B) : B) = (squareclass41' i : ℚ_[41]) * z ^ 2 := by
  fin_cases i
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root41' 0 (1) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root41' 1 (1) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root41' 2 (3) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root41' 3 (3) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root41' 4 (1) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root41' 5 (3) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root41' 6 (1) (by decide)
  · exact iota_alpha_of_unit_odd _ _ _ toZMod_root41' 7 (1) (by decide)

theorem root41'_eq : root41' = 1 - root41 :=
  omegaRoot_eq_one_sub root41_mul_self root41'_mul_self fun h ↦ by
    have := congrArg PadicInt.toZMod h
    rw [toZMod_root41, toZMod_root41'] at this
    exact absurd this (by decide)

theorem iota41'_eq_comp_sigma : iota41' = iota41.comp (sigma : B →ₐ[ℚ] B) :=
  (iota_congr root41'_eq root41'_mul_self).trans (iota_one_sub root41 root41_mul_self)

theorem sq_eq_241_iff_41 (s : ℚ_[41]) :
    s ^ 2 = 241 ↔ s = iota41 sqrt241 ∨ s = iota41' sqrt241 := by
  rw [sq_eq_241_iff root41 root41_mul_self, iota41'_eq_comp_sigma, AlgHom.comp_apply]
  have h1 : ((sigma : B →ₐ[ℚ] B) : B → B) sqrt241 = -sqrt241 := sigma_sqrt241
  rw [h1, map_neg]
  rfl

theorem algHom_eq_iota41_or (f : B →ₐ[ℚ] ℚ_[41]) : f = iota41 ∨ f = iota41' := by
  rcases algHom_eq_iota_or root41 root41_mul_self f with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans (iota_congr root41'_eq root41'_mul_self).symm)

theorem radicand_squareclass41 (i : Fin 8) : ∃ z : ℚ_[41], z ≠ 0 ∧
    (radicandA i : ℚ_[41]) + (radicandB i : ℚ_[41]) * iota41 sqrt241 =
      (squareclass41 i : ℚ_[41]) * z ^ 2 := by
  have h : (radicandA i : ℚ_[41]) + (radicandB i : ℚ_[41]) * iota41 sqrt241 =
      iota41 ((alpha i : 𝓞 B) : B) := by
    rw [← alphaB_eq, algHom_alphaB]
    simp
  rw [h]; exact iota41_alpha i

theorem radicand_squareclass41' (i : Fin 8) : ∃ z : ℚ_[41], z ≠ 0 ∧
    (radicandA i : ℚ_[41]) + (radicandB i : ℚ_[41]) * iota41' sqrt241 =
      (squareclass41' i : ℚ_[41]) * z ^ 2 := by
  have h : (radicandA i : ℚ_[41]) + (radicandB i : ℚ_[41]) * iota41' sqrt241 =
      iota41' ((alpha i : 𝓞 B) : B) := by
    rw [← alphaB_eq, algHom_alphaB]
    simp
  rw [h]; exact iota41'_alpha i

end UnitDistance.Sqrt241.Base
