module

public import UnitDistance.Sqrt241.Base.Local
public import UnitDistance.Sqrt241.Base.Selmer

@[expose] public section
set_option backward.privateInPublic true

/-!
# Every `p`-adic embedding of `B` is one of the two named ones

For `p ∈ {2, 3, 5, 29}` the square roots of `241` in `ℚ_p` are exactly
`iotaN sqrt241` and `iotaN' sqrt241` (`sq_eq_241_iff_2`, …), and every ring map
`B → ℚ_p` is `iotaN` or `iotaN'` (`ringHom_eq_iota2_or`, …). The square classes of
the radicands `radicandA i + radicandB i · s` for either root `s` are then read off from
the tables of `Local.lean` (`radicand_squareclass2`, …). This is the form in which the
local elements of `G_B` (`Local/`) use them: the image of `baseRoot` under a chosen place
is not controlled.
Also `not_isSquare_241_Q7`: `241` is not a square in `ℚ_7` (7 is inert in `B`).
-/

noncomputable section

namespace UnitDistance.Sqrt241.Base

open NumberField CanonicalGenus

variable {p : ℕ} [Fact p.Prime]

theorem iota_sqrt241_sq (r : ℤ_[p]) (hr : r * r = r + 60) :
    (iota r hr sqrt241) ^ 2 = 241 := by
  rw [← map_pow, sqrt241_sq, map_ofNat]

/-- The square roots of `241` in `ℚ_p` are `± ι(√241)`. -/
theorem sq_eq_241_iff (r : ℤ_[p]) (hr : r * r = r + 60) (s : ℚ_[p]) :
    s ^ 2 = 241 ↔ s = iota r hr sqrt241 ∨ s = -iota r hr sqrt241 := by
  rw [← iota_sqrt241_sq r hr, sq_eq_sq_iff_eq_or_eq_neg]

/-- Every `ℚ`-algebra map `B → ℚ_p` is `ι_r` or `ι_{1-r}`. -/
theorem algHom_eq_iota_or (r : ℤ_[p]) (hr : r * r = r + 60) (f : B →ₐ[ℚ] ℚ_[p]) :
    f = iota r hr ∨ f = iota (1 - r) (one_sub_root_mul_self hr) := by
  have hf : (f sqrt241) ^ 2 = 241 := by rw [← map_pow, sqrt241_sq, map_ofNat]
  rcases (sq_eq_241_iff r hr _).mp hf with h | h
  · exact Or.inl (algHom_ext h)
  · right
    apply algHom_ext
    rw [h, iota_one_sub, AlgHom.comp_apply]
    have h1 : ((sigma : B →ₐ[ℚ] B) : B → B) sqrt241 = -sqrt241 := sigma_sqrt241
    rw [h1, map_neg]

/-- `ι(alphaB i) = radicandA i + radicandB i · ι(√241)`. -/
theorem algHom_alphaB {A : Type*} [Ring A] [Algebra ℚ A] (f : B →ₐ[ℚ] A) (i : Fin 8) :
    f (alphaB i) = algebraMap ℚ A (radicandA i) + algebraMap ℚ A (radicandB i) * f sqrt241 := by
  rw [alphaB, map_add, map_mul, AlgHom.commutes, AlgHom.commutes]

/-! ## The four split primes -/

theorem sq_eq_241_iff_2 (s : ℚ_[2]) : s ^ 2 = 241 ↔ s = iota2 sqrt241 ∨ s = iota2' sqrt241 := by
  rw [sq_eq_241_iff root2 root2_mul_self, iota2'_eq_comp_sigma, AlgHom.comp_apply]
  have h1 : ((sigma : B →ₐ[ℚ] B) : B → B) sqrt241 = -sqrt241 := sigma_sqrt241
  rw [h1, map_neg]
  rfl

theorem sq_eq_241_iff_3 (s : ℚ_[3]) : s ^ 2 = 241 ↔ s = iota3 sqrt241 ∨ s = iota3' sqrt241 := by
  rw [sq_eq_241_iff root3 root3_mul_self, iota3'_eq_comp_sigma, AlgHom.comp_apply]
  have h1 : ((sigma : B →ₐ[ℚ] B) : B → B) sqrt241 = -sqrt241 := sigma_sqrt241
  rw [h1, map_neg]
  rfl

theorem sq_eq_241_iff_5 (s : ℚ_[5]) : s ^ 2 = 241 ↔ s = iota5 sqrt241 ∨ s = iota5' sqrt241 := by
  rw [sq_eq_241_iff root5' root5'_mul_self, iota5_eq_comp_sigma, AlgHom.comp_apply]
  have h1 : ((sigma : B →ₐ[ℚ] B) : B → B) sqrt241 = -sqrt241 := sigma_sqrt241
  rw [h1, map_neg, or_comm]
  rfl

theorem sq_eq_241_iff_29 (s : ℚ_[29]) :
    s ^ 2 = 241 ↔ s = iota29 sqrt241 ∨ s = iota29' sqrt241 := by
  rw [sq_eq_241_iff root29 root29_mul_self, iota29'_eq_comp_sigma, AlgHom.comp_apply]
  have h1 : ((sigma : B →ₐ[ℚ] B) : B → B) sqrt241 = -sqrt241 := sigma_sqrt241
  rw [h1, map_neg]
  rfl

theorem algHom_eq_iota2_or (f : B →ₐ[ℚ] ℚ_[2]) : f = iota2 ∨ f = iota2' := by
  rcases algHom_eq_iota_or root2 root2_mul_self f with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans (iota_congr root2'_eq root2'_mul_self).symm)

theorem algHom_eq_iota3_or (f : B →ₐ[ℚ] ℚ_[3]) : f = iota3 ∨ f = iota3' := by
  rcases algHom_eq_iota_or root3 root3_mul_self f with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans (iota_congr root3'_eq root3'_mul_self).symm)

theorem algHom_eq_iota5_or (f : B →ₐ[ℚ] ℚ_[5]) : f = iota5 ∨ f = iota5' := by
  rcases algHom_eq_iota_or root5' root5'_mul_self f with h | h
  · exact Or.inr h
  · exact Or.inl (h.trans (iota_congr root5_eq root5_mul_self).symm)

theorem algHom_eq_iota29_or (f : B →ₐ[ℚ] ℚ_[29]) : f = iota29 ∨ f = iota29' := by
  rcases algHom_eq_iota_or root29 root29_mul_self f with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans (iota_congr root29'_eq root29'_mul_self).symm)

/-- Every ring map `B → ℚ₂` is `iota2` or `iota2'`. -/
theorem ringHom_eq_iota2_or (f : B →+* ℚ_[2]) :
    f = (iota2 : B →+* ℚ_[2]) ∨ f = (iota2' : B →+* ℚ_[2]) := by
  rcases algHom_eq_iota2_or f.toRatAlgHom with h | h
  · exact Or.inl (RingHom.ext fun x ↦ congrArg (fun g : B →ₐ[ℚ] ℚ_[2] ↦ g x) h)
  · exact Or.inr (RingHom.ext fun x ↦ congrArg (fun g : B →ₐ[ℚ] ℚ_[2] ↦ g x) h)

theorem ringHom_eq_iota3_or (f : B →+* ℚ_[3]) :
    f = (iota3 : B →+* ℚ_[3]) ∨ f = (iota3' : B →+* ℚ_[3]) := by
  rcases algHom_eq_iota3_or f.toRatAlgHom with h | h
  · exact Or.inl (RingHom.ext fun x ↦ congrArg (fun g : B →ₐ[ℚ] ℚ_[3] ↦ g x) h)
  · exact Or.inr (RingHom.ext fun x ↦ congrArg (fun g : B →ₐ[ℚ] ℚ_[3] ↦ g x) h)

theorem ringHom_eq_iota5_or (f : B →+* ℚ_[5]) :
    f = (iota5 : B →+* ℚ_[5]) ∨ f = (iota5' : B →+* ℚ_[5]) := by
  rcases algHom_eq_iota5_or f.toRatAlgHom with h | h
  · exact Or.inl (RingHom.ext fun x ↦ congrArg (fun g : B →ₐ[ℚ] ℚ_[5] ↦ g x) h)
  · exact Or.inr (RingHom.ext fun x ↦ congrArg (fun g : B →ₐ[ℚ] ℚ_[5] ↦ g x) h)

theorem ringHom_eq_iota29_or (f : B →+* ℚ_[29]) :
    f = (iota29 : B →+* ℚ_[29]) ∨ f = (iota29' : B →+* ℚ_[29]) := by
  rcases algHom_eq_iota29_or f.toRatAlgHom with h | h
  · exact Or.inl (RingHom.ext fun x ↦ congrArg (fun g : B →ₐ[ℚ] ℚ_[29] ↦ g x) h)
  · exact Or.inr (RingHom.ext fun x ↦ congrArg (fun g : B →ₐ[ℚ] ℚ_[29] ↦ g x) h)

/-! ## Square classes of `radicandA i + radicandB i · s` -/

private theorem radicand_eq_iota {q : ℕ} [Fact q.Prime] (f : B →ₐ[ℚ] ℚ_[q]) (i : Fin 8) :
    (radicandA i : ℚ_[q]) + (radicandB i : ℚ_[q]) * f sqrt241 = f ((alpha i : 𝓞 B) : B) := by
  rw [← alphaB_eq, algHom_alphaB]
  simp

theorem radicand_squareclass2 (i : Fin 8) : ∃ z : ℚ_[2], z ≠ 0 ∧
    (radicandA i : ℚ_[2]) + (radicandB i : ℚ_[2]) * iota2 sqrt241 = (squareclass2 i : ℚ_[2]) * z ^ 2 := by
  rw [radicand_eq_iota]; exact iota2_alpha i

theorem radicand_squareclass2' (i : Fin 8) : ∃ z : ℚ_[2], z ≠ 0 ∧
    (radicandA i : ℚ_[2]) + (radicandB i : ℚ_[2]) * iota2' sqrt241 =
      (squareclass2' i : ℚ_[2]) * z ^ 2 := by
  rw [radicand_eq_iota]; exact iota2'_alpha i

theorem radicand_squareclass3 (i : Fin 8) : ∃ z : ℚ_[3], z ≠ 0 ∧
    (radicandA i : ℚ_[3]) + (radicandB i : ℚ_[3]) * iota3 sqrt241 = (squareclass3 i : ℚ_[3]) * z ^ 2 := by
  rw [radicand_eq_iota]; exact iota3_alpha i

theorem radicand_squareclass3' (i : Fin 8) : ∃ z : ℚ_[3], z ≠ 0 ∧
    (radicandA i : ℚ_[3]) + (radicandB i : ℚ_[3]) * iota3' sqrt241 =
      (squareclass3' i : ℚ_[3]) * z ^ 2 := by
  rw [radicand_eq_iota]; exact iota3'_alpha i

theorem radicand_squareclass5 (i : Fin 8) : ∃ z : ℚ_[5], z ≠ 0 ∧
    (radicandA i : ℚ_[5]) + (radicandB i : ℚ_[5]) * iota5 sqrt241 = (squareclass5 i : ℚ_[5]) * z ^ 2 := by
  rw [radicand_eq_iota]; exact iota5_alpha i

theorem radicand_squareclass5' (i : Fin 8) : ∃ z : ℚ_[5], z ≠ 0 ∧
    (radicandA i : ℚ_[5]) + (radicandB i : ℚ_[5]) * iota5' sqrt241 =
      (squareclass5' i : ℚ_[5]) * z ^ 2 := by
  rw [radicand_eq_iota]; exact iota5'_alpha i

theorem radicand_squareclass29 (i : Fin 8) : ∃ z : ℚ_[29], z ≠ 0 ∧
    (radicandA i : ℚ_[29]) + (radicandB i : ℚ_[29]) * iota29 sqrt241 =
      (squareclass29 i : ℚ_[29]) * z ^ 2 := by
  rw [radicand_eq_iota]; exact iota29_alpha i

theorem radicand_squareclass29' (i : Fin 8) : ∃ z : ℚ_[29], z ≠ 0 ∧
    (radicandA i : ℚ_[29]) + (radicandB i : ℚ_[29]) * iota29' sqrt241 =
      (squareclass29' i : ℚ_[29]) * z ^ 2 := by
  rw [radicand_eq_iota]; exact iota29'_alpha i

/-! ## The inert prime `7` -/

/-- `241` is not a square in `ℚ_7`. -/
theorem not_isSquare_241_Q7 : ¬ IsSquare (241 : ℚ_[7]) := by
  rintro ⟨z, hz⟩
  have hz1 : ‖z‖ ≤ 1 := by
    have h241 : ‖(241 : ℚ_[7])‖ = 1 := by
      have : ((241 : ℤ) : ℚ_[7]) = 241 := by norm_num
      rw [← this, Padic.norm_intCast_eq_one_iff]
      decide
    have h2 : ‖z‖ * ‖z‖ = 1 := by rw [← norm_mul, ← hz, h241]
    nlinarith [norm_nonneg z]
  set y : ℤ_[7] := ⟨z, hz1⟩
  have hy : y * y = 241 := by
    apply Subtype.ext
    change z * z = ((241 : ℤ_[7]) : ℚ_[7])
    rw [← hz]
    norm_cast
  have h := congrArg PadicInt.toZMod hy
  rw [map_mul, map_ofNat] at h
  generalize PadicInt.toZMod y = t at h
  revert t
  decide

end UnitDistance.Sqrt241.Base
