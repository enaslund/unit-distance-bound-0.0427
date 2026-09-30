module

public import UnitDistance.Sqrt241.Retained.Basic
public import UnitDistance.Sqrt241.Local.Elements

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# The concrete input: the local elements of `G_B`

`Retained.input : Retained.Input` with `E = Local.localElements`, all fields from `Local/`
(`Local/Elements.lean`: relations, labels, `σ̂`-relations `tame_sigma`,
`dyadicLocal_sigma`, `frob29_sigma`; `Local.coe_conj₂`, `Local.frob7_not_mem`,
`Local.conj₁_isConj`). Everything downstream is therefore unconditional.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Retained

open Tower Presentation _root_.UnitDistance.Sqrt241.Local

/-- `s = h σ̂` turns the form `x₂ = h (σ̂ x₁ σ̂⁻¹) h⁻¹` of the `σ̂`-relations of `Local/` into
`x₂ = s x₁ s⁻¹`, `s σ̂⁻¹ ∈ G_B`. -/
theorem conj_form {h x y : Ghat} (hx : y = h * (sigmaHat * x * sigmaHat⁻¹) * h⁻¹) :
    y = (h * sigmaHat) * x * (h * sigmaHat)⁻¹ := by
  rw [hx]
  group

theorem mul_sigma_inv_mem {h : Ghat} (hh : h ∈ GB) : h * sigmaHat * sigmaHat⁻¹ ∈ GB := by
  simpa using hh

theorem sigma_mul_inv_mem_of_not_mem {F : Ghat} (hF : F ∉ GB) : sigmaHat * F⁻¹ ∈ GB := by
  rcases mem_GB_or_inv_mul_mem F with h | h
  · exact absurd h hF
  · have h1 : F⁻¹ * sigmaHat ∈ GB := by simpa using GB.inv_mem h
    have h2 := GB_normal.conj_mem _ h1 sigmaHat
    simpa [mul_assoc] using h2

/-- **The concrete input** (`Local.localElements`). -/
def input : Input where
  E := localElements
  relations := localElements_relations
  labels := localElements_labels
  conj_compat := coe_conj₂
  tame_compat_q := by
    obtain ⟨h, hh, h1, h2⟩ := tame_sigma 0
    exact ⟨h * sigmaHat, mul_sigma_inv_mem hh, conj_form h1, conj_form h2⟩
  tame_compat_r := by
    obtain ⟨h, hh, h1, h2⟩ := tame_sigma 1
    exact ⟨h * sigmaHat, mul_sigma_inv_mem hh, conj_form h1, conj_form h2⟩
  dyadic_compat := by
    obtain ⟨h, hh, hrel⟩ := dyadicLocal_sigma
    exact ⟨h * sigmaHat, mul_sigma_inv_mem hh, fun g => conj_form (hrel g)⟩
  cap_compat := by
    obtain ⟨h, hh, hrel⟩ := frob29_sigma
    exact ⟨h * sigmaHat, mul_sigma_inv_mem hh, conj_form hrel⟩
  frob7_compat := ⟨frob7, rfl, sigma_mul_inv_mem_of_not_mem frob7_not_mem⟩
  phi := phi₁
  conj_isConj := conj₁_isConj

@[simp] theorem input_E : input.E = localElements := rfl

end UnitDistance.Sqrt241.Retained
