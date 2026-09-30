/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceH2Localization
public import Mathlib.LinearAlgebra.Pi

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false
/-!
# The family of finite-place degree-two localization maps

The restriction maps to all absolute decomposition subgroups are assembled into one linear map
with dependent function codomain.
-/

open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ)

/-- The product of degree-two continuous cohomology spaces of the finite-place absolute
decomposition subgroups. -/
abbrev FinitePlaceH2LocalizationTarget :=
  (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) →
    continuousCohomologyZModPLifted p
      (finitePlaceAbsoluteDecompositionGroup F v) 2

/-- Simultaneous restriction of an absolute degree-two class to every finite-place decomposition
subgroup. -/
noncomputable def finitePlaceH2LocalizationFamily :
    continuousCohomologyZModPLifted p (Field.absoluteGaloisGroup F) 2 →ₗ[ZMod p]
      FinitePlaceH2LocalizationTarget F p :=
  LinearMap.pi fun v ↦ finitePlaceH2Localization F p v

/-- Each component of the family map is the corresponding finite-place localization. -/
@[simp]
theorem finitePlaceH2LocalizationFamily_apply
    (x : continuousCohomologyZModPLifted p (Field.absoluteGaloisGroup F) 2)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    finitePlaceH2LocalizationFamily F p x v =
      finitePlaceH2Localization F p v x :=
  rfl

end ClassFieldTower.Martinet.Shafarevich
