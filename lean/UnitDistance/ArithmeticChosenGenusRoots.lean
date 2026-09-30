module

public import UnitDistance.ArithmeticChosenGenusField
public import UnitDistance.QuadraticGeneratedRootFamily
public import UnitDistance.QuadraticRootFamilyGalois

@[expose] public section
set_option backward.privateInPublic true


/-! All actual independent sign automorphisms of the generated genus field. -/
noncomputable section
namespace UnitDistance.ArithmeticChosenGenus
open Multiquadratic

def genusRootFamily : RootFamily radicands 7 GenusField :=
  generatedRootFamily radicands roots roots_sq genusField_generated genusField_galoisGroup_card

abbrev signAutomorphism := genusRootFamily.automorphism

theorem signAutomorphism_roots (v : Fin 7 → ZMod 2) (i : Fin 7) :
    signAutomorphism v (roots i)=binarySign (v i)*roots i :=
  genusRootFamily.action v i i.isLt

theorem signAutomorphism_involutive (v : Fin 7 → ZMod 2) :
    Function.Involutive (signAutomorphism v) := genusRootFamily.involutive v

theorem signAutomorphism_injective : Function.Injective signAutomorphism :=
  genusRootFamily.automorphism_injective radicands_ne_zero

theorem signAutomorphism_bijective : Function.Bijective signAutomorphism :=
  genusRootFamily.automorphism_bijective radicands_ne_zero genusField_galoisGroup_card

theorem automorphism_ext_roots {σ τ : Gal(GenusField/ℚ)}
    (h : ∀ i, σ (roots i)=τ (roots i)) : σ=τ :=
  genusRootFamily.aut_ext radicands_ne_zero genusField_galoisGroup_card h

def genusSignHom : Multiplicative (Fin 7 → ZMod 2) →* Gal(GenusField/ℚ) :=
  genusRootFamily.signHom radicands_ne_zero genusField_galoisGroup_card

def genusGaloisEquiv : Multiplicative (Fin 7 → ZMod 2) ≃* Gal(GenusField/ℚ) :=
  genusRootFamily.galoisEquiv radicands_ne_zero genusField_galoisGroup_card

theorem every_automorphism_involutive (σ : Gal(GenusField/ℚ)) : Function.Involutive σ :=
  genusRootFamily.every_automorphism_involutive radicands_ne_zero genusField_galoisGroup_card σ

end UnitDistance.ArithmeticChosenGenus
