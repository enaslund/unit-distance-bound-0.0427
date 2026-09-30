module

public import UnitDistance.PadicTwoQuadraticField
public import UnitDistance.QuadraticLiftSquare

@[expose] public section
set_option backward.privateInPublic true


/-! Genuine square and commutator actions in the degree256 local field. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.PadicTwoQuadratic
open Multiquadratic PadicTwoGenus PadicTwoNormCatalog
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev G := Gal(QuadraticField/ℚ_[2])

def genusVector (σ : G) : Fin 3 → ZMod 2 := (signEquiv (σ.restrictNormal E)).toAdd

theorem restrict_genusVector (σ : G) (a : E) :
    σ (algebraMap E QuadraticField a)=
      algebraMap E QuadraticField (signAutomorphism (genusVector σ) a) := by
  have h : signAutomorphism (genusVector σ)=σ.restrictNormal E := signEquiv.symm_apply_apply _
  rw [h]
  exact (AlgEquiv.restrictNormal_commutes σ E a).symm

theorem every_genus_automorphism_involutive (σ : Gal(E/ℚ_[2])) : Function.Involutive σ := by
  have he : signAutomorphism (signEquiv σ).toAdd=σ := signEquiv.symm_apply_apply σ
  rw [← he]
  exact signAutomorphism_involutive _

theorem square_action (σ : G) (i : Fin 5) (r : QuadraticField)
    (hr : r^2=algebraMap E QuadraticField (alpha i)) :
    (σ^2) r=binarySign (form i (genusVector σ))*r :=
  square_on_root_of_twisted_norm
    (signAutomorphism (genusVector σ)).toRingEquiv σ.toRingEquiv
    (restrict_genusVector σ) hr (multiplier_twist i (genusVector σ)) _
    (multiplier_norm i (genusVector σ))

theorem aut_pow_four (σ : G) : σ^4=1 :=
  quadraticTower.aut_pow_four every_genus_automorphism_involutive σ

theorem aut_square_central (σ τ : G) : Commute (σ^2) τ :=
  quadraticTower.aut_square_commute every_genus_automorphism_involutive
    (fun i _ => alpha_invariant i) σ τ

theorem genusVector_mul (σ τ : G) : genusVector (σ*τ)=genusVector σ+genusVector τ := by
  change (signEquiv ((AlgEquiv.restrictNormalHom E) (σ*τ))).toAdd=_
  rw [map_mul,map_mul]
  rfl

theorem commutator_eq_three_squares (σ τ : G) : σ⁻¹*τ⁻¹*σ*τ=σ^2*τ^2*(σ*τ)^2 := by
  have hc (g : G) : g^3=g⁻¹ := by
    apply mul_right_cancel (b:=g)
    rw [inv_mul_cancel]
    simpa only [← pow_succ] using aut_pow_four g
  symm
  calc
    σ^2*τ^2*(σ*τ)^2=σ^2*(τ^2*σ)*τ*σ*τ := by simp only [pow_two,mul_assoc]
    _ = σ^2*(σ*τ^2)*τ*σ*τ := by rw [(aut_square_central τ σ).eq]
    _ = σ^3*τ^3*σ*τ := by group
    _ = _ := by rw [hc σ,hc τ]

private theorem map_sign (σ : G) (w : ZMod 2) : σ (binarySign w)=binarySign w := by
  simp [binarySign]

theorem commutator_action (σ τ : G) (i : Fin 5) (r : QuadraticField)
    (hr : r^2=algebraMap E QuadraticField (alpha i)) :
    (σ⁻¹*τ⁻¹*σ*τ) r=binarySign
      (form i (genusVector σ+genusVector τ)+form i (genusVector σ)+form i (genusVector τ))*r := by
  rw [commutator_eq_three_squares]
  simp only [AlgEquiv.mul_apply,square_action _ i r hr,map_mul,map_sign,
    genusVector_mul,binarySign_add]
  ring

end UnitDistance.PadicTwoQuadratic
