module

public import UnitDistance.PadicTwoGenusField
public import UnitDistance.QuadraticNormTwist

@[expose] public section
set_option backward.privateInPublic true


/-! Five actual local norm extensions detecting every quadratic coordinate
except the single Q₂ norm relation. -/
noncomputable section
namespace UnitDistance.PadicTwoNormCatalog
open Multiquadratic PadicTwoGenus
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
abbrev E := PadicTwoGenus.GenusField

private theorem has_seven_scalar : ∃ s : ℚ_[2],s^2= -7 := by
  obtain ⟨s,hs⟩ := PadicTwo.genus_relations.2.1.exists_sq
  exact ⟨s,hs.symm⟩
def sevenScalar : ℚ_[2] := has_seven_scalar.choose
theorem sevenScalar_sq : sevenScalar^2= -7 := has_seven_scalar.choose_spec

def a : Fin 5 → E := ![roots 0,2*roots 0,roots 1,roots 2,roots 0*roots 1]
def b : Fin 5 → E := ![roots 1,roots 2,roots 1,roots 2,roots 0*roots 2]
def x : Fin 5 → E := ![1,1,2,5,algebraMap ℚ_[2] E sevenScalar]
def z : Fin 5 → E := ![1,1,1,2,1]
def alpha (i : Fin 5) : E := x i+a i

def charA (v : Fin 3 → ZMod 2) : Fin 5 → ZMod 2 := ![v 0,v 0,v 1,v 2,v 0+v 1]
def charB (v : Fin 3 → ZMod 2) : Fin 5 → ZMod 2 := ![v 1,v 2,v 1,v 2,v 0+v 2]
def form (i : Fin 5) (v : Fin 3 → ZMod 2) : ZMod 2 := charA v i*charB v i

theorem b_ne_zero (i : Fin 5) : b i≠0 := by
  fin_cases i <;> simp [b,roots_ne_zero]
theorem z_ne_zero (i : Fin 5) : z i≠0 := by
  fin_cases i <;> norm_num [z]

theorem norm_identity (i : Fin 5) : (x i+a i)*(x i-a i)=(b i)^2*(z i)^2 := by
  have h0 : (roots 0)^2=(-1 : E) := by simpa [PadicTwo.independentRadicand] using roots_sq_int 0
  have h1 : (roots 1)^2=(2 : E) := by simpa [PadicTwo.independentRadicand] using roots_sq_int 1
  have h2 : (roots 2)^2=(5 : E) := by simpa [PadicTwo.independentRadicand] using roots_sq_int 2
  have h7 : (algebraMap ℚ_[2] E sevenScalar)^2=(-7 : E) := by
    rw [← map_pow,sevenScalar_sq,map_neg,map_ofNat]
  fin_cases i
  · change (1+roots 0)*(1-roots 0)=(roots 1)^2*1^2
    linear_combination -h0-h1
  · change (1+2*roots 0)*(1-2*roots 0)=(roots 2)^2*1^2
    linear_combination -4*h0-h2
  · change (2+roots 1)*(2-roots 1)=(roots 1)^2*1^2
    linear_combination -2*h1
  · change (5+roots 2)*(5-roots 2)=(roots 2)^2*2^2
    linear_combination -5*h2
  · change ((algebraMap ℚ_[2] E sevenScalar)+roots 0*roots 1)*
      ((algebraMap ℚ_[2] E sevenScalar)-roots 0*roots 1)=(roots 0*roots 2)^2*1^2
    linear_combination h7-((roots 1)^2+(roots 2)^2)*h0+h1+h2

theorem alpha_ne_zero (i : Fin 5) : alpha i≠0 :=
  QuadraticNormTwist.alpha_ne_zero _ _ _ _ (b_ne_zero i) (z_ne_zero i) (norm_identity i)

theorem action_a (v : Fin 3 → ZMod 2) (i : Fin 5) :
    signAutomorphism v (a i)=binarySign (charA v i)*a i := by
  fin_cases i
  · exact signAutomorphism_roots v 0
  · change signAutomorphism v (2*roots 0)=binarySign (v 0)*(2*roots 0)
    rw [map_mul,map_ofNat,signAutomorphism_roots]
    ring
  · exact signAutomorphism_roots v 1
  · exact signAutomorphism_roots v 2
  · change signAutomorphism v (roots 0*roots 1)=binarySign (v 0+v 1)*(roots 0*roots 1)
    rw [map_mul,signAutomorphism_roots,signAutomorphism_roots,binarySign_add]
    ring

theorem action_b (v : Fin 3 → ZMod 2) (i : Fin 5) :
    signAutomorphism v (b i)=binarySign (charB v i)*b i := by
  fin_cases i
  · exact signAutomorphism_roots v 1
  · exact signAutomorphism_roots v 2
  · exact signAutomorphism_roots v 1
  · exact signAutomorphism_roots v 2
  · change signAutomorphism v (roots 0*roots 2)=binarySign (v 0+v 2)*(roots 0*roots 2)
    rw [map_mul,signAutomorphism_roots,signAutomorphism_roots,binarySign_add]
    ring

theorem action_x (v : Fin 3 → ZMod 2) (i : Fin 5) : signAutomorphism v (x i)=x i := by
  fin_cases i
  · exact map_one _
  · exact map_one _
  · exact map_ofNat _ 2
  · exact map_ofNat _ 5
  · exact (signAutomorphism v).commutes sevenScalar

theorem action_z (v : Fin 3 → ZMod 2) (i : Fin 5) : signAutomorphism v (z i)=z i := by
  fin_cases i
  · exact map_one _
  · exact map_one _
  · exact map_one _
  · exact map_ofNat _ 2
  · exact map_one _

def multiplier (i : Fin 5) (v : Fin 3 → ZMod 2) : E :=
  QuadraticNormTwist.multiplier (x i) (a i) (b i) (z i) (charA v i)

theorem multiplier_twist (i : Fin 5) (v : Fin 3 → ZMod 2) :
    alpha i*(multiplier i v)^2=signAutomorphism v (alpha i) :=
  QuadraticNormTwist.twist _ _ _ _ _ _ (b_ne_zero i) (z_ne_zero i) (norm_identity i)
    (action_x v i) (action_a v i)

theorem multiplier_norm (i : Fin 5) (v : Fin 3 → ZMod 2) :
    multiplier i v*signAutomorphism v (multiplier i v)=binarySign (form i v) :=
  QuadraticNormTwist.twisted_norm _ _ _ _ _ _ _ (b_ne_zero i) (z_ne_zero i) (norm_identity i)
    (action_x v i) (action_a v i) (action_b v i) (action_z v i)

/-- A kernel-checked test of the five independently specified quadratic forms. -/
theorem forms_detect : ∀ w : Fin 5 → ZMod 2,
    (∀ v : Fin 3 → ZMod 2,∑ i,form i v*w i=0) → w=0 := by decide +kernel

end UnitDistance.PadicTwoNormCatalog
