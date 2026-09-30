module

public import UnitDistance.UniversalQuadraticGroup

@[expose] public section
set_option backward.privateInPublic true


/-! Exact images of tame odd relators in the actual universal quadratic
detector, independent of the central coordinates chosen for the lifts. -/
noncomputable section
namespace UnitDistance.UniversalQuadratic
open ClassTwo

theorem pow_four (g : Q) : g^4=1 := by
  change g^(2*2)=1
  rw [pow_mul,GroupModel.square_coordinates,GroupModel.square_coordinates]
  apply GroupModel.ext <;> simp

/-- The local tame word for an odd rational prime. -/
def tameWord (p : ℕ) (inertia frobenius : Q) : Q :=
  frobenius*inertia*frobenius⁻¹*(inertia^p)⁻¹

theorem tameWord_one (g h : Q) :
    tameWord 1 g h=(⟨0,bracketVector g.base h.base⟩ : Q) := by
  have he := GroupModel.commutator_coordinates cocycle (h⁻¹) (g⁻¹)
  simp only [inv_inv] at he
  change h*g*h⁻¹*(g^1)⁻¹=_
  rw [pow_one,he]
  apply GroupModel.ext
  · rfl
  · funext i
    simp [bracketVector,GroupModel.inv_base,map_neg,LinearMap.neg_apply,
      sub_eq_add_neg,ZMod.neg_eq_self_mod_two,add_comm]

theorem tameWord_three (g h : Q) :
    tameWord 3 g h=(⟨0,bracketVector g.base h.base+squareVector g.base⟩ : Q) := by
  have hg : g^3=g⁻¹ := eq_inv_iff_mul_eq_one.mpr (by
    rw [← pow_succ]
    exact pow_four g)
  change h*g*h⁻¹*(g^3)⁻¹=_
  rw [hg,inv_inv]
  calc
    h*g*h⁻¹*g=(tameWord 1 g h)*(g^2) := by
      simp only [tameWord,pow_one,pow_two,mul_assoc,inv_mul_cancel_left]
    _ = (⟨0,bracketVector g.base h.base⟩ : Q)*⟨0,squareVector g.base⟩ := by
      rw [tameWord_one,GroupModel.square_coordinates]
      rfl
    _ = _ := by ext <;> simp

abbrev oddPrimes : Fin 5 → ℕ := ![3,5,7,11,13]
def oddIndex (i : Fin 5) : Fin 6 := ⟨i.val+1,by omega⟩

theorem oddPrime_mod_four (i : Fin 5) : oddPrimes i%4=1 ∨ oddPrimes i%4=3 := by
  have h : ∀ i : Fin 5, oddPrimes i%4=1 ∨ oddPrimes i%4=3 := by decide +kernel
  exact h i

theorem odd_square_coefficient (i : Fin 5) :
    squareCoefficients (oddIndex i)=if oddPrimes i%4=3 then 1 else 0 := by
  have h : ∀ i : Fin 5,
      squareCoefficients (oddIndex i)=if oddPrimes i%4=3 then 1 else 0 := by decide +kernel
  exact h i

/-- For arbitrary actual lifts with the specified elementary images, the
actual tame relator maps to the independently checked original central row. -/
theorem tameWord_originalInitial (i : Fin 5) (g h : Q)
    (hg : g.base=inertiaVectors (oddIndex i))
    (hh : h.base=frobeniusVectors (oddIndex i)) :
    tameWord (oddPrimes i) g h=(⟨0,originalInitial (oddIndex i)⟩ : Q) := by
  have hm : tameWord (oddPrimes i) g h=tameWord (oddPrimes i%4) g h := by
    unfold tameWord
    rw [pow_eq_pow_mod (oddPrimes i) (pow_four g)]
  rw [hm]
  rcases oddPrime_mod_four i with hp | hp
  · rw [hp,tameWord_one]
    have hc : squareCoefficients (oddIndex i)=0 := by rw [odd_square_coefficient,hp]; decide
    simp [originalInitial,hc,hg,hh]
  · rw [hp,tameWord_three]
    have hc : squareCoefficients (oddIndex i)=1 := by rw [odd_square_coefficient,hp]; decide
    simp [originalInitial,hc,hg,hh]

/-- The actual infinity square has the first original central row. -/
theorem infinitySquare_originalInitial (g : Q) (hg : g.base=inertiaVectors 0) :
    g^2=(⟨0,originalInitial 0⟩ : Q) := by
  rw [GroupModel.square_coordinates]
  apply GroupModel.ext
  · rfl
  · have hf : frobeniusVectors (0 : Fin 6)=(0 : V) := by decide +kernel
    simp [originalInitial,bracketVector,hf,squareCoefficients,squareVector,hg]

/-- The actual odd tame-word images evaluate to the required dual matrix. -/
theorem tameWord_coordinate (i : Fin 5) (j : Fin 6) (g h : Q)
    (hg : g.base=inertiaVectors (oddIndex i))
    (hh : h.base=frobeniusVectors (oddIndex i)) :
    OriginalQuadratic.coordinate j (tameWord (oddPrimes i) g h).central =
      if j=oddIndex i then 1 else 0 := by
  rw [tameWord_originalInitial i g h hg hh]
  exact original_coordinate j (oddIndex i)

end UnitDistance.UniversalQuadratic
