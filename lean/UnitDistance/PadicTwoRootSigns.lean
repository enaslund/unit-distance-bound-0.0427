module

public import UnitDistance.PadicTwoFiniteRestriction

@[expose] public section
set_option backward.privateInPublic true


/-! Actual Q₂ root signs on the seven rational genus radicands. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace UnitDistance.PadicTwoRootSigns
open PadicTwoMaximalProTwo Multiquadratic

def localRoot (i : Fin 3) : Closure := genusEmbedding (PadicTwoGenus.roots i)

theorem localRoot_sq (i : Fin 3) : (localRoot i)^2=(PadicTwo.independentRadicand i : Closure) := by
  rw [localRoot,←map_pow,PadicTwoGenus.roots_sq_int,map_intCast]

theorem localRoot_ne_zero (i : Fin 3) : localRoot i≠0 :=
  (map_ne_zero genusEmbedding).mpr (PadicTwoGenus.roots_ne_zero i)

theorem localRoot_action (σ : AbsoluteGroup) (i : Fin 3) :
    σ (localRoot i)=binarySign ((absoluteSigns σ).toAdd i)*localRoot i := by
  let τ := GaloisEmbedding.restriction genusEmbedding σ
  have h := PadicTwoGenus.signAutomorphism_roots (PadicTwoGenus.signEquiv τ).toAdd i
  rw [show PadicTwoGenus.signAutomorphism (PadicTwoGenus.signEquiv τ).toAdd=τ from
    PadicTwoGenus.signEquiv.symm_apply_apply τ] at h
  rw [localRoot,←GaloisEmbedding.restriction_commutes genusEmbedding σ]
  change genusEmbedding (τ (PadicTwoGenus.roots i))=_
  rw [h,map_mul]
  simp only [binarySign,map_intCast]
  rfl

theorem fixed_of_square_base (σ : AbsoluteGroup) (x : Closure) (a : ℚ_[2])
    (hx : x^2=algebraMap ℚ_[2] Closure a) (ha : IsSquare a) : σ x=x := by
  obtain ⟨b,hb⟩ := ha
  have he : x^2=(algebraMap ℚ_[2] Closure b)^2 := by rw [hx,hb,map_mul,pow_two]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with h | h
  · rw [h,σ.commutes]
  · rw [h,map_neg,σ.commutes]

theorem transfer_sign (σ : AbsoluteGroup) (x y : Closure) (a : ℚ_[2])
    (hy : y≠0) (hxy : (x*y)^2=algebraMap ℚ_[2] Closure a) (ha : IsSquare a)
    (v : ZMod 2) (hσy : σ y=binarySign v*y) : σ x=binarySign v*x := by
  have h := fixed_of_square_base σ (x*y) a hxy ha
  rw [map_mul,hσy,←mul_assoc] at h
  have he : σ x*binarySign v=x := mul_right_cancel₀ hy h
  calc
    σ x=σ x*(binarySign v)^2 := by rw [binarySign_sq,mul_one]
    _=(σ x*binarySign v)*binarySign v := by ring
    _=binarySign v*x := by rw [he,mul_comm]

/-- Actual restriction matrix for the seven rational radicands. -/
def signsVector (v : Fin 3 → ZMod 2) : Fin 7 → ZMod 2 :=
  ![v 0,v 1,v 0+v 2,v 2,v 0,v 0+v 2,v 2]

abbrev globalRadicands : Fin 7 → ℤ := ![-1,2,3,5,7,11,13]

/-- Every actual choice of the seven roots has the same local character matrix. -/
theorem root_action (σ : AbsoluteGroup) (a : Fin 7 → Closure)
    (ha : ∀i,(a i)^2=(globalRadicands i : Closure)) (i : Fin 7) :
    σ (a i)=binarySign (signsVector (absoluteSigns σ).toAdd i)*a i := by
  let v := (absoluteSigns σ).toAdd
  have hs (j : Fin 3) := localRoot_sq j
  have hact (j : Fin 3) := localRoot_action σ j
  have hprod : σ (localRoot 0*localRoot 2)=binarySign (v 0+v 2)*(localRoot 0*localRoot 2) := by
    rw [map_mul,hact,hact,binarySign_add]
    ring
  have ht (j : Fin 7) (k : Fin 3) (he : globalRadicands j=PadicTwo.independentRadicand k) :
      σ (a j)=binarySign (v k)*a j := by
    apply transfer_sign σ (a j) (localRoot k) ((globalRadicands j : ℚ_[2])^2)
      (localRoot_ne_zero k) ?_ (by exact ⟨globalRadicands j,by rw [pow_two]⟩) _ (hact k)
    rw [mul_pow,ha,hs,←he,map_pow,map_intCast,pow_two]
  have h02 (j : Fin 7) (n : ℤ) (hn : globalRadicands j*(-5)=n)
      (hsq : IsSquare (n : ℚ_[2])) : σ (a j)=binarySign (v 0+v 2)*a j := by
    apply transfer_sign σ (a j) (localRoot 0*localRoot 2) n
      (mul_ne_zero (localRoot_ne_zero 0) (localRoot_ne_zero 2)) ?_ hsq _ hprod
    rw [mul_pow,mul_pow,ha,hs,hs,map_intCast]
    rw [show PadicTwo.independentRadicand 0=(-1 : ℤ) from rfl,
      show PadicTwo.independentRadicand 2=(5 : ℤ) from rfl]
    push_cast
    change (globalRadicands j : Closure)*((-1)*5)=(n : Closure)
    have h := congrArg (fun z : ℤ => (z : Closure)) hn
    push_cast at h
    convert h using 1 <;> ring
  fin_cases i
  · exact ht 0 0 rfl
  · exact ht 1 1 rfl
  · exact h02 2 (-15) rfl PadicTwo.genus_relations.1
  · exact ht 3 2 rfl
  · apply transfer_sign σ (a 4) (localRoot 0) (-7) (localRoot_ne_zero 0) ?_
      PadicTwo.genus_relations.2.1 _ (hact 0)
    rw [mul_pow,ha,hs,map_neg,map_ofNat]
    rw [show globalRadicands 4=(7 : ℤ) from rfl,
      show PadicTwo.independentRadicand 0=(-1 : ℤ) from rfl]
    norm_num
  · exact h02 5 (-55) rfl PadicTwo.genus_relations.2.2.1
  · apply transfer_sign σ (a 6) (localRoot 2) 65 (localRoot_ne_zero 2) ?_
      PadicTwo.genus_relations.2.2.2 _ (hact 2)
    rw [mul_pow,ha,hs,map_ofNat]
    rw [show globalRadicands 6=(13 : ℤ) from rfl,
      show PadicTwo.independentRadicand 2=(5 : ℤ) from rfl]
    norm_num

end UnitDistance.PadicTwoRootSigns
