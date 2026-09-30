module

public import UnitDistance.FreeThreeQuadratic
public import UnitDistance.DyadicGroup

@[expose] public section
set_option backward.privateInPublic true


/-! The dyadic order-thirty-two quotient of the universal quadratic detector.
The original local relation is killed by an actual homomorphism. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace UnitDistance.FreeThreeDyadicQuotient
open ClassTwo
abbrev Q := FreeThreeQuadratic.Q

def value (q : Q) : Dyadic.D :=
  ⟨q.base 1,q.base 0+q.base 2,
    ((q.base 2).val+2*(q.central 2).val : ZMod 4),q.central 2+q.central 4⟩

theorem cocycle_two (u v : FreeThreeQuadratic.V) :
    FreeThreeQuadratic.cocycle u v 2=u 2*v 2 := by
  have h : ∀u v : FreeThreeQuadratic.V,FreeThreeQuadratic.cocycle u v 2=u 2*v 2 := by decide +kernel
  exact h u v

theorem cocycle_four (u v : FreeThreeQuadratic.V) :
    FreeThreeQuadratic.cocycle u v 4=u 2*v 0 := by
  have h : ∀u v : FreeThreeQuadratic.V,FreeThreeQuadratic.cocycle u v 4=u 2*v 0 := by decide +kernel
  exact h u v

def quotient : Q →* Dyadic.D where
  toFun := value
  map_one' := by decide +kernel
  map_mul' q r := by
    apply Dyadic.D.ext
    · rfl
    · change (q.base 0+r.base 0)+(q.base 2+r.base 2)=
        (q.base 0+q.base 2)+(r.base 0+r.base 2)
      ring
    · change (((q.base 2+r.base 2).val : ZMod 4)+
        2*(q.central 2+r.central 2+FreeThreeQuadratic.cocycle q.base r.base 2).val)=_
      rw [cocycle_two]
      have h : ∀a b c d : ZMod 2,
          (((a+b).val : ZMod 4)+2*(c+d+a*b).val)=
            (a.val+2*c.val)+(b.val+2*d.val) := by decide +kernel
      exact h _ _ _ _
    · change (q.central 2+r.central 2+FreeThreeQuadratic.cocycle q.base r.base 2)+
        (q.central 4+r.central 4+FreeThreeQuadratic.cocycle q.base r.base 4)=
        (q.central 2+q.central 4)+(r.central 2+r.central 4)+
          Dyadic.parity (((q.base 2).val : ZMod 4)+2*(q.central 2).val)*(r.base 0+r.base 2)
      have hp : ∀a b : ZMod 2,Dyadic.parity ((a.val : ZMod 4)+2*b.val)=a := by decide +kernel
      rw [cocycle_two,cocycle_four,hp]
      ring

@[simp] theorem quotient_basis (i : Fin 3) :
    quotient (FreeThreeQuadratic.basis i)=![Dyadic.D.y,Dyadic.D.x,Dyadic.D.y*Dyadic.D.z] i := by
  have h : ∀i : Fin 3,quotient (FreeThreeQuadratic.basis i)=
      ![Dyadic.D.y,Dyadic.D.x,Dyadic.D.y*Dyadic.D.z] i := by decide +kernel
  exact h i

@[simp] theorem quotient_relation : quotient FreeThreeQuadratic.relation=1 := by decide +kernel

theorem base_zero_of_quotient_eq_one (q : Q) (h : quotient q=1) : q.base=0 := by
  have h1 : q.base 1=0 := congrArg Dyadic.D.a h
  have h02 : q.base 0+q.base 2=0 := congrArg Dyadic.D.b h
  have h2 : q.base 2=0 := by
    have hh : ∀a b : ZMod 2,(a.val+2*b.val : ZMod 4)=0 → a=0 := by decide +kernel
    exact hh _ _ (congrArg Dyadic.D.c h)
  funext i
  fin_cases i
  · change q.base 0=0
    simpa only [h2,add_zero] using h02
  · exact h1
  · exact h2

end UnitDistance.FreeThreeDyadicQuotient
