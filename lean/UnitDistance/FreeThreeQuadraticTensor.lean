module

public import UnitDistance.FreeThreeQuadratic

@[expose] public section
set_option backward.privateInPublic true


/-! Actual degree-two tensor coordinates of the universal quadratic group. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace UnitDistance.FreeThreeQuadratic
open ClassTwo

def second (q : Q) (j i : Fin 3) : F :=
  ![![q.central 0,q.central 3+q.base 0*q.base 1,q.central 4+q.base 0*q.base 2],
    ![q.central 3,q.central 1,q.central 5+q.base 1*q.base 2],
    ![q.central 4,q.central 5,q.central 2]] j i

theorem second_one : ∀j i,second 1 j i=0 := by decide +kernel

theorem second_basis : ∀k j i,second (basis k) j i=0 := by decide +kernel

theorem second_inv_basis : ∀k j i,second (basis k)⁻¹ j i=
    (Pi.single k 1 : V) j*(Pi.single k 1 : V) i := by decide +kernel

/-- The actual tensor product rule, including all quadratic carry terms. -/
theorem second_mul (q r : Q) (j i : Fin 3) :
    second (q*r) j i=second q j i+second r j i+q.base j*r.base i := by
  have hc0 : ∀u v : V,cocycle u v 0=u 0*v 0 := by decide +kernel
  have hc1 : ∀u v : V,cocycle u v 1=u 1*v 1 := by decide +kernel
  have hc2 : ∀u v : V,cocycle u v 2=u 2*v 2 := by decide +kernel
  have hc3 : ∀u v : V,cocycle u v 3=u 1*v 0 := by decide +kernel
  have hc4 : ∀u v : V,cocycle u v 4=u 2*v 0 := by decide +kernel
  have hc5 : ∀u v : V,cocycle u v 5=u 2*v 1 := by decide +kernel
  fin_cases j <;> fin_cases i
  · change (q.central 0+r.central 0+cocycle q.base r.base 0)=(q.central 0)+(r.central 0)+q.base 0*r.base 0
    rw [hc0] <;> ring_nf
  · change (q.central 3+r.central 3+cocycle q.base r.base 3)+(q.base 0+r.base 0)*(q.base 1+r.base 1)=(q.central 3+q.base 0*q.base 1)+(r.central 3+r.base 0*r.base 1)+q.base 0*r.base 1
    rw [hc3] <;> ring_nf
    simp only [show (2 : F)=0 by decide,mul_zero,zero_mul,add_zero]
  · change (q.central 4+r.central 4+cocycle q.base r.base 4)+(q.base 0+r.base 0)*(q.base 2+r.base 2)=(q.central 4+q.base 0*q.base 2)+(r.central 4+r.base 0*r.base 2)+q.base 0*r.base 2
    rw [hc4] <;> ring_nf
    simp only [show (2 : F)=0 by decide,mul_zero,zero_mul,add_zero]
  · change (q.central 3+r.central 3+cocycle q.base r.base 3)=(q.central 3)+(r.central 3)+q.base 1*r.base 0
    rw [hc3] <;> ring_nf
  · change (q.central 1+r.central 1+cocycle q.base r.base 1)=(q.central 1)+(r.central 1)+q.base 1*r.base 1
    rw [hc1] <;> ring_nf
  · change (q.central 5+r.central 5+cocycle q.base r.base 5)+(q.base 1+r.base 1)*(q.base 2+r.base 2)=(q.central 5+q.base 1*q.base 2)+(r.central 5+r.base 1*r.base 2)+q.base 1*r.base 2
    rw [hc5] <;> ring_nf
    simp only [show (2 : F)=0 by decide,mul_zero,zero_mul,add_zero]
  · change (q.central 4+r.central 4+cocycle q.base r.base 4)=(q.central 4)+(r.central 4)+q.base 2*r.base 0
    rw [hc4] <;> ring_nf
  · change (q.central 5+r.central 5+cocycle q.base r.base 5)=(q.central 5)+(r.central 5)+q.base 2*r.base 1
    rw [hc5] <;> ring_nf
  · change (q.central 2+r.central 2+cocycle q.base r.base 2)=(q.central 2)+(r.central 2)+q.base 2*r.base 2
    rw [hc2] <;> ring_nf

def wordDetector : FreeGroup (Fin 3) →* Q := FreeGroup.lift basis

@[simp] theorem wordDetector_of (i : Fin 3) : wordDetector (FreeGroup.of i)=basis i :=
  FreeGroup.lift_apply_of

end UnitDistance.FreeThreeQuadratic
