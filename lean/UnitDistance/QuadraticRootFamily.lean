module

public import UnitDistance.QuadraticRationalSignLift

@[expose] public section
set_option backward.privateInPublic true


/-! Generic extension of actual independent root/sign data by one quadratic root. -/
noncomputable section
namespace UnitDistance.Multiquadratic
open QuadraticAlgebra KummerInvariant

structure RootFamily (r : Fin 7 → ℚ) (n : ℕ) (E : Type*)
    [Field E] [CharZero E] [Algebra ℚ E] where
  roots : Fin 7 → E
  automorphism : (Fin 7 → ZMod 2) → Gal(E/ℚ)
  square : ∀ i, i.val<n → (roots i)^2=(r i : E)
  action : ∀ v i, i.val<n → automorphism v (roots i)=binarySign (v i)*roots i
  involutive : ∀ v, Function.Involutive (automorphism v)

variable {r : Fin 7 → ℚ} {n : ℕ} {E : Type*}
  [Field E] [CharZero E] [Algebra ℚ E]

/-- The genuine root/sign construction for one additional rational radical. -/
def RootFamily.extend (A : RootFamily r n E) (j : Fin 7) (hj : j.val=n)
    [Fact (Nonsquare (r j : E))] [Algebra ℚ (Extension (r j : E))] :
    RootFamily r (n+1) (Extension (r j : E)) where
  roots i := if i=j then omega else algebraMap E (Extension (r j : E)) (A.roots i)
  automorphism v := rationalSignLift (A.automorphism v) (r j) (v j)
  square i hi := by
    by_cases h : i=j
    · subst i
      simp only [ite_true]
      exact root_sq (r j)
    · have hiprev : i.val<n := by
        have hne : i.val≠j.val := fun he => h (Fin.ext he)
        omega
      simp only [if_neg h,← map_pow,A.square i hiprev,map_ratCast]
  action v i hi := by
    by_cases h : i=j
    · subst i
      simp only [ite_true,rationalSignLift_root,Algebra.smul_def,binarySign,map_intCast]
    · have hiprev : i.val<n := by
        have hne : i.val≠j.val := fun he => h (Fin.ext he)
        omega
      simp only [if_neg h,rationalSignLift_algebraMap,A.action v i hiprev,
        map_mul,binarySign,map_intCast]
  involutive v := rationalSignLift_involutive _ (A.involutive v) _ _

end UnitDistance.Multiquadratic
