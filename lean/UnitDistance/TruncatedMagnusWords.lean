module

public import UnitDistance.TruncatedMagnusConjugacyIndex
public import Mathlib.Algebra.CharP.Two

@[expose] public section
set_option backward.privateInPublic true


/-! Literal word coordinates in the actual cubic group. These formulas
hold for arbitrary lifts; their unknown higher coefficients are preserved. -/
noncomputable section
namespace UnitDistance.TruncatedMagnus.Certificate
open Group
open scoped CharTwo

/-- Every actual element of the cubic detector has exponent dividing four. -/
theorem pow_four (g : Group F) : g^4=1 := by
  have h1 : (g^2).first=0 := by ext i; simp [pow_two]
  rw [show (4 : ℕ)=2*2 by decide,pow_mul]
  ext <;> simp [pow_two,h1]

@[simp] theorem square_first (g : Group F) : (g^2).first=0 := by
  ext i
  simp [pow_two]

def squareTensor (x : V₁ F) : V₂ F := fun i j => x i*x j

theorem square_second (g : Group F) : (g^2).second=squareTensor g.first := by
  ext i j
  simp [pow_two,squareTensor]

def commutator (g h : Group F) : Group F := g⁻¹*h⁻¹*g*h

@[simp] theorem commutator_first (g h : Group F) : (commutator g h).first=0 := by
  simp [commutator]

theorem commutator_second (g h : Group F) :
    (commutator g h).second=quadraticBracket g.first h.first := by
  ext i j
  simpa [commutator,quadraticBracket] using Group.commutator_second g⁻¹ h⁻¹ i j

theorem commutator_of_first_zero (g h : Group F) (hg : g.first=0) :
    commutator g h=(⟨0,0,bracket h.first g.second⟩ : Group F) := by
  ext <;> simp [commutator,hg,bracket] <;> ring_nf <;> simp

/-- The literal nested commutator has exactly the displayed cubic tensor. -/
theorem nested_commutator (g h : Group F) :
    commutator (commutator g h) h=
      (⟨0,0,bracket h.first (quadraticBracket g.first h.first)⟩ : Group F) := by
  rw [commutator_of_first_zero _ _ (commutator_first g h),commutator_second]

/-- The specified dyadic cubic is independent of all higher coefficients of its actual lifts. -/
theorem nested_commutator_dyadic (y z : Group F)
    (hy : y.first=vector 53) (hz : z.first=vector 89) :
    commutator (commutator y z) z=(⟨0,0,dyadicCubic⟩ : Group F) := by
  rw [nested_commutator,hy,hz]
  rfl

def tameWord (p : ℕ) (g h : Group F) : Group F := h*g*h⁻¹*(g^p)⁻¹

theorem tameWord_one (g h : Group F) : tameWord 1 g h=h*g*h⁻¹*g⁻¹ := by
  simp [tameWord]

theorem tameWord_three (g h : Group F) : tameWord 3 g h=tameWord 1 g h*g^2 := by
  have hg : g^3=g⁻¹ := eq_inv_iff_mul_eq_one.mpr (by rw [← pow_succ]; exact pow_four g)
  simp only [tameWord,hg,inv_inv,pow_one,pow_two,mul_assoc,inv_mul_cancel_left]

@[simp] theorem tameWord_one_first (g h : Group F) : (tameWord 1 g h).first=0 := by
  simp [tameWord]

theorem tameWord_one_second (g h : Group F) :
    (tameWord 1 g h).second=quadraticBracket g.first h.first := by
  rw [tameWord_one]
  funext i j
  simpa [quadraticBracket,add_comm] using
    Group.commutator_second h g i j

@[simp] theorem tameWord_three_first (g h : Group F) : (tameWord 3 g h).first=0 := by
  rw [tameWord_three,mul_first,tameWord_one_first,square_first,add_zero]

theorem tameWord_three_second (g h : Group F) :
    (tameWord 3 g h).second=quadraticBracket g.first h.first+squareTensor g.first := by
  rw [tameWord_three]
  ext i j
  simp [tameWord_one_second,square_second]

abbrev oddPrimes : Fin 5 → ℕ := ![3,5,7,11,13]
def inertiaVector (i : Fin 5) : V₁ F := vector (![4,8,16,32,64] i)
def frobeniusVector (i : Fin 5) : V₁ F := vector (![43,86,77,83,58] i)
def oddInitial (i : Fin 5) : V₂ F := quadraticBracket (inertiaVector i) (frobeniusVector i)+
  (if oddPrimes i%4=3 then 1 else 0 : F) • squareTensor (inertiaVector i)

theorem tameWord_odd_initial (i : Fin 5) (g h : Group F)
    (hg : g.first=inertiaVector i) (hh : h.first=frobeniusVector i) :
    (tameWord (oddPrimes i) g h).first=0 ∧
    (tameWord (oddPrimes i) g h).second=oddInitial i := by
  have hm : tameWord (oddPrimes i) g h=tameWord (oddPrimes i%4) g h := by
    unfold tameWord
    rw [pow_eq_pow_mod (oddPrimes i) (pow_four g)]
  have hp : oddPrimes i%4=1 ∨ oddPrimes i%4=3 := by
    have hp' : ∀ i : Fin 5, oddPrimes i%4=1 ∨ oddPrimes i%4=3 := by decide +kernel
    exact hp' i
  rw [hm]
  rcases hp with hp | hp
  · rw [hp,tameWord_one_first,tameWord_one_second]
    simp [oddInitial,hp,hg,hh]
  · rw [hp,tameWord_three_first,tameWord_three_second]
    simp [oddInitial,hp,hg,hh]

/-- The sixteen literal independent quadratic initials of the actual cut presentation. -/
def wordInitials : Fin 16 → V₂ F :=
  ![squareTensor (vector 1),oddInitial 0,oddInitial 1,oddInitial 2,oddInitial 3,oddInitial 4,
    squareTensor (vector 4),squareTensor (vector 8),squareTensor (vector 16),
    squareTensor (vector 32),squareTensor (vector 64),squareTensor (vector 2),
    quadraticBracket (vector 2) (vector 53),quadraticBracket (vector 2) (vector 89),
    squareTensor (vector 43),squareTensor (vector 86)]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem wordInitials_certificate : ∀ (i : Fin 16) (j k : Fin 7),
    wordInitials i j k=quadraticRow i j k := by decide +kernel

theorem wordInitials_eq (i : Fin 16) : wordInitials i=quadraticRow i :=
  funext (fun j => funext (wordInitials_certificate i j))

end UnitDistance.TruncatedMagnus.Certificate
