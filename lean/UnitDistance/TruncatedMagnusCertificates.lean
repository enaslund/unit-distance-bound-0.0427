module

public import UnitDistance.TruncatedMagnusQuotient
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Tactic.NormNum

@[expose] public section
set_option backward.privateInPublic true


/-! Small exact dual certificates for the actual truncated Magnus quotient.
Every certificate is checked by Lean's kernel. The linear maps are literal
coordinate sums and are independent of any desired dimension or rank. -/
noncomputable section
open scoped BigOperators
namespace UnitDistance.TruncatedMagnus.Certificate
abbrev F := ZMod 2
abbrev U := Fin 6 → F
abbrev A := Fin 16 → F

def vector (m : ℕ) : V₁ F := fun i => if m.testBit i.val then 1 else 0

def quadraticMasks : Fin 16 → ℕ :=
  ![1,137448112644,35186700059648,70393742491664,144697448206368,257303034994688,65536,16777216,4294967296,1099511627776,281474976710656,256,69256387202,8796634098818,1477558932907,378255086824192]
def quadraticRow (r : Fin 16) : V₂ F :=
  fun i j => if (quadraticMasks r).testBit (7*i.val+j.val) then 1 else 0

def leftSupports : Fin 16 → List (Fin 7 × Fin 7) :=
  ![[(0,0),(0,3)],
    [(0,2)],
    [(0,2),(0,3),(1,2),(1,3),(1,4)],
    [(0,4)],
    [(0,3),(0,5)],
    [(0,1),(0,2),(0,3),(1,2),(1,6)],
    [(0,1),(0,2),(0,3),(1,4),(2,2)],
    [(0,3),(3,3)],
    [(0,1),(0,3),(0,4),(1,4),(4,4)],
    [(0,5),(5,5)],
    [(0,1),(0,3),(1,4),(6,6)],
    [(0,1),(1,1),(1,4)],
    [(0,1),(0,2),(0,3),(1,2),(1,4)],
    [(0,2),(1,2),(1,4)],
    [(0,3)],
    [(0,1),(0,3),(1,4)]]
def secondSupports : Fin 6 → List (Fin 7 × Fin 7) :=
  ![[(0,1),(1,2),(1,3),(2,3),(2,6)],
    [(0,2),(2,5)],
    [(0,3),(1,2),(1,3),(1,4),(2,3)],
    [(0,4),(2,4),(2,6)],
    [(0,5),(1,2),(1,5),(2,5),(2,6)],
    [(0,6)]]
def thirdSupports : Fin 6 → List (Fin 7 × Fin 7 × Fin 7) :=
  ![[(0,1,2),(0,1,4),(0,2,3),(0,3,2),(0,3,6),(0,4,1),(0,4,3),(0,5,1),(0,5,2),(0,5,3),(0,5,4),(0,6,4),(1,2,3),(1,2,6),(1,3,2),(1,3,4),(1,3,6),(1,4,2),(1,4,6),(1,5,3),(1,5,4),(1,6,2),(2,3,4),(2,3,6),(2,4,3),(2,5,4)],
    [(0,1,2),(0,2,1),(0,2,3),(0,2,4),(0,3,1),(0,3,2),(0,4,2),(0,4,3),(0,5,3),(0,6,1),(0,6,4),(1,2,3),(1,3,2),(1,5,2),(1,5,3),(2,4,3),(2,5,4)],
    [(0,1,2),(0,2,1),(0,2,6),(0,3,5),(0,3,6),(0,4,1),(0,5,1),(0,6,1),(0,6,2),(0,6,3),(0,6,5),(1,2,5),(1,2,6),(1,3,2),(1,3,5),(1,3,6),(1,4,5),(1,4,6),(1,5,2),(2,3,5),(2,3,6),(2,5,6)],
    [(0,1,2),(0,1,4),(0,1,6),(0,2,1),(0,2,4),(0,3,2),(0,3,6),(0,4,1),(0,4,2),(0,5,2),(0,5,4),(0,5,6),(0,6,1),(1,2,6),(1,3,2),(1,3,4),(1,4,2),(1,4,6),(1,5,4),(1,5,6),(1,6,2),(2,3,4),(2,5,6)],
    [(0,1,2),(0,1,4),(0,1,6),(0,2,1),(0,3,6),(0,4,1),(0,4,2),(0,5,4),(0,5,6),(0,6,1),(0,6,3),(0,6,4),(1,2,6),(1,3,2),(1,3,4),(1,4,2),(1,4,6),(1,5,4),(1,5,6),(1,6,2),(2,3,4),(2,5,4),(2,5,6)],
    [(0,1,2),(0,1,6),(0,2,1),(0,2,3),(0,2,4),(0,3,2),(0,3,5),(0,3,6),(0,4,2),(0,4,3),(0,5,3),(0,5,6),(0,6,1),(0,6,2),(0,6,4),(0,6,5),(1,2,3),(1,2,5),(1,2,6),(1,3,2),(1,3,5),(1,4,2),(1,4,5),(1,4,6),(1,5,3),(1,5,6),(1,6,2),(2,3,5),(2,4,3),(2,5,4),(2,5,6)]]

def coordinateSum₂ {n : ℕ} (s : Fin n → List (Fin 7 × Fin 7)) :
    V₂ F →ₗ[F] (Fin n → F) where
  toFun y k := ((s k).map fun p => y p.1 p.2).sum
  map_add' y z := by
    funext k
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    induction s k with
    | nil => simp
    | cons p l ih => simp only [List.map_cons,List.sum_cons,Pi.add_apply,ih]; abel
  map_smul' r y := by
    funext k
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    induction s k with
    | nil => simp
    | cons p l ih => simp only [List.map_cons,List.sum_cons,Pi.smul_apply,smul_eq_mul,ih,
        RingHom.id_apply,mul_add]

def coordinateSum₃ {n : ℕ} (s : Fin n → List (Fin 7 × Fin 7 × Fin 7)) :
    V₃ F →ₗ[F] (Fin n → F) where
  toFun z k := ((s k).map fun p => z p.1 p.2.1 p.2.2).sum
  map_add' y z := by
    funext k
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    induction s k with
    | nil => simp
    | cons p l ih => simp only [List.map_cons,List.sum_cons,Pi.add_apply,ih]; abel
  map_smul' r y := by
    funext k
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    induction s k with
    | nil => simp
    | cons p l ih => simp only [List.map_cons,List.sum_cons,Pi.smul_apply,smul_eq_mul,ih,
        RingHom.id_apply,mul_add]

def leftInverse : V₂ F →ₗ[F] A := coordinateSum₂ leftSupports
def secondDetector : V₂ F →ₗ[F] U := coordinateSum₂ secondSupports
def thirdDetector : V₃ F →ₗ[F] U := coordinateSum₃ thirdSupports

def e (i : Fin 7) : V₁ F := Pi.single i 1

def quadraticBracket (x y : V₁ F) : V₂ F :=
  fun i j => x i*y j-y i*x j

def selectedPairs : Fin 6 → Fin 7 × Fin 7 := ![(1,2),(1,3),(1,4),(2,3),(2,4),(2,6)]
def selectedQuadratic (j : Fin 6) : V₂ F :=
  quadraticBracket (e (selectedPairs j).1) (e (selectedPairs j).2)

def dyadicCubic : V₃ F := bracket (vector 89) (quadraticBracket (vector 53) (vector 89))

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

theorem leftInverse_row_certificate : ∀ (i j : Fin 16),
    leftInverse (quadraticRow i) j=(Pi.single i (1 : F) : A) j := by decide +kernel

theorem second_row_certificate : ∀ (i : Fin 16) (j : Fin 6),
    secondDetector (quadraticRow i) j=0 := by decide +kernel

theorem second_detect_certificate : ∀ (i j : Fin 6),
    secondDetector (quadraticBracket (e 0) (e i.succ)) j=
      (Pi.single i (1 : F) : U) j := by decide +kernel

theorem third_row_certificate : ∀ (i : Fin 16) (j : Fin 7) (k : Fin 6),
    thirdDetector (bracket (e j) (quadraticRow i)) k=0 := by decide +kernel

theorem third_dyadic_certificate : ∀ (k : Fin 6),
    thirdDetector dyadicCubic k=0 := by decide +kernel

theorem third_detect_certificate : ∀ (i j : Fin 6),
    thirdDetector (bracket (e 0) (selectedQuadratic i)) j=
      (Pi.single i (1 : F) : U) j := by decide +kernel

end UnitDistance.TruncatedMagnus.Certificate
