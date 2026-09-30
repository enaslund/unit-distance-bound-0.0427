module

public import UnitDistance.Sqrt241.GroupData.MagnusConjugacy
public import UnitDistance.Sqrt241.GroupData.Basic

@[expose] public section
set_option backward.privateInPublic true


/-!
# Truncated Magnus certificates over `ℚ(√241)`

The 21 quadratic cut rows (Magnus tensors of the cut initials), a left
inverse, a second-layer detector with seven outputs (dual to `[eᵢ, c₁]`,
`i = 1..7`) and a third-layer detector with eight outputs (dual to
`[c₁, [e_p, e_q]]` for eight generator pairs), for the conjugation vector
`c₁ = 10111010`. All identities are checked by `decide +kernel`; the data are
the generated masks of `Data.lean`. The third detector also kills both dyadic
cubics `[z_P, [y_P, z_P]]`. This gives `data : CutData 8 21 7 8`, whence the
class of `c₁` has at least `2^15` elements in every cut quotient.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.Sqrt241.MagnusB
open Magnus GroupData

/-- The 21 quadratic rows as Magnus tensors. -/
def row (r : Fin 21) : V₂ 8 Magnus.F :=
  fun i j => if (quadraticRowMasks r).testBit (8*i.val+j.val) then 1 else 0

def coordinateSum₂ {m : ℕ} (s : Fin m → List (Fin 8 × Fin 8)) :
    V₂ 8 Magnus.F →ₗ[Magnus.F] (Fin m → Magnus.F) where
  toFun y k := ((s k).map fun p => y p.1 p.2).sum
  map_add' y z := by
    funext k
    simp only [Pi.add_apply]
    induction s k with
    | nil => simp
    | cons p l ih => simp only [List.map_cons,List.sum_cons,ih]; abel
  map_smul' r y := by
    funext k
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    induction s k with
    | nil => simp
    | cons p l ih => simp only [List.map_cons,List.sum_cons,ih,mul_add]

def coordinateSum₃ {m : ℕ} (s : Fin m → List (Fin 8 × Fin 8 × Fin 8)) :
    V₃ 8 Magnus.F →ₗ[Magnus.F] (Fin m → Magnus.F) where
  toFun z k := ((s k).map fun p => z p.1 p.2.1 p.2.2).sum
  map_add' y z := by
    funext k
    simp only [Pi.add_apply]
    induction s k with
    | nil => simp
    | cons p l ih => simp only [List.map_cons,List.sum_cons,ih]; abel
  map_smul' r y := by
    funext k
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    induction s k with
    | nil => simp
    | cons p l ih => simp only [List.map_cons,List.sum_cons,ih,mul_add]

def leftInverse : V₂ 8 Magnus.F →ₗ[Magnus.F] (Fin 21 → Magnus.F) := coordinateSum₂ leftSupports
def secondDetector : V₂ 8 Magnus.F →ₗ[Magnus.F] (Fin 7 → Magnus.F) := coordinateSum₂ secondSupports
def thirdDetector : V₃ 8 Magnus.F →ₗ[Magnus.F] (Fin 8 → Magnus.F) := coordinateSum₃ thirdSupports

/-- The conjugation vector `c₁ = 10111010`. -/
def cVec : V₁ 8 Magnus.F := conjVector 0


theorem leftInverse_row_certificate : ∀ (i j : Fin 21),
    leftInverse (row i) j = (Pi.single i (1 : Magnus.F) : Fin 21 → Magnus.F) j := by
  decide +kernel

theorem second_row_certificate : ∀ (i : Fin 21) (j : Fin 7), secondDetector (row i) j = 0 := by
  decide +kernel

theorem second_detect_certificate : ∀ (i j : Fin 7),
    secondDetector (quadraticBracket (e (baseIndex i)) cVec) j =
      (Pi.single i (1 : Magnus.F) : Fin 7 → Magnus.F) j := by
  decide +kernel

/-- Checked one row at a time, so that every kernel reduction stays small. -/
theorem third_row_certificate : ∀ (i : Fin 21) (j k : Fin 8),
    thirdDetector (bracket (e j) (row i)) k = 0 := by
  intro i
  fin_cases i <;> decide +kernel

theorem third_detect_certificate : ∀ (i j : Fin 8),
    thirdDetector (bracket cVec (quadraticBracket (e (selectedPairs i).1) (e (selectedPairs i).2))) j =
      (Pi.single i (1 : Magnus.F) : Fin 8 → Magnus.F) j := by
  decide +kernel

theorem third_dyadic_certificate : ∀ (P : Fin 2) (k : Fin 8),
    thirdDetector (bracket (dyadicZVector P)
      (quadraticBracket (dyadicYVector P) (dyadicZVector P))) k = 0 := by
  decide +kernel

/-- The certificate data for `B`: 21 rows, `U₂ = F₂⁷`, `U₃ = F₂⁸`, vector `c₁`. -/
def data : CutData 8 21 7 8 where
  row := row
  leftInverse := leftInverse
  second := secondDetector
  third := thirdDetector
  baseIndex := baseIndex
  pairs := selectedPairs
  cVec := cVec
  leftInverse_row i := funext (leftInverse_row_certificate i)
  second_row i := funext (second_row_certificate i)
  third_row i j := funext (third_row_certificate i j)
  second_detect i := funext (second_detect_certificate i)
  third_detect i := funext (third_detect_certificate i)

theorem third_dyadic (P : Fin 2) :
    data.third (bracket (dyadicZVector P) (quadraticBracket (dyadicYVector P) (dyadicZVector P))) = 0 :=
  funext (third_dyadic_certificate P)

end UnitDistance.Sqrt241.MagnusB
