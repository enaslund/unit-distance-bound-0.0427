module

public import UnitDistance.Sqrt241.GroupData.Data
public import UnitDistance.GroupAugmentationClassTwo
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.StdBasis

@[expose] public section
set_option backward.privateInPublic true


/-!
# Binary vectors, matrices and bilinear laws from bit masks

Small generic helpers for the finite data of the tower over `ℚ(√241)`:
vectors, linear maps, linear functionals and bilinear laws over `F₂`
given by bit masks. They are ordinary linear maps; no property of the masks
is assumed.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.Sqrt241.GroupData

abbrev F := ZMod 2

/-- The vector whose coordinate `i` is bit `i` of `mask`. -/
def bits (n mask : ℕ) : Fin n → F := fun i => if mask.testBit i.val then 1 else 0

/-- The linear map sending the basis vector `j` to `bits n (columns j)`. -/
def columnMap (m n : ℕ) (columns : Fin m → ℕ) : (Fin m → F) →ₗ[F] (Fin n → F) where
  toFun v := ∑ i, v i • bits n (columns i)
  map_add' v w := by simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' r v := by
    simp only [Pi.smul_apply,Finset.smul_sum,smul_smul,smul_eq_mul,RingHom.id_apply]

theorem columnMap_apply (m n : ℕ) (columns : Fin m → ℕ) (v : Fin m → F) :
    columnMap m n columns v = ∑ i, v i • bits n (columns i) := rfl

/-- The linear functional `v ↦ ∑_{i ∈ mask} v i`. -/
def maskFunctional (n mask : ℕ) : (Fin n → F) →ₗ[F] F where
  toFun v := ∑ i, bits n mask i * v i
  map_add' v w := by simp only [Pi.add_apply,mul_add,Finset.sum_add_distrib]
  map_smul' r v := by
    simp only [Pi.smul_apply,smul_eq_mul,Finset.mul_sum,RingHom.id_apply]
    exact Finset.sum_congr rfl (fun i _ => by ring)

theorem maskFunctional_apply (n mask : ℕ) (v : Fin n → F) :
    maskFunctional n mask v = ∑ i, bits n mask i * v i := rfl

/-- The bilinear law `(v, w) ↦ ∑ᵢ ∑ⱼ vᵢ wⱼ • bits n (masks i j)`. -/
def bilinearOfMasks (m n : ℕ) (masks : Fin m → Fin m → ℕ) :
    (Fin m → F) →ₗ[F] (Fin m → F) →ₗ[F] (Fin n → F) where
  toFun v :=
    { toFun := fun w => ∑ i, ∑ j, (v i*w j) • bits n (masks i j)
      map_add' w w' := by
        simp only [Pi.add_apply,mul_add,add_smul,Finset.sum_add_distrib]
      map_smul' r w := by
        simp only [Pi.smul_apply,smul_eq_mul,Finset.smul_sum,smul_smul]
        simp only [RingHom.id_apply,mul_left_comm] }
  map_add' v v' := by
    apply LinearMap.ext
    intro w
    change (∑ i, ∑ j, ((v i+v' i)*w j) • bits n (masks i j)) = _
    simp only [add_mul,add_smul,Finset.sum_add_distrib]
    rfl
  map_smul' r v := by
    apply LinearMap.ext
    intro w
    change (∑ i, ∑ j, ((r*v i)*w j) • bits n (masks i j)) =
      r • (∑ i, ∑ j, (v i*w j) • bits n (masks i j))
    simp only [Finset.smul_sum,smul_smul,mul_assoc]

theorem bilinearOfMasks_apply (m n : ℕ) (masks : Fin m → Fin m → ℕ) (v w : Fin m → F) :
    bilinearOfMasks m n masks v w = ∑ i, ∑ j, (v i*w j) • bits n (masks i j) := rfl

/-- Two linear maps out of `Fin m → F` agree once they agree on basis vectors. -/
theorem linearMap_ext_single {m : ℕ} {M : Type*} [AddCommGroup M] [Module F M]
    {f g : (Fin m → F) →ₗ[F] M} (h : ∀ j, f (Pi.single j 1) = g (Pi.single j 1)) : f = g := by
  apply (Pi.basisFun F (Fin m)).ext
  intro j
  simpa only [Pi.basisFun_apply] using h j

theorem add_self_eq_zero {m : ℕ} (v : Fin m → F) : v + v = 0 := by
  funext i
  have h : ∀ a : F, a + a = 0 := by decide
  exact h (v i)

theorem neg_eq_self {m : ℕ} (v : Fin m → F) : -v = v := by
  funext i
  have h : ∀ a : F, -a = a := by decide
  exact h (v i)

theorem sub_eq_add {m : ℕ} (v w : Fin m → F) : v - w = v + w := by
  rw [sub_eq_add_neg,neg_eq_self]

end UnitDistance.Sqrt241.GroupData

namespace UnitDistance.Sqrt241.GroupData

/-! ### The elementary vectors of the local generators (construction.md §3.4) -/

abbrev V := Fin 8 → F

def conjVector (i : Fin 2) : V := bits 8 (conjMask i)
def tameInertiaVector (q : Fin 4) : V := bits 8 (tameInertiaMask q)
def tameFrobeniusVector (q : Fin 4) : V := bits 8 (tameFrobeniusMask q)
def dyadicAVector (P : Fin 2) : V := bits 8 (dyadicAMask P)
def dyadicBVector (P : Fin 2) : V := bits 8 (dyadicBMask P)
def dyadicCVector (P : Fin 2) : V := bits 8 (dyadicCMask P)
def dyadicXVector (P : Fin 2) : V := bits 8 (dyadicXMask P)
def dyadicYVector (P : Fin 2) : V := bits 8 (dyadicYMask P)
def dyadicZVector (P : Fin 2) : V := bits 8 (dyadicZMask P)
def capVector (k : Fin 3) : V := bits 8 (capMask k)

/-- `x = b`, `y = a`, `z = a + c` in elementary coordinates. -/
theorem dyadic_vectors_certificate : ∀ (P : Fin 2) (k : Fin 8),
    dyadicXVector P k = dyadicBVector P k ∧ dyadicYVector P k = dyadicAVector P k ∧
      dyadicZVector P k = dyadicAVector P k + dyadicCVector P k := by
  decide +kernel

theorem dyadicXVector_eq (P : Fin 2) : dyadicXVector P = dyadicBVector P :=
  funext fun k => (dyadic_vectors_certificate P k).1
theorem dyadicYVector_eq (P : Fin 2) : dyadicYVector P = dyadicAVector P :=
  funext fun k => (dyadic_vectors_certificate P k).2.1
theorem dyadicZVector_eq (P : Fin 2) : dyadicZVector P = dyadicAVector P + dyadicCVector P :=
  funext fun k => (dyadic_vectors_certificate P k).2.2

end UnitDistance.Sqrt241.GroupData
