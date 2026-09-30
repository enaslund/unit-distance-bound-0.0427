module

public import UnitDistance.GroupAugmentationInducedHilbert

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual induced-row Hilbert values

The actual annihilator of an induced local row decomposes in the genuine
filtered local coordinates. Strict induction of the row then subtracts its
actual annihilator cost, giving the exact row-image value in the shifted
ambient derivative module.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.GroupAugmentation
open FilteredHilbert
local notation "F" => ZMod 2
variable (D P T : Type*) [Group D] [Group P] [Finite D] [Finite P] [Fintype T]
variable {ι : Type*} [Fintype ι]
variable (f : D →* P) (e : A F P ≃ₗ[F] (T →₀ A F D)) (w : T → ℕ)
variable (hmul : ∀ a b t, e (a*induced F D f b) t = e a t*b)
variable (hpower : ∀ a n, a ∈ power F P n ↔ ∀ t, e a t ∈ power F D (n-w t))
variable (c : ι → A F D)

/-- The actual row annihilator with its induced augmentation filtration. -/
def rowKernelPower (n : ℕ) : Submodule F (A F D) :=
  (coefficientRow F D c).ker ⊓ power F D n

include hmul in
/-- Actual row annihilation is equivalent to annihilation in every actual
local coordinate, including all higher-order coefficients. -/
theorem induced_rowKernel_coordinates (a : A F P) :
    a ∈ (coefficientRow F P (fun i => induced F D f (c i))).ker ↔
      ∀ t, e a t ∈ (coefficientRow F D c).ker := by
  constructor
  · intro ha t
    apply LinearMap.mem_ker.mpr
    funext i
    have hi := congrFun (LinearMap.mem_ker.mp ha) i
    change a*induced F D f (c i) = 0 at hi
    change e a t*c i = 0
    rw [← hmul,hi,map_zero,Finsupp.zero_apply]
  · intro ha
    apply LinearMap.mem_ker.mpr
    funext i
    apply e.injective
    apply Finsupp.ext
    intro t
    change e (a*induced F D f (c i)) t = e 0 t
    rw [hmul,map_zero,Finsupp.zero_apply]
    exact congrFun (LinearMap.mem_ker.mp (ha t)) i

include hmul hpower in
/-- The actual induced annihilator filtration becomes the product of the
shifted actual local annihilator filtrations. -/
theorem induced_rowKernelPower_coordinates (n : ℕ) :
    ((coefficientRow F P (fun i => induced F D f (c i))).ker ⊓ power F P n).map
      (finiteBlockCoordinates D P T e).toLinearMap =
      piSpace F (A F D) (fun t => rowKernelPower D c (n-w t)) := by
  ext b
  constructor
  · rintro ⟨a,⟨ha,hap⟩,rfl⟩
    apply (mem_piSpace F (A F D) _ _).mpr
    intro t
    exact ⟨(induced_rowKernel_coordinates D P T f e hmul c a).mp ha t,(hpower a n).mp hap t⟩
  · intro hb
    have ht := (mem_piSpace F (A F D) _ b).mp hb
    let a := (finiteBlockCoordinates D P T e).symm b
    have ha (t : T) : e a t = b t :=
      congrFun ((finiteBlockCoordinates D P T e).apply_symm_apply b) t
    refine ⟨a,⟨?_,?_⟩,by simp [a]⟩
    · apply (induced_rowKernel_coordinates D P T f e hmul c a).mpr
      intro t
      rw [ha]
      exact (ht t).1
    · apply (hpower a n).mpr
      intro t
      rw [ha]
      exact (ht t).2

variable (hD : IsPGroup 2 D) (hP : IsPGroup 2 P)

include hD in
theorem rowKernelPower_nilpotent (n : ℕ) (hn : Nat.card D ≤ n) : rowKernelPower D c n = ⊥ := by
  rw [rowKernelPower,hilbert_power_vanishes_after_card D hD n hn,inf_bot_eq]

include hD hmul hpower in
/-- Exact induction of the actual row-annihilator Hilbert value. -/
theorem value_induced_rowKernel (N : ℕ) (hN : ∀ t, Nat.card D+w t ≤ N) (x : ℝ) :
    value F (A F P)
      (fun n => (coefficientRow F P (fun i => induced F D f (c i))).ker ⊓ power F P n) N x =
      (∑ t, x^(w t)) * value F (A F D) (rowKernelPower D c) (Nat.card D) x := by
  rw [← value_map_equiv F (A F P) (finiteBlockCoordinates D P T e)]
  have he : (fun n => ((coefficientRow F P (fun i => induced F D f (c i))).ker ⊓ power F P n).map
      (finiteBlockCoordinates D P T e).toLinearMap) =
      (fun n => piSpace F (A F D) (fun t => rowKernelPower D c (n-w t))) := by
    funext n
    exact induced_rowKernelPower_coordinates D P T f e w hmul hpower c n
  rw [he,value_shifted_piSpace F (A F D) (rowKernelPower D c) w (Nat.card D) N
    (rowKernelPower_nilpotent D c hD) hN]

variable (hc : ∀ i, c i ∈ power F D 1)
variable (hstrict : ∀ n, rowImagePower F D c n =
  (coefficientRow F D c).range ⊓ coefficientPower F D (ι := ι) (n+1))

include hc hstrict hmul hpower in
/-- In the actual derivative module the strict row has degree two: one
from its coefficient and one from the generator basis. -/
theorem induced_row_shifted_strict (n : ℕ) :
    (power F P (n-2)).map (coefficientRow F P (fun i => induced F D f (c i))) =
      (coefficientRow F P (fun i => induced F D f (c i))).range ⊓ shiftedFoxCoefficientPower P n := by
  cases n with
  | zero => simp [Submodule.map_top]
  | succ n =>
    cases n with
    | zero =>
      have h0 : coefficientPower F P (ι := ι) 0 = ⊤ := shiftedFoxCoefficientPower_zero P
      simp [shiftedFoxCoefficientPower,h0,Submodule.map_top]
    | succ n =>
      simpa only [show n+1+1-2 = n by omega, Nat.add_sub_cancel,
        shiftedFoxCoefficientPower,rowImagePower] using
        induced_rowImagePower_eq_induced F D P T f e w hmul hpower c hc hstrict n

include hD hP hc hstrict hmul hpower in
/-- The actual induced row image has its exact Hilbert value, with the
actual local annihilator subtracted and both degree shifts included. -/
theorem value_induced_row (x : ℝ) :
    value F (ι → A F P)
      (fun n => (coefficientRow F P (fun i => induced F D f (c i))).range ⊓ shiftedFoxCoefficientPower P n)
      (Nat.card P+1) x =
      x^2 * (Polynomial.eval₂ (Nat.castRingHom ℝ) x (hilbertPolynomial P) -
        (∑ t, x^(w t)) * value F (A F D) (rowKernelPower D c) (Nat.card D) x) := by
  classical
  let N := Nat.card P + Nat.card D + Finset.univ.sup w + 2
  have hNP : Nat.card P+1 ≤ N := by dsimp [N]; omega
  have hNP2 : Nat.card P+2 ≤ N := by dsimp [N]; omega
  have hN (t : T) : Nat.card D+w t ≤ N-2 := by
    have ht : w t ≤ Finset.univ.sup w := Finset.le_sup (by simp)
    dsimp [N]
    omega
  have he := value_map_add_kernel F (A F P) (ι → A F P)
    (fun n => power F P (n-2)) (coefficientRow F P (fun i => induced F D f (c i))) N x
  have hm : (fun n => (power F P (n-2)).map (coefficientRow F P (fun i => induced F D f (c i)))) =
      (fun n => (coefficientRow F P (fun i => induced F D f (c i))).range ⊓ shiftedFoxCoefficientPower P n) := by
    funext n
    exact induced_row_shifted_strict D P T f e w hmul hpower c hc hstrict n
  have hk : value F (A F P)
      (fun n => power F P (n-2) ⊓ (coefficientRow F P (fun i => induced F D f (c i))).ker) N x =
      x^2 * ((∑ t, x^(w t)) * value F (A F D) (rowKernelPower D c) (Nat.card D) x) := by
    have hh : (fun n => power F P (n-2) ⊓ (coefficientRow F P (fun i => induced F D f (c i))).ker) =
        (fun n => (fun k => (coefficientRow F P (fun i => induced F D f (c i))).ker ⊓ power F P k) (n-2)) := by
      funext n
      exact inf_comm _ _
    have hN2 : N = (N-2)+2 := by omega
    rw [hh]
    conv_lhs => rw [hN2]
    rw [value_shift_add F (A F P)
      (fun k => (coefficientRow F P (fun i => induced F D f (c i))).ker ⊓ power F P k)
      (N-2) 2 x,value_induced_rowKernel D P T f e w hmul hpower c hD (N-2) hN]
  rw [hm,hk,value_power_shift P hP 2 N hNP2] at he
  have hzero (n : ℕ) (hn : Nat.card P+1 ≤ n) :
      (coefficientRow F P (fun i => induced F D f (c i))).range ⊓ shiftedFoxCoefficientPower P n = ⊥ := by
    rw [shiftedFoxCoefficientPower_nilpotent P hP n hn,inf_bot_eq]
  rw [value_extend_of_le F (ι → A F P) _ (Nat.card P+1) N hNP hzero] at he
  nlinarith [he]

end UnitDistance.GroupAugmentation
