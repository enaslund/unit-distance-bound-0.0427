module

public import UnitDistance.FilteredHilbertPi
public import UnitDistance.GroupAugmentationInducedFox
public import UnitDistance.GroupAugmentationHilbertShift

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual Hilbert costs of full induced local Fox kernels

The induced local augmentation image is identified with actual shifted
copies of the local augmentation ideal. Strictness then determines the
Hilbert value of its actual ambient kernel. This is the complete local-kernel
cost used in the optimized weighted infinitude inequality.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.GroupAugmentation
open FilteredHilbert
local notation "F" => ZMod 2
variable (D : Type*) [Group D] [Finite D] (hD : IsPGroup 2 D)

/-- The actual augmentation ideal with its induced augmentation filtration. -/
def augmentationIdealPower (n : ℕ) : Submodule F (A F D) :=
  power F D 1 ⊓ power F D n

theorem augmentationIdealPower_eq :
    augmentationIdealPower D = fun n => power F D ((n-1)+1) := by
  funext n
  cases n with
  | zero => simp [augmentationIdealPower]
  | succ n =>
    simp only [augmentationIdealPower,Nat.add_sub_cancel]
    exact inf_eq_right.mpr (power_antitone F D (by omega : 1 ≤ n+1))

include hD in
theorem augmentationIdealPower_nilpotent (n : ℕ) (hn : Nat.card D ≤ n) :
    augmentationIdealPower D n = ⊥ := by
  rw [augmentationIdealPower,hilbert_power_vanishes_after_card D hD n hn,inf_bot_eq]

include hD in
/-- Removing the actual scalar augmentation quotient subtracts exactly one
from the actual group-algebra Hilbert value. -/
theorem value_augmentationIdealPower (N : ℕ) (hN : Nat.card D ≤ N) (t : ℝ) :
    value F (A F D) (augmentationIdealPower D) N t =
      Polynomial.eval₂ (Nat.castRingHom ℝ) t (hilbertPolynomial D) - 1 := by
  rw [value_extend_of_le F (A F D) (augmentationIdealPower D) (Nat.card D) N hN
    (augmentationIdealPower_nilpotent D hD)]
  rw [← value_extend F (A F D) (augmentationIdealPower D) (Nat.card D)
    (augmentationIdealPower_nilpotent D hD _ le_rfl)
    (augmentationIdealPower_nilpotent D hD _ (by omega))]
  rw [augmentationIdealPower_eq,value_shift F (A F D) (fun n => power F D (n+1))]
  have he := value_succ F (A F D) (power F D) (Nat.card D) t
  rw [value_extend F (A F D) (power F D) (Nat.card D)
    (hilbert_power_vanishes_after_card D hD _ le_rfl)
    (hilbert_power_vanishes_after_card D hD _ (by omega))] at he
  have hd : (Module.finrank F ↥(power F D 0) : ℝ) - Module.finrank F ↥(power F D 1) = 1 := by
    have hh := finrank_power_zero_sub_one D
    exact_mod_cast (show (Module.finrank F ↥(power F D 0) : ℤ) -
      Module.finrank F ↥(power F D 1) = 1 by omega)
  rw [hd] at he
  rw [hilbertPolynomial_eval]
  linarith

variable (P T : Type*) [Group P] [Finite P] [Fintype T]
variable {ι : Type*} [Fintype ι]
variable (f : D →* P) (e : A F P ≃ₗ[F] (T →₀ A F D)) (w : T → ℕ)
variable (hmul : ∀ a b t, e (a*induced F D f b) t = e a t*b)
variable (hpower : ∀ a n, a ∈ power F P n ↔ ∀ t, e a t ∈ power F D (n-w t))
variable (generators : ι → D)
variable (hgen : Subgroup.closure (Set.range generators) = ⊤)

/-- Ordinary finite-function coordinates for the actual right-module blocks. -/
def finiteBlockCoordinates : A F P ≃ₗ[F] (T → A F D) :=
  e.trans (Finsupp.linearEquivFunOnFinite F (A F D) T)

@[simp] theorem finiteBlockCoordinates_apply (a : A F P) (t : T) :
    finiteBlockCoordinates D P T e a t = e a t := rfl

include hmul hpower hgen in
/-- The induced local augmentation image has precisely the shifted actual
local augmentation-ideal filtrations in the genuine ambient coordinates. -/
theorem induced_foxImage_coordinates (n : ℕ) :
    ((foxMap F P (fun i => f (generators i))).range ⊓ power F P n).map
      (finiteBlockCoordinates D P T e).toLinearMap =
      piSpace F (A F D) (fun t => augmentationIdealPower D (n-w t)) := by
  ext b
  constructor
  · rintro ⟨a,⟨ha,hap⟩,rfl⟩
    apply (mem_piSpace F (A F D) _ _).mpr
    intro t
    exact ⟨(induced_foxMap_mem_range_iff F D P T f e w hmul hpower generators hgen a).mp ha t,
      (hpower a n).mp hap t⟩
  · intro hb
    have ht := (mem_piSpace F (A F D) _ b).mp hb
    let a := (finiteBlockCoordinates D P T e).symm b
    have ha (t : T) : e a t = b t := by
      exact congrFun ((finiteBlockCoordinates D P T e).apply_symm_apply b) t
    refine ⟨a,⟨?_,?_⟩,by simp [a]⟩
    · apply (induced_foxMap_mem_range_iff F D P T f e w hmul hpower generators hgen a).mpr
      intro t
      rw [ha]
      exact (ht t).1
    · apply (hpower a n).mpr
      intro t
      rw [ha]
      exact (ht t).2

include hD hmul hpower hgen in
/-- The actual induced local augmentation image has Hilbert value equal to
the genuine shift sum times the actual local ideal's Hilbert value. -/
theorem value_induced_foxImage (N : ℕ) (hN : ∀ t, Nat.card D+w t ≤ N) (x : ℝ) :
    value F (A F P)
      (fun n => (foxMap F P (fun i => f (generators i))).range ⊓ power F P n) N x =
      (∑ t, x^(w t)) * (Polynomial.eval₂ (Nat.castRingHom ℝ) x (hilbertPolynomial D)-1) := by
  rw [← value_map_equiv F (A F P) (finiteBlockCoordinates D P T e)]
  have he : (fun n => ((foxMap F P (fun i => f (generators i))).range ⊓ power F P n).map
      (finiteBlockCoordinates D P T e).toLinearMap) =
      (fun n => piSpace F (A F D) (fun t => augmentationIdealPower D (n-w t))) := by
    funext n
    exact induced_foxImage_coordinates D P T f e w hmul hpower generators hgen n
  rw [he,value_shifted_piSpace F (A F D) (augmentationIdealPower D) w (Nat.card D) N
    (augmentationIdealPower_nilpotent D hD) hN,
    value_augmentationIdealPower D hD (Nat.card D) le_rfl]

include hmul hpower hgen in
theorem induced_foxMap_shifted_strict (n : ℕ) :
    (shiftedFoxCoefficientPower P (ι := ι) n).map (foxMap F P (fun i => f (generators i))) =
      (foxMap F P (fun i => f (generators i))).range ⊓ power F P n := by
  cases n with
  | zero => simp [Submodule.map_top]
  | succ n =>
    simpa only [shiftedFoxCoefficientPower,Nat.add_sub_cancel] using
      induced_foxMap_strict F D P T f e w hmul hpower generators hgen n

variable (hP : IsPGroup 2 P)

include hP in
theorem value_shiftedFoxCoefficientPower (N : ℕ) (hN : Nat.card P+1 ≤ N) (x : ℝ) :
    value F (ι → A F P) (shiftedFoxCoefficientPower P) N x =
      (Fintype.card ι : ℝ)*x*Polynomial.eval₂ (Nat.castRingHom ℝ) x (hilbertPolynomial P) := by
  have he : N = (N-1)+1 := by omega
  conv_lhs => rw [he]
  change value F (ι → A F P) (fun n => coefficientPower F P (n-1)) ((N-1)+1) x = _
  rw [value_shift,value_coefficientPower,
    value_extend_of_le F (A F P) (power F P) (Nat.card P) (N-1) (by omega)
      (hilbert_power_vanishes_after_card P hP),← hilbertPolynomial_eval]
  ring

include hD hP hmul hpower hgen in
/-- The actual full induced local kernel has its exact Hilbert cost. This
identity includes every actual local relation, not only a displayed row. -/
theorem value_induced_foxKernel (N : ℕ) (hN : ∀ t, Nat.card D+w t ≤ N)
    (hNP : Nat.card P+1 ≤ N) (x : ℝ) :
    value F (ι → A F P) (foxKernelPower P (fun i => f (generators i))) N x =
      (Fintype.card ι : ℝ)*x*Polynomial.eval₂ (Nat.castRingHom ℝ) x (hilbertPolynomial P) -
        (∑ t, x^(w t)) * (Polynomial.eval₂ (Nat.castRingHom ℝ) x (hilbertPolynomial D)-1) := by
  have he := value_map_add_kernel F (ι → A F P) (A F P)
    (shiftedFoxCoefficientPower P) (foxMap F P (fun i => f (generators i))) N x
  have hm : (fun n => (shiftedFoxCoefficientPower P n).map (foxMap F P (fun i => f (generators i)))) =
      (fun n => (foxMap F P (fun i => f (generators i))).range ⊓ power F P n) := by
    funext n
    exact induced_foxMap_shifted_strict D P T f e w hmul hpower generators hgen n
  rw [hm,value_induced_foxImage D hD P T f e w hmul hpower generators hgen N hN,
    value_shiftedFoxCoefficientPower P hP N hNP] at he
  change _ + value F (ι → A F P) (foxKernelPower P (fun i => f (generators i))) N x = _ at he
  linarith

include hD hP hmul hpower hgen in
/-- The exact induced full-kernel cost at the standard ambient nilpotence
cutoff, with the temporary larger coordinate cutoff eliminated. -/
theorem value_induced_foxKernel_standard (x : ℝ) :
    value F (ι → A F P) (foxKernelPower P (fun i => f (generators i))) (Nat.card P+1) x =
      (Fintype.card ι : ℝ)*x*Polynomial.eval₂ (Nat.castRingHom ℝ) x (hilbertPolynomial P) -
        (∑ t, x^(w t)) * (Polynomial.eval₂ (Nat.castRingHom ℝ) x (hilbertPolynomial D)-1) := by
  classical
  let N := Nat.card P + Nat.card D + Finset.univ.sup w + 1
  have hNP : Nat.card P+1 ≤ N := by dsimp [N]; omega
  have hN (t : T) : Nat.card D+w t ≤ N := by
    have ht : w t ≤ Finset.univ.sup w := Finset.le_sup (by simp)
    dsimp [N]
    omega
  have he := value_induced_foxKernel D hD P T f e w hmul hpower generators hgen hP N hN hNP x
  rw [value_extend_of_le F (ι → A F P) (foxKernelPower P (fun i => f (generators i)))
    (Nat.card P+1) N hNP (foxKernelPower_nilpotent P hP (fun i => f (generators i)))] at he
  exact he

end UnitDistance.GroupAugmentation
