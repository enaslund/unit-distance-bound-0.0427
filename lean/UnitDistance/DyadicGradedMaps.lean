module

public import UnitDistance.DyadicGradedLinear

@[expose] public section
set_option backward.privateInPublic true


/-! Actual left and right multiplication on the augmentation filtration. -/

noncomputable section
open scoped BigOperators

namespace UnitDistance.Dyadic
namespace AlgebraD

theorem power_mul_augmentation (n : ℕ) (v a : AlgebraD)
    (hv : v ∈ augmentationPower n) (ha : augmentation a = 0) :
    v * a ∈ augmentationPower (n + 1) := by
  rw [← stage_eq_augmentationPower] at hv ⊢
  exact stage_mul_augmentation n v a hv ha

/-- Augmentation powers are also stable under left augmentation multiplication.
The proof uses the ordinary span-of-products definition, without commutativity. -/
theorem augmentation_mul_power (n : ℕ) (a v : AlgebraD)
    (ha : augmentation a = 0) (hv : v ∈ augmentationPower n) :
    a * v ∈ augmentationPower (n + 1) := by
  induction n generalizing v with
  | zero =>
    rw [augmentationPower_one]
    change augmentation (a * v) = 0
    rw [augmentation_mul, ha, zero_mul]
  | succ n ih =>
    change v ∈ Submodule.span F {v | ∃ u ∈ augmentationPower n,
      ∃ b, augmentation b = 0 ∧ v = u * b} at hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      rcases hv with ⟨u, hu, b, hb, rfl⟩
      rw [← mul_assoc]
      exact power_mul_augmentation (n + 1) _ b (ih u hu) hb
    | zero => simp
    | add v w hv hw ihv ihw =>
      simpa only [mul_add] using (augmentationPower (n + 1 + 1)).add_mem ihv ihw
    | smul c v hv ihv =>
      simpa only [mul_smul_comm] using (augmentationPower (n + 1 + 1)).smul_mem c ihv

theorem coefficients_mem_stage (n : ℕ) (v : AlgebraD) :
    Filtration.coefficients v ∈ Filtration.stage n ↔ v ∈ augmentationPower n := by
  rw [← coefficients_stage, stage_eq_augmentationPower]
  constructor
  · rintro ⟨a, ha, he⟩
    have heq : a = v := Filtration.coefficients.injective he
    exact heq ▸ ha
  · intro hv
    exact ⟨v, hv, rfl⟩

end AlgebraD

namespace Graded
open Filtration

/-- `true` means left multiplication by the generator difference; `false`
means right multiplication, the variable-row convention for left Fox coefficients. -/
def sidedStep (left : Bool) (k : Fin 3) : V →ₗ[F] V :=
  if left then
    { toFun := fun v i => v (D.index ((gen k)⁻¹ * D.ofIndex i)) - v i
      map_add' := by intros; ext i; simp; ring
      map_smul' := by intros; ext i; simp; ring }
  else step k

def sidedProduct (left : Bool) (k : Fin 3) (v : AlgebraD) : AlgebraD :=
  if left then (AlgebraD.delta (gen k) - 1) * v
  else v * (AlgebraD.delta (gen k) - 1)

theorem sidedStep_coefficients (left : Bool) (k : Fin 3) (v : AlgebraD) :
    sidedStep left k (coefficients v) = coefficients (sidedProduct left k v) := by
  cases left with
  | false => exact step_coefficients k v
  | true =>
    ext i
    simp [sidedStep, sidedProduct, coefficients_apply, sub_mul, AlgebraD.delta,
      D.ofIndex_index, MonoidAlgebra.coeff_single_mul_apply]

theorem sidedProduct_mem_power (left : Bool) (k : Fin 3) (n : ℕ) (v : AlgebraD)
    (hv : v ∈ AlgebraD.augmentationPower n) :
    sidedProduct left k v ∈ AlgebraD.augmentationPower (n + 1) := by
  cases left with
  | false => exact AlgebraD.power_mul_augmentation n v _ hv (by simp)
  | true => exact AlgebraD.augmentation_mul_power n _ v (by simp) hv

theorem sidedStep_mem_stage (left : Bool) (k : Fin 3) (n : ℕ) (v : V)
    (hv : v ∈ stage n) : sidedStep left k v ∈ stage (n + 1) := by
  obtain ⟨a, rfl⟩ := coefficients.surjective v
  rw [sidedStep_coefficients, AlgebraD.coefficients_mem_stage]
  exact sidedProduct_mem_power left k n a ((AlgebraD.coefficients_mem_stage n a).mp hv)

def joint {r : ℕ} (left : Bool) (b : Fin r → V) (p : Fin r → Fin 32) :
    V →ₗ[F] (Fin 3 × Fin 32 → F) where
  toFun v ki := remainder b p (sidedStep left ki.1 v) ki.2
  map_add' u v := by ext ki; simp
  map_smul' a v := by ext ki; simp

theorem joint_eq_zero_iff {r : ℕ} (left : Bool) (b : Fin r → V)
    (p : Fin r → Fin 32) (hp : ∀ i j, b i (p j) = if i = j then 1 else 0) (v : V) :
    joint left b p v = 0 ↔ ∀ k, sidedStep left k v ∈ spanRows b := by
  constructor
  · intro h k
    apply (remainder_eq_zero_iff b p hp _).mp
    ext i
    exact congrFun h (k, i)
  · intro h
    ext ⟨k, i⟩
    exact congrFun ((remainder_eq_zero_iff b p hp _).mpr (h k)) i

def combination {r : ℕ} (b : Fin r → V) (mask : ℕ) : V :=
  ∑ i, (if mask.testBit i.val then (1 : F) else 0) • b i

theorem combination_mem {r : ℕ} (b : Fin r → V) (mask : ℕ) :
    combination b mask ∈ spanRows b := sum_mem_spanRows b _

/-- A small identity minor certifies the entire associated graded kernel.
All other inputs are the independently certified augmentation bases and dimensions. -/
theorem gradedKernel_of_certificate {r s d : ℕ} (n : ℕ)
    (b : Fin r → V) (c : Fin s → V) (pc : Fin s → Fin 32)
    (hb : stage n = spanRows b) (hc : stage (n + 2) = spanRows c)
    (hpc : ∀ i j, c i (pc j) = if i = j then 1 else 0)
    (hdim : Module.finrank F (stage n) = d + Module.finrank F (stage (n + 1)))
    (masks : Bool → Fin d → ℕ) (p : Fin d → Fin 3 × Fin 32)
    (hp : ∀ left i j, joint left c pc (combination b (masks left i)) (p j) =
      if i = j then 1 else 0) :
    ∀ left v, v ∈ stage n →
      ((∀ k, sidedStep left k v ∈ stage (n + 2)) ↔ v ∈ stage (n + 1)) := by
  intro left
  have hle : stage (n + 1) ≤ stage n := by
    rw [← AlgebraD.coefficients_stage, ← AlgebraD.coefficients_stage]
    exact Submodule.map_mono (AlgebraD.stage_succ_le n)
  have hk : stage (n + 1) ≤ (joint left c pc).ker := by
    intro v hv
    apply (joint_eq_zero_iff left c pc hpc v).mpr
    intro k
    rw [← hc]
    exact sidedStep_mem_stage left k (n + 1) v hv
  have hr := rank_lower_of_pivots (stage n) (joint left c pc)
    (fun i => combination b (masks left i))
    (fun i => hb.symm ▸ combination_mem b (masks left i)) p (hp left)
  have he := kernel_eq_of_rank_lower (stage n) (stage (n + 1))
    (joint left c pc) hle hk hdim hr
  intro v hv
  rw [← he v hv, joint_eq_zero_iff left c pc hpc, ← hc]

end Graded
end UnitDistance.Dyadic
