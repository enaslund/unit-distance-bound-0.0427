module

public import UnitDistance.DyadicFiltration

@[expose] public section
set_option backward.privateInPublic true


/-!
# Identification of the recurrence with actual augmentation powers

The powers below are independently defined as spans of products of elements
of the ordinary augmentation ideal. The generator recurrence is proved equal
to them, so its finite certificates measure the true augmentation filtration.
-/

noncomputable section
open scoped BigOperators

namespace UnitDistance.Dyadic.AlgebraD

def next (S : Submodule F AlgebraD) : Submodule F AlgebraD :=
  ⨆ k : Fin 3, S.map (rightMul (delta (Filtration.gen k) - 1))

def stage : ℕ → Submodule F AlgebraD
  | 0 => ⊤
  | n + 1 => next (stage n)

/-- Ordinary powers of the augmentation ideal, as linear spans of products.
This definition does not refer to any proposed rank or finite certificate. -/
def augmentationPower (n : ℕ) : Submodule F AlgebraD :=
  Nat.rec ⊤ (fun _ S => Submodule.span F {v | ∃ a ∈ S,
    ∃ b : AlgebraD, augmentation b = 0 ∧ v = a * b}) n

theorem augmentationPower_one : augmentationPower 1 = augmentation.ker := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨a, _, b, hb, rfl⟩
    change augmentation (a * b) = 0
    rw [augmentation_mul, hb, mul_zero]
  · intro v hv
    apply Submodule.subset_span
    exact ⟨1, by trivial, v, hv, (one_mul v).symm⟩

theorem next_mono : Monotone next := by
  intro S T h
  exact iSup_mono fun _ => Submodule.map_mono h

theorem stage_succ_le (n : ℕ) : stage (n + 1) ≤ stage n := by
  induction n with
  | zero => exact le_top
  | succ n ih => exact next_mono ih

/-- A subspace stable under right translation by a group element is stable
under all powers of that translation; exponent four supplies inverses. -/
def rightPreserving (S : Submodule F AlgebraD) : Subgroup D where
  carrier := {g | ∀ v ∈ S, v * delta g ∈ S}
  one_mem' := by intro v hv; simpa using hv
  mul_mem' {g h} hg hh := by
    intro v hv
    simpa [← delta_mul, ← mul_assoc] using hh _ (hg v hv)
  inv_mem' {g} hg := by
    intro v hv
    have h := hg _ (hg _ (hg v hv))
    rw [D.inv_eq_cube]
    simpa [pow_succ, ← delta_mul, ← mul_assoc] using h

theorem stage_right_generator (n : ℕ) (k : Fin 3) (v : AlgebraD)
    (hv : v ∈ stage n) : v * delta (Filtration.gen k) ∈ stage n := by
  have hnext : v * (delta (Filtration.gen k) - 1) ∈ stage (n + 1) :=
    (le_iSup (fun k : Fin 3 => (stage n).map (rightMul (delta (Filtration.gen k) - 1))) k)
      ⟨v, hv, rfl⟩
  have h := (stage n).add_mem (stage_succ_le n hnext) hv
  simpa only [mul_sub, mul_one, sub_add_cancel] using h

theorem stage_right_group (n : ℕ) (g : D) (v : AlgebraD)
    (hv : v ∈ stage n) : v * delta g ∈ stage n := by
  have hcl : Subgroup.closure ({D.x, D.y, D.z} : Set D) ≤ rightPreserving (stage n) := by
    apply (Subgroup.closure_le (rightPreserving (stage n))).mpr
    intro h hh
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
    rcases hh with rfl | rfl | rfl
    · exact stage_right_generator n 0
    · exact stage_right_generator n 1
    · exact stage_right_generator n 2
  rw [D.generators] at hcl
  exact hcl (Subgroup.mem_top g) v hv

def differencesPreserving (S : Submodule F AlgebraD)
    (hS : ∀ g v, v ∈ S → v * delta g ∈ S) : Subgroup D where
  carrier := {g | ∀ v ∈ S, v * (delta g - 1) ∈ next S}
  one_mem' := by intro v _; simp
  mul_mem' {g h} hg hh := by
    intro v hv
    have h₁ := hh (v * delta g) (hS g v hv)
    have h₂ := hg v hv
    have hid : v * (delta (g * h) - 1) =
        (v * delta g) * (delta h - 1) + v * (delta g - 1) := by
      rw [← delta_mul]
      noncomm_ring
    rw [hid]
    exact (next S).add_mem h₁ h₂
  inv_mem' {g} hg := by
    intro v hv
    have h := hg (v * delta g⁻¹) (hS g⁻¹ v hv)
    have hid : v * (delta g⁻¹ - 1) = -(v * delta g⁻¹ * (delta g - 1)) := by
      simp only [mul_sub, mul_one, neg_sub, mul_assoc, delta_mul,
        inv_mul_cancel, delta_one]
    rw [hid]
    exact (next S).neg_mem h

theorem stage_mul_group_difference (n : ℕ) (g : D) (v : AlgebraD)
    (hv : v ∈ stage n) : v * (delta g - 1) ∈ stage (n + 1) := by
  let H := differencesPreserving (stage n) (stage_right_group n)
  have hcl : Subgroup.closure ({D.x, D.y, D.z} : Set D) ≤ H := by
    apply (Subgroup.closure_le H).mpr
    intro g hg v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    have hgen : ∀ k : Fin 3, v * (delta (Filtration.gen k) - 1) ∈ next (stage n) := by
      intro k
      exact (le_iSup (fun k : Fin 3 => (stage n).map
        (rightMul (delta (Filtration.gen k) - 1))) k) ⟨v, hv, rfl⟩
    rcases hg with rfl | rfl | rfl
    · exact hgen 0
    · exact hgen 1
    · exact hgen 2
  rw [D.generators] at hcl
  exact hcl (Subgroup.mem_top g) v hv

theorem stage_mul_augmentation (n : ℕ) (v b : AlgebraD)
    (hv : v ∈ stage n) (hb : augmentation b = 0) : v * b ∈ stage (n + 1) := by
  rw [← augmentation_zero_expansion b hb, Finset.mul_sum]
  apply Submodule.sum_mem
  intro g _
  rw [mul_smul_comm]
  exact Submodule.smul_mem _ _ (stage_mul_group_difference n g v hv)

/-- The finite generator recurrence is exactly the ordinary ideal-power
filtration, with no additional mathematical hypothesis. -/
theorem stage_eq_augmentationPower (n : ℕ) : stage n = augmentationPower n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    apply le_antisymm
    · apply iSup_le
      intro k
      rintro v ⟨a, ha, rfl⟩
      apply Submodule.subset_span
      refine ⟨a, (show a ∈ augmentationPower n from ih ▸ ha), delta (Filtration.gen k) - 1, ?_, rfl⟩
      simp
    · apply Submodule.span_le.mpr
      rintro v ⟨a, ha, b, hb, rfl⟩
      exact stage_mul_augmentation n a b (ih.symm ▸ ha) hb

theorem coefficients_next (S : Submodule F AlgebraD) :
    (next S).map Filtration.coefficients.toLinearMap =
      Filtration.next (S.map Filtration.coefficients.toLinearMap) := by
  simp only [next, Filtration.next, Submodule.map_iSup, ← Submodule.map_comp]
  apply congrArg iSup
  funext k
  apply congrArg (fun f : AlgebraD →ₗ[F] Filtration.V => S.map f)
  apply LinearMap.ext
  intro v
  funext i
  exact congrFun (Filtration.step_coefficients k v).symm i

theorem coefficients_stage (n : ℕ) :
    (stage n).map Filtration.coefficients.toLinearMap = Filtration.stage n := by
  induction n with
  | zero =>
    change (⊤ : Submodule F AlgebraD).map Filtration.coefficients.toLinearMap = ⊤
    rw [Submodule.map_top, LinearMap.range_eq_top.mpr Filtration.coefficients.surjective]
  | succ n ih =>
    rw [show stage (n + 1) = next (stage n) from rfl, coefficients_next, ih]
    rfl

theorem finrank_augmentationPower_eq (n : ℕ) :
    Module.finrank F (augmentationPower n) = Module.finrank F (Filtration.stage n) := by
  rw [← stage_eq_augmentationPower n, ← coefficients_stage n]
  exact (Filtration.coefficients.finrank_map_eq (stage n)).symm

end UnitDistance.Dyadic.AlgebraD
