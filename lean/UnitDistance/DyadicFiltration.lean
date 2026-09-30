module

public import UnitDistance.DyadicAlgebra
public import Mathlib.LinearAlgebra.Finsupp.Defs

@[expose] public section
set_option backward.privateInPublic true


/-!
# Exact certificate interfaces for the dyadic augmentation recurrence

The operators in this file are the coefficient form of actual right
multiplication by `x-1`, `y-1`, and `z-1` in the concrete group algebra.
Finite row certificates must prove both span inclusions and independence.
-/

noncomputable section

open scoped BigOperators
open Set

namespace UnitDistance.Dyadic.Filtration

abbrev V := Fin 32 → F

def gen : Fin 3 → D := ![D.x, D.y, D.z]

/-- Coefficients after right multiplication by the indicated group generator
minus the identity. -/
def step (k : Fin 3) : V →ₗ[F] V where
  toFun v i := v (D.index (D.ofIndex i * (gen k)⁻¹)) - v i
  map_add' u v := by ext i; simp; ring
  map_smul' a v := by ext i; simp; ring

/-- The concrete coefficient representation in the group-element index order. -/
def coefficients : AlgebraD ≃ₗ[F] V :=
  (MonoidAlgebra.coeffLinearEquiv F).trans
    ((Finsupp.linearEquivFunOnFinite F F D).trans
      (LinearEquiv.funCongrLeft F F D.indexEquiv.symm))

theorem coefficients_apply (v : AlgebraD) (i : Fin 32) :
    coefficients v i = v.coeff (D.ofIndex i) := rfl

/-- The computational right-action matrices are attached to convolution
multiplication in the actual group algebra. -/
theorem step_coefficients (k : Fin 3) (v : AlgebraD) :
    step k (coefficients v) =
      coefficients (v * (AlgebraD.delta (gen k) - 1)) := by
  ext i
  simp [step, coefficients_apply, mul_sub, AlgebraD.delta,
    D.ofIndex_index, MonoidAlgebra.coeff_mul_single_apply]

def next (S : Submodule F V) : Submodule F V :=
  ⨆ k : Fin 3, S.map (step k)

/-- Start with the full group algebra and repeatedly span right products by
the three generator differences, exactly as in the manuscript's row reduction. -/
def stage : ℕ → Submodule F V
  | 0 => ⊤
  | n + 1 => next (stage n)

def row (mask : ℕ) : V := fun i => if mask.testBit i.val then 1 else 0

def rows {r : ℕ} (masks : Fin r → ℕ) : Fin r → V := fun i => row (masks i)

def spanRows {r : ℕ} (b : Fin r → V) : Submodule F V :=
  Submodule.span F (Set.range b)

theorem sum_mem_spanRows {r : ℕ} (b : Fin r → V) (a : Fin r → F) :
    (∑ j, a j • b j) ∈ spanRows b := by
  apply Submodule.sum_mem
  intro j _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- Pivot evaluation certifies linear independence, without numerical rank
oracles or native evaluation. -/
theorem independent_of_pivots {r : ℕ} (b : Fin r → V) (p : Fin r → Fin 32)
    (h : ∀ i j, b i (p j) = if i = j then 1 else 0) : LinearIndependent F b := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha j
  have hj := congrArg (fun v : V => v (p j)) ha
  simpa [h] using hj

theorem finrank_spanRows {r : ℕ} (b : Fin r → V) (p : Fin r → Fin 32)
    (h : ∀ i j, b i (p j) = if i = j then 1 else 0) :
    Module.finrank F (spanRows b) = r := by
  rw [spanRows, finrank_span_eq_card (independent_of_pivots b p h)]
  exact Fintype.card_fin r

/-- Two explicit linear-combination identities certify the full recurrence.
The upper identities ensure no generated row was missed; the lower identities
ensure every proposed next row really comes from the previous stage. -/
theorem next_spanRows {r s : ℕ} (b : Fin r → V) (c : Fin s → V)
    (upper : Fin r → Fin 3 → Fin s → F)
    (lower : Fin s → Fin r × Fin 3 → F)
    (hu : ∀ i k, step k (b i) = ∑ j, upper i k j • c j)
    (hl : ∀ j, c j = ∑ ik : Fin r × Fin 3, lower j ik • step ik.2 (b ik.1)) :
    next (spanRows b) = spanRows c := by
  apply le_antisymm
  · apply iSup_le
    intro k
    apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro v ⟨i, rfl⟩
    change step k (b i) ∈ spanRows c
    rw [hu]
    exact sum_mem_spanRows c _
  · apply Submodule.span_le.mpr
    rintro v ⟨j, rfl⟩
    rw [hl]
    apply Submodule.sum_mem
    intro ik _
    apply Submodule.smul_mem
    apply (le_iSup (fun k : Fin 3 => (spanRows b).map (step k)) ik.2)
    exact ⟨b ik.1, Submodule.subset_span ⟨ik.1, rfl⟩, rfl⟩

end UnitDistance.Dyadic.Filtration
