module

public import UnitDistance.LocalOperator
public import Mathlib.Topology.LocallyConstant.Algebra

@[expose] public section
set_option backward.privateInPublic true


/-! # Regularity and invariances of actual finite shell profiles -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace UnitDistance.Local.BallSystem

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G]
variable {μ : Measure G} {Q : ℝ} (B : BallSystem G μ Q)

theorem shell_invariant (φ : G → G)
    (hφ : ∀ a x, φ x ∈ B.ball a ↔ x ∈ B.ball a) (k : ℤ) (i : ℕ) (x : G) :
    φ x ∈ B.shell k i ↔ x ∈ B.shell k i := by
  cases i with
  | zero => exact hφ k x
  | succ i => simp only [shell, Set.mem_sdiff, SetLike.mem_coe, hφ]

/-- Separate invariance under any transformations preserving the balls; in
the valued-field model these include multiplication by norm-one units. -/
theorem shellProfile_invariant (φ ψ : G → G)
    (hφ : ∀ a x, φ x ∈ B.ball a ↔ x ∈ B.ball a)
    (hψ : ∀ a x, ψ x ∈ B.ball a ↔ x ∈ B.ball a)
    (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) (x : G × G) :
    B.shellProfile k I w (φ x.1, ψ x.2) = B.shellProfile k I w x := by
  classical
  apply Finset.sum_congr rfl
  intro ij hij
  simp only [shellCell, Set.indicator, Set.mem_prod,
    B.shell_invariant φ hφ, B.shell_invariant ψ hψ]

theorem shellProfile_nonneg (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ)
    (hw : ∀ ij ∈ I, 0 ≤ w ij) (x : G × G) : 0 ≤ B.shellProfile k I w x := by
  apply Finset.sum_nonneg
  intro ij hij
  exact Set.indicator_nonneg (fun _ _ => hw ij hij) x

variable [TopologicalSpace G]

theorem shell_clopen (hB : ∀ a, IsClopen (B.ball a : Set G)) (k : ℤ) (i : ℕ) :
    IsClopen (B.shell k i) := by
  cases i with
  | zero => exact hB k
  | succ i => exact (hB _).diff (hB _)

theorem shellCell_clopen (hB : ∀ a, IsClopen (B.ball a : Set G)) (k : ℕ) (ij : ℕ × ℕ) :
    IsClopen (B.shellCell k ij) :=
  (B.shell_clopen hB _ _).prod (B.shell_clopen hB _ _)

/-- Finite shell profiles are locally constant when the underlying balls are clopen. -/
theorem shellProfile_locallyConstant (hB : ∀ a, IsClopen (B.ball a : Set G))
    (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) :
    IsLocallyConstant (B.shellProfile k I w) := by
  classical
  unfold shellProfile
  induction I using Finset.induction_on with
  | empty =>
    apply IsLocallyConstant.of_constant
    intro x y
    simp
  | @insert ij I hij ih =>
    simp only [Finset.sum_insert hij]
    exact ((LocallyConstant.const (G × G) (w ij)).indicator
      (B.shellCell_clopen hB k ij)).isLocallyConstant.add ih

/-- The support is contained in a compact rectangle; the compactness requirement
is an ordinary local-field property and is independent of the energy identity. -/
theorem shellProfile_hasCompactSupport [T2Space G]
    (hB : ∀ a, IsCompact (B.ball a : Set G))
    (k : ℕ) (I : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) :
    HasCompactSupport (B.shellProfile k I w) := by
  have hI : ∀ ij ∈ I, ij.1 ≤ I.sup Prod.fst ∧ ij.2 ≤ I.sup Prod.snd :=
    fun ij hij => ⟨Finset.le_sup hij, Finset.le_sup hij⟩
  apply HasCompactSupport.intro
    ((hB ((I.sup Prod.fst : ℕ) : ℤ)).prod (hB (k + ((I.sup Prod.snd : ℕ) : ℤ))))
  intro x hx
  by_contra hz
  exact hx (B.shellProfile_support k I w _ _ hI hz)

end UnitDistance.Local.BallSystem
