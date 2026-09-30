module

public import UnitDistance.TensorMixedCoordinates
public import UnitDistance.TensorEnergySupport

@[expose] public section
set_option backward.privateInPublic true


/-! # Compact pair-log support for the common mixed window -/

noncomputable section
open MeasureTheory
open scoped Classical BigOperators

namespace UnitDistance.Witness

variable {β γ ι : Type*} [Fintype β] [Fintype γ] [Fintype ι]
  {G U : ι → Type*} [∀ i, AddCommGroup (G i)] [∀ i, MeasurableSpace (G i)]
  (v : ι → Fin 11) (μ : (i : ι) → Measure (G i))
  (B : (i : ι) → Local.BallSystem (G i) (μ i) (residueCard (v i)))

/-- Finite shell energies have a fixed lower bound, so the archimedean
projection of the common mixed window lies in a compact energy window. -/
theorem mixed_supportedWindow_arch_bound (T : ℝ) {x : MixedPositionCoordinates β γ G}
    (hx : x ∈ supportedWindow (mixedPositionSupport v μ B) (mixedPositionEnergy v μ B) T) :
    tensorPositionEnergy x.1 ≤ T+∑ i, finiteShellEnergyBound (v i) := by
  have hi (i : ι) : -finiteShellEnergyBound (v i) ≤ localShellEnergy (v i) (B i) (x.2 i) := by
    apply neg_le_of_abs_le
    exact (B i).shellEnergy_norm_le _ _ _ _
  have hs : -(∑ i, finiteShellEnergyBound (v i)) ≤ ∑ i, localShellEnergy (v i) (B i) (x.2 i) := by
    simpa only [Finset.sum_neg_distrib] using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  have ht : tensorPositionEnergy x.1 + ∑ i, localShellEnergy (v i) (B i) (x.2 i) ≤ T := hx.2
  linarith

/-- Compact log support holds for every finite displacement and every
position measure. No norm or compactness hypothesis on the finite places
is required for this archimedean truncation. -/
theorem mixed_window_overlap_compactSupport
    (ν : Measure (MixedPositionCoordinates β γ G)) (T : ℝ) (δ : (i : ι) → G i × G i) :
    HasCompactSupport (fun u : γ → ℝ =>
      ν (overlapSet
        (supportedWindow (mixedPositionSupport v μ B) (mixedPositionEnergy v μ B) T)
        (tensorStep u, δ))) := by
  let plus : γ → MixedPositionCoordinates β γ G →+ ℂ := fun j =>
    { toFun := fun x => (x.1.2 j).1
      map_zero' := rfl
      map_add' := by intros; rfl }
  let minus : γ → MixedPositionCoordinates β γ G →+ ℂ := fun j =>
    { toFun := fun x => (x.1.2 j).2
      map_zero' := rfl
      map_add' := by intros; rfl }
  obtain ⟨R, hR, hbound⟩ := (isCompact_tensorPositionEnergy_window
    (β := β) (γ := γ) (T+∑ i, finiteShellEnergyBound (v i))).isBounded.exists_pos_norm_le
  apply reciprocal_overlap_compactSupport ν _ plus minus (fun u => (tensorStep u, δ)) hR
  · intro x hx j
    have hb := hbound x.1 (mixed_supportedWindow_arch_bound v μ B T hx)
    exact (norm_fst_le (x.1.2 j)).trans
      ((norm_le_pi_norm x.1.2 j).trans ((norm_snd_le x.1).trans hb))
  · intro x hx j
    have hb := hbound x.1 (mixed_supportedWindow_arch_bound v μ B T hx)
    exact (norm_snd_le (x.1.2 j)).trans
      ((norm_le_pi_norm x.1.2 j).trans ((norm_snd_le x.1).trans hb))
  · intro u j
    change ‖(Real.exp (u j) : ℂ)‖ = Real.exp (u j)
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  · intro u j
    change ‖(Real.exp (-u j) : ℂ)‖ = Real.exp (-u j)
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

end UnitDistance.Witness
