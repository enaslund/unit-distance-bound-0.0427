module

public import UnitDistance.PairOverlapBetaIntegral

@[expose] public section
set_option backward.privateInPublic true


/-! The normalized beta densities appearing in the actual pair overlap. -/

noncomputable section
open MeasureTheory Set
namespace UnitDistance.Witness

def pairOverlapBetaExponent (i k : Fin 4) : ℝ := s + (i : ℕ) + (s + (k : ℕ)) - 1

def pairOverlapBetaNormalization (i k : Fin 4) : ℝ :=
  Real.Gamma (s + (i : ℕ) + (s + (k : ℕ))) /
    (Real.Gamma (s + (i : ℕ)) * Real.Gamma (s + (k : ℕ)))

def pairOverlapBetaDensity (i k : Fin 4) (t : ℝ) : ℝ :=
  pairOverlapBetaNormalization i k * t ^ (s + (i : ℕ) - 1) *
    (1 - t) ^ (s + (k : ℕ) - 1)

def pairOverlapBetaShiftKernel (i k : Fin 4) (h : ℂ) (t : ℝ) : ℝ :=
  pairOverlapBetaDensity i k t *
    (1 + a*t*(1-t)*‖h‖^2) ^ (-pairOverlapBetaExponent i k)

theorem pairOverlapBetaExponent_pos (i k : Fin 4) : 0 < pairOverlapBetaExponent i k := by
  unfold pairOverlapBetaExponent
  have hs : 1 < s := by norm_num [s]
  linarith [Nat.cast_nonneg (α := ℝ) (i : ℕ), Nat.cast_nonneg (α := ℝ) (k : ℕ)]

theorem pairOverlapBetaNormalization_pos (i k : Fin 4) :
    0 < pairOverlapBetaNormalization i k := by
  have hs : 0 < s := by norm_num [s]
  unfold pairOverlapBetaNormalization
  positivity

theorem pairOverlapBetaDensity_nonneg (i k : Fin 4) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) : 0 ≤ pairOverlapBetaDensity i k t := by
  unfold pairOverlapBetaDensity
  positivity [pairOverlapBetaNormalization_pos i k, ht.1, sub_pos.mpr ht.2]

theorem pairOverlapBetaShiftKernel_eq (i k : Fin 4) (h : ℂ) (t : ℝ) :
    pairOverlapBetaShiftKernel i k h t = pairOverlapBetaNormalization i k *
      pairOverlapBetaKernel (s + (i : ℕ)) (s + (k : ℕ)) h t := by
  unfold pairOverlapBetaShiftKernel pairOverlapBetaDensity pairOverlapBetaKernel
    pairOverlapBetaExponent
  ring

theorem integrableOn_pairOverlapBetaShiftKernel (i k : Fin 4) (h : ℂ) :
    IntegrableOn (pairOverlapBetaShiftKernel i k h) (Ioo 0 1) := by
  have hs : 1 < s := by norm_num [s]
  have hi : 1 ≤ s + (i : ℕ) := by linarith [Nat.cast_nonneg (α := ℝ) (i : ℕ)]
  have hk : 1 ≤ s + (k : ℕ) := by linarith [Nat.cast_nonneg (α := ℝ) (k : ℕ)]
  have hI := (integrableOn_pairOverlapBetaKernel hi hk h).const_mul
    (pairOverlapBetaNormalization i k)
  apply hI.congr
  filter_upwards with t
  exact (pairOverlapBetaShiftKernel_eq i k h t).symm

theorem pairOverlapBetaShiftKernel_nonneg (i k : Fin 4) (h : ℂ) {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) 1) : 0 ≤ pairOverlapBetaShiftKernel i k h t := by
  rw [pairOverlapBetaShiftKernel_eq]
  exact mul_nonneg (pairOverlapBetaNormalization_pos i k).le
    (pairOverlapBetaKernel_nonneg h ht)

theorem pairOverlapCoordinateConvolution_beta_density (i k : Fin 4) (h : ℂ) :
    pairOverlapCoordinateConvolution i k h =
      (Real.pi / (a * pairOverlapBetaExponent i k)) *
        ∫ t in Ioo (0 : ℝ) 1, pairOverlapBetaShiftKernel i k h t := by
  simp_rw [pairOverlapBetaShiftKernel_eq]
  rw [integral_const_mul, pairOverlapCoordinateConvolution_beta]
  unfold pairOverlapBetaExponent pairOverlapBetaNormalization
  ring

end UnitDistance.Witness
