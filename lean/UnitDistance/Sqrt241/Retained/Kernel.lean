module

public import UnitDistance.Sqrt241.Retained.Detector
public import UnitDistance.Sqrt241.Cut.Descent

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# The cut kernel `kernelHat` is normal in `Ĝ`, with infinite quotient

`kernelHat` (the image in `G_B ≤ Ĝ` of the cut kernel of `F(8)`) equals
`A.kernel.map freeHat` for `freeHat : F(8) → G_B ≤ Ĝ`. The descent `Cut/Descent.lean`
(`SourceLifts.kernelHat_normal`, `SourceLifts.infinite_hat`) gives normality in
`Ĝ` from the `σ̂`-compatibility of the local elements (`Input` fields) and the
infinitude of `Ĝ ⧸ kernelHat` from the infinitude of the cut quotient.
Consequently `kernelHat ≤ core` and `kernelHat ≤ detKer`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Retained

open Tower Presentation Cut GroupData ProCGroups ProCGroups.Presentations

/-- `F(8) → G_B ≤ Ĝ`. -/
def freeHat : Source →ₜ* Ghat :=
  (⟨GB.subtype, continuous_subtype_val⟩ : GB →ₜ* Ghat).comp freeMap

theorem freeHat_apply (g : Source) : freeHat g = ((freeMap g : GB) : Ghat) := rfl

theorem freeHat_mem (g : Source) : freeHat g ∈ GB := (freeMap g).2

theorem freeHat_onto (h : Ghat) (hh : h ∈ GB) : ∃ g, freeHat g = h := by
  obtain ⟨g, hg⟩ := freeMap_surjective ⟨h, hh⟩
  exact ⟨g, by rw [freeHat_apply, hg]⟩

/-- A normal subgroup contained in `K` lies in its `σ̂`-core. -/
theorem le_sigmaCore_of_normal {N K : Subgroup Ghat} [N.Normal] (h : N ≤ K) : N ≤ sigmaCore K := by
  intro x hx
  rw [mem_sigmaCore_iff]
  refine ⟨h hx, h ?_⟩
  have := (inferInstance : N.Normal).conj_mem x hx sigmaHat⁻¹
  simpa using this

namespace Input

variable (I : Input)

theorem freeHat_conj (k : Fin 2) : freeHat (I.A.conj k) = ((I.E.conj k : GB) : Ghat) := by
  change ((freeMap (LocalElements.lift (I.E.conj k)) : GB) : Ghat) = _
  rw [LocalElements.freeMap_lift]

theorem freeHat_tameInertia (q : Fin 4) :
    freeHat (I.A.tameInertia q) = ((I.E.tameInertia q : GB) : Ghat) := by
  change ((freeMap (LocalElements.lift (I.E.tameInertia q)) : GB) : Ghat) = _
  rw [LocalElements.freeMap_lift]

theorem freeHat_tameFrobenius (q : Fin 4) :
    freeHat (I.A.tameFrobenius q) = ((I.E.tameFrobenius q : GB) : Ghat) := by
  change ((freeMap (LocalElements.lift (I.E.tameFrobenius q)) : GB) : Ghat) = _
  rw [LocalElements.freeMap_lift]

theorem freeHat_cap (k : Fin 3) : freeHat (I.A.cap k) = ((I.E.cap k : GB) : Ghat) := by
  change ((freeMap (LocalElements.lift (I.E.cap k)) : GB) : Ghat) = _
  rw [LocalElements.freeMap_lift]

theorem freeHat_dyadic (P : Fin 2) (g : LocalSource) :
    freeHat (I.A.dyadic P g) = ((I.E.dyadic P (localPresentation g) : GB) : Ghat) := by
  change ((freeMap (I.E.dyadicLift P g) : GB) : Ghat) = _
  rw [LocalElements.freeMap_dyadicLift]

/-- The `σ̂`-stability hypotheses of the descent (`Cut.SourceLifts.SigmaStable`). -/
theorem sigmaStable : I.A.SigmaStable GB freeHat sigmaHat where
  sq_mem := sigmaHat_sq_mem
  conj := ⟨sigmaHat, by simp, by rw [MulAut.conj_apply, freeHat_conj, freeHat_conj, I.conj_compat]⟩
  tame_q := by
    obtain ⟨s, hs, h1, h2⟩ := I.tame_compat_q
    exact ⟨s, hs, by rw [MulAut.conj_apply, freeHat_tameInertia, freeHat_tameInertia, h1],
      by rw [MulAut.conj_apply, freeHat_tameFrobenius, freeHat_tameFrobenius, h2]⟩
  tame_r := by
    obtain ⟨s, hs, h1, h2⟩ := I.tame_compat_r
    exact ⟨s, hs, by rw [MulAut.conj_apply, freeHat_tameInertia, freeHat_tameInertia, h1],
      by rw [MulAut.conj_apply, freeHat_tameFrobenius, freeHat_tameFrobenius, h2]⟩
  dyadic := by
    obtain ⟨s, hs, h⟩ := I.dyadic_compat
    exact ⟨s, hs, fun g => by rw [MulAut.conj_apply, freeHat_dyadic, freeHat_dyadic, h]⟩
  cap := by
    obtain ⟨s, hs, h⟩ := I.cap_compat
    exact ⟨s, hs, by rw [MulAut.conj_apply, freeHat_cap, freeHat_cap, h]⟩
  frob7 := by
    obtain ⟨F, hF, hσF⟩ := I.frob7_compat
    exact ⟨F, by rw [freeHat_cap, hF], hσF⟩

theorem kernelHat_eq_map : I.kernelHat = I.A.kernel.map freeHat.toMonoidHom := by
  ext x
  rw [mem_kernelHat_iff]
  constructor
  · rintro ⟨hx, h1⟩
    obtain ⟨s, hs⟩ := freeMap_surjective (⟨x, hx⟩ : GB)
    refine ⟨s, ?_, ?_⟩
    · rw [← hs, projB_freeMap] at h1
      exact (QuotientGroup.eq_one_iff s).mp h1
    · change ((freeMap s : GB) : Ghat) = x
      rw [hs]
  · rintro ⟨s, hs, rfl⟩
    refine ⟨freeHat_mem s, ?_⟩
    change I.projB (freeMap s) = 1
    rw [projB_freeMap]
    exact I.A.projection_eq_one_of_mem hs

/-- **`kernelHat` is normal in `Ĝ`** (descent of the cut with the `σ̂`-compatibility). -/
instance kernelHat_normal : I.kernelHat.Normal := by
  rw [kernelHat_eq_map]
  exact I.A.kernelHat_normal GB freeHat freeHat_mem freeHat_onto genuineRelation
    detector_genuineRelation I.hgen sigmaHat I.sigmaStable mem_GB_or_inv_mul_mem

theorem freeHat_ker_le : freeHat.toMonoidHom.ker ≤ I.A.kernel := by
  intro g hg
  apply I.relationKernel_le_kernel
  change freeMap g = 1
  apply Subtype.ext
  exact hg

/-- **`Ĝ ⧸ kernelHat` is infinite.** -/
theorem infinite_quotient : Infinite (Ghat ⧸ I.kernelHat) := by
  have : (I.A.kernel.map freeHat.toMonoidHom).Normal := by
    rw [← kernelHat_eq_map]
    exact I.kernelHat_normal
  have h := I.A.infinite_hat I.hL genuineRelation detector_genuineRelation I.hgen
    freeHat.toMonoidHom I.freeHat_ker_le
  rw [kernelHat_eq_map]
  exact h

theorem kernelHat_le_magnusKer : I.kernelHat ≤ I.magnusKer := by
  intro x hx
  obtain ⟨hB, h1⟩ := (I.mem_kernelHat_iff x).mp hx
  refine (I.mem_magnusKer_iff x).mpr ⟨hB, ?_⟩
  change I.magnusQ (I.projB ⟨x, hB⟩) = 1
  rw [h1, map_one]

theorem kernelHat_le_core : I.kernelHat ≤ I.core :=
  le_sigmaCore_of_normal I.kernelHat_le_retainedKer

theorem kernelHat_le_detKer : I.kernelHat ≤ I.detKer :=
  le_sigmaCore_of_normal (le_inf I.kernelHat_le_retainedKer I.kernelHat_le_magnusKer)

/-- `kernelHat` as a closed subgroup. -/
def kernelHatClosed : ClosedSubgroup Ghat := ⟨I.kernelHat, I.isClosed_kernelHat⟩

instance kernelHatClosed_normal : I.kernelHatClosed.Normal := I.kernelHat_normal

end Input

end UnitDistance.Sqrt241.Retained
