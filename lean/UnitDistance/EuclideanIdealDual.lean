module

public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import UnitDistance.MinkowskiTrace
public import UnitDistance.ThirdParty.PoissonSummation

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual ideal lattices with the ordinary Euclidean metric

The coordinate equivalence preserves ordinary Lebesgue measure. The dual
identification includes conjugation and a factor two at every complex place.
No automorphism of the number field is identified with coordinate conjugation.
-/

noncomputable section
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory DedekindZeta
open scoped nonZeroDivisors Classical RealInnerProductSpace
namespace UnitDistance.EuclideanIdeal
variable (K : Type*) [Field K] [NumberField K]

abbrev Space := mixedEmbedding.euclidean.mixedSpace K
abbrev coordinates := mixedEmbedding.euclidean.toMixed K

def embedding (a : K) : Space K := (coordinates K).symm (mixedEmbedding K a)

def lattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : Submodule ℤ (Space K) :=
  ZLattice.comap ℝ (mixedEmbedding.idealLattice K I) (coordinates K).toLinearMap

instance (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : DiscreteTopology (lattice K I) := by
  unfold lattice
  infer_instance

instance (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : IsZLattice ℝ (lattice K I) := by
  unfold lattice
  infer_instance

theorem covolume_lattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ZLattice.covolume (lattice K I) =
      (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) *
        (2⁻¹)^nrComplexPlaces K * Real.sqrt |(discr K : ℝ)| := by
  rw [lattice, ZLattice.covolume_comap _ _ _
    (mixedEmbedding.euclidean.volumePreserving_toMixed K),
    mixedEmbedding.covolume_idealLattice]

theorem mem_lattice_iff (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (y : Space K) :
    y ∈ lattice K I ↔ ∃ a ∈ (I : FractionalIdeal (𝓞 K)⁰ K), embedding K a = y := by
  change coordinates K y ∈ mixedEmbedding.idealLattice K I ↔ _
  rw [mixedEmbedding.mem_idealLattice]
  refine exists_congr fun a => and_congr_right fun _ => ?_
  rw [embedding, ContinuousLinearEquiv.symm_apply_eq]

def traceCoordinates (ξ : mixedSpace K) : mixedSpace K :=
  (ξ.1, fun w => (starRingEnd ℂ (ξ.2 w)) / 2)

def dualCoordinates (ξ : mixedSpace K) : mixedSpace K :=
  (ξ.1, fun w => 2 * starRingEnd ℂ (ξ.2 w))

omit [NumberField K] in
@[simp] theorem dual_traceCoordinates (ξ : mixedSpace K) :
    dualCoordinates K (traceCoordinates K ξ) = ξ := by
  ext w <;> simp [dualCoordinates, traceCoordinates, map_ofNat]
  ring

omit [NumberField K] in
@[simp] theorem trace_dualCoordinates (ξ : mixedSpace K) :
    traceCoordinates K (dualCoordinates K ξ) = ξ := by
  ext w <;> simp [dualCoordinates, traceCoordinates, map_ofNat]

theorem inner_embedding (y : Space K) (a : K) :
    inner ℝ y (embedding K a) =
      MinkowskiTrace.traceForm K (traceCoordinates K (coordinates K y)) a := by
  rw [WithLp.prod_inner_apply]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, real_inner_eq_re_inner ℂ]
  unfold MinkowskiTrace.traceForm traceCoordinates
  simp only [Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro w _
    change (mixedEmbedding K a).1 w * (coordinates K y).1 w = _
    ring
  · apply Finset.sum_congr rfl
    intro w _
    change ((mixedEmbedding K a).2 w * starRingEnd ℂ ((coordinates K y).2 w)).re = _
    simp only [div_mul_eq_mul_div, Complex.div_ofNat_re]
    rw [mul_comm ((mixedEmbedding K a).2 w)]
    ring

/-- The full ordinary Euclidean dual of a nonzero integral ideal lattice. -/
theorem mem_dual_lattice_iff (I : Ideal (𝓞 K)) (hI : I ≠ 0) (y : Space K) :
    y ∈ PoissonSummation.dualLattice
        (lattice K (Units.mk0 (I : FractionalIdeal (𝓞 K)⁰ K)
          (FractionalIdeal.coeIdeal_ne_zero.mpr hI))) ↔
      ∃ b ∈ (MinkowskiTrace.dualIdeal K I : Submodule (𝓞 K) K),
        coordinates K y = dualCoordinates K (mixedEmbedding K b) := by
  rw [PoissonSummation.mem_dualLattice]
  have hgen : (∀ x ∈ lattice K (Units.mk0 (I : FractionalIdeal (𝓞 K)⁰ K)
        (FractionalIdeal.coeIdeal_ne_zero.mpr hI)), inner ℝ y x ∈ (1 : Submodule ℤ ℝ)) ↔
      ∀ a ∈ (I : FractionalIdeal (𝓞 K)⁰ K),
        ∃ k : ℤ, MinkowskiTrace.traceForm K (traceCoordinates K (coordinates K y)) a = k := by
    constructor
    · intro h a ha
      obtain ⟨k, hk⟩ := Submodule.mem_one.mp (h (embedding K a)
        ((mem_lattice_iff K _ _).mpr ⟨a, ha, rfl⟩))
      exact ⟨k, by rw [inner_embedding] at hk; simpa using hk.symm⟩
    · intro h x hx
      obtain ⟨a, ha, rfl⟩ := (mem_lattice_iff K _ x).mp hx
      obtain ⟨k, hk⟩ := h a ha
      refine Submodule.mem_one.mpr ⟨k, ?_⟩
      rw [inner_embedding]
      simpa using hk.symm
  rw [hgen, MinkowskiTrace.traceForm_int_iff_exists_dualIdeal K I hI]
  refine exists_congr fun b => and_congr_right fun _ => ?_
  constructor
  · intro h
    rw [h, dual_traceCoordinates]
  · intro h
    rw [h, trace_dualCoordinates]

end UnitDistance.EuclideanIdeal
