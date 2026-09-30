module

public import UnitDistance.PeriodicHaarSum
public import Mathlib.GroupTheory.QuotientGroup.Defs

@[expose] public section
set_option backward.privateInPublic true


/-!
# Combining an ideal-fiber bound with an actual local profile integral

A finite set is partitioned by its actual finite-place cosets. The bound on
each archimedean fiber and the Haar mass of the local periodic profile combine
at the same translate. No equidistribution or count of occupied cosets is
assumed.
-/

noncomputable section
open Set MeasureTheory
open scoped Classical BigOperators
namespace UnitDistance

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]
  (μ : Measure G) [μ.IsAddRightInvariant]

theorem periodic_eq_of_quotient_eq (P : AddSubgroup G) (g : G → ℝ)
    (hg : ∀ p ∈ P, ∀ x, g (x+p) = g x) {x y : G}
    (h : QuotientAddGroup.mk' P x = QuotientAddGroup.mk' P y) : g x = g y := by
  have hp : x-y ∈ P := QuotientAddGroup.eq_iff_sub_mem.mp h
  have he := hg (x-y) hp y
  rwa [show y+(x-y) = x by abel] at he

theorem finite_weighted_coset_sum_mul_measureReal_le
    (P : AddSubgroup G) (hP : MeasurableSet (P : Set G))
    (g : G → ℝ) (hg0 : ∀ x, 0 ≤ g x) (hgi : Integrable g μ)
    (hg : ∀ p ∈ P, ∀ x, g (x+p) = g x)
    {A : Type*} (s : Finset A) (location : A → G) (f : A → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ c : G ⧸ P, (∑ a ∈ s.filter
      (fun a => QuotientAddGroup.mk' P (location a) = c), f a) ≤ C) :
    (∑ a ∈ s, f a*g (location a))*μ.real P ≤ C*(∫ x, g x ∂μ) := by
  let q : A → G ⧸ P := fun a => QuotientAddGroup.mk' P (location a)
  let J := s.image q
  let r : G ⧸ P → G := fun c => (QuotientAddGroup.mk'_surjective P c).choose
  have hr (c : G ⧸ P) : QuotientAddGroup.mk' P (r c) = c :=
    (QuotientAddGroup.mk'_surjective P c).choose_spec
  have hsum : (∑ a ∈ s, f a*g (location a)) ≤ C*(∑ c ∈ J, g (r c)) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := s) (t := J) (g := q)
      (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩) (fun a => f a*g (location a)),
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro c hc
    have he (a : A) (ha : a ∈ s.filter (fun a => q a = c)) :
        g (location a) = g (r c) := by
      apply periodic_eq_of_quotient_eq P g hg
      exact (Finset.mem_filter.mp ha).2.trans (hr c).symm
    calc
      (∑ a ∈ s.filter (fun a => q a = c), f a*g (location a)) =
          ∑ a ∈ s.filter (fun a => q a = c), f a*g (r c) :=
        Finset.sum_congr rfl (fun a ha => congrArg (fun t => f a*t) (he a ha))
      _ = (∑ a ∈ s.filter (fun a => q a = c), f a)*g (r c) := (Finset.sum_mul ..).symm
      _ ≤ C*g (r c) := mul_le_mul_of_nonneg_right (hf c) (hg0 _)
  have hlocal := periodic_finite_coset_sum_mul_measureReal_le μ P hP g hg0 hgi hg J r
    (fun i _ j _ hij hp => hij (by
      have hh : QuotientAddGroup.mk' P (r i) = QuotientAddGroup.mk' P (r j) :=
        QuotientAddGroup.eq_iff_sub_mem.mpr hp
      simpa only [hr] using hh))
  calc
    (∑ a ∈ s, f a*g (location a))*μ.real P ≤
        (C*(∑ c ∈ J, g (r c)))*μ.real P :=
      mul_le_mul_of_nonneg_right hsum measureReal_nonneg
    _ = C*((∑ c ∈ J, g (r c))*μ.real P) := mul_assoc _ _ _
    _ ≤ C*(∫ x, g x ∂μ) := mul_le_mul_of_nonneg_left hlocal hC

end UnitDistance
