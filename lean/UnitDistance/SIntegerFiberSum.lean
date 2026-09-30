module

public import UnitDistance.SIntegerFundamentalDomain
public import UnitDistance.FiniteCosetWeightedSum

@[expose] public section
set_option backward.privateInPublic true


/-!
# Actual S-integer cosets inherit the proved ideal-lattice bound

The finite completion class of an S-integer selects an actual translate of
the period ideal. Subtracting a point in a nonempty fiber gives an injective
finite subset of the original Euclidean ideal lattice.
-/

noncomputable section
open Set MeasureTheory NumberField IsDedekindDomain
open scoped Classical BigOperators nonZeroDivisors
namespace UnitDistance.SIntegerCRT

variable {K : Type} [Field K] [NumberField K] {T : Type*} [Fintype T]

theorem sInteger_coset_archimedean_sum_le
    (P : T → HeightOneSpectrum (𝓞 K)) (hP : Function.Injective P) (a : T → ℤ)
    (f : EuclideanIdeal.Space K → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ r (s : Finset (EuclideanIdeal.lattice K (periodIdeal P a))),
      (∑ v ∈ s, f (r+(v : EuclideanIdeal.Space K))) ≤ C)
    (s : Finset ((Set.range P).integer K))
    (r : EuclideanIdeal.Space K) (t : LocalProduct P) (c : LocalProduct P ⧸ finitePeriod P a) :
    (∑ x ∈ s.filter (fun x : (Set.range P).integer K => QuotientAddGroup.mk' (finitePeriod P a)
      (localEmbedding P (x : K)+t) = c), f (r+EuclideanIdeal.embedding K (x : K))) ≤ C := by
  let A : Finset ((Set.range P).integer K) := s.filter (fun x : (Set.range P).integer K => QuotientAddGroup.mk' (finitePeriod P a)
    (localEmbedding P (x : K)+t) = c)
  change (∑ x ∈ A, f (r+EuclideanIdeal.embedding K (x : K))) ≤ C
  by_cases hA : A.Nonempty
  · obtain ⟨y, hy⟩ := hA
    have hd (x : A) : (x.val : K)-(y : K) ∈ (periodIdeal P a).val := by
      apply (finitePeriod_fiber_iff P hP a (y : K) y.property (x.val : K)).mp
      refine ⟨x.val.property, ?_⟩
      have hh := (Finset.mem_filter.mp x.property).2.trans (Finset.mem_filter.mp hy).2.symm
      have hp := QuotientAddGroup.eq_iff_sub_mem.mp hh
      simpa only [add_sub_add_right_eq_sub] using hp
    let d : A → EuclideanIdeal.lattice K (periodIdeal P a) := fun x =>
      EuclideanIdeal.idealLatticeEquiv K (periodIdeal P a) ⟨(x.val : K)-(y : K), hd x⟩
    have hdinj : Function.Injective d := by
      intro x z h
      have he := congrArg Subtype.val ((EuclideanIdeal.idealLatticeEquiv K (periodIdeal P a)).injective h)
      apply Subtype.ext
      apply Subtype.ext
      exact sub_left_injective he
    have he (x : A) :
        (r+EuclideanIdeal.embedding K (y : K))+(d x : EuclideanIdeal.Space K) =
          r+EuclideanIdeal.embedding K (x.val : K) := by
      change (r+EuclideanIdeal.embedding K (y : K))+
        EuclideanIdeal.embedding K ((x.val : K)-(y : K)) = _
      simp only [EuclideanIdeal.embedding, map_sub]
      abel
    have hb := hf (r+EuclideanIdeal.embedding K (y : K)) (A.attach.image d)
    rw [Finset.sum_image (fun x _ z _ h => hdinj h)] at hb
    simp_rw [he] at hb
    have hs := Finset.sum_attach A (fun x : (Set.range P).integer K =>
      f (r+EuclideanIdeal.embedding K (x : K)))
    exact hs ▸ hb
  · rw [Finset.not_nonempty_iff_eq_empty.mp hA, Finset.sum_empty]
    exact hC

end UnitDistance.SIntegerCRT
