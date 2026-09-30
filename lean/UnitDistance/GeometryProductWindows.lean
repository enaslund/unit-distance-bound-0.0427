module

public import UnitDistance.SupportedProfile
public import UnitDistance.GeometryFinite
public import Mathlib.Topology.Algebra.InfiniteSum.Basic

@[expose] public section
set_option backward.privateInPublic true


/-!
# Compact supported energy windows for finite products

Lower bounds on the individual energies turn a bound on their sum into a
bound on each coordinate. This connects compact profile blocks to the
actual common energy window, whose shape need not be a product.
-/

open scoped Classical BigOperators

namespace UnitDistance

/-- The true common supported energy window is contained in an explicit
product of coordinate windows. No rectangular replacement is made. -/
theorem sum_energyWindow_subset_pi {ι : Type*} [Fintype ι]
    {X : ι → Type*} (S : ∀ i, Set (X i)) (E : ∀ i, X i → ℝ) (b : ι → ℝ)
    (hb : ∀ i x, x ∈ S i → b i ≤ E i x) (T : ℝ) :
    supportedWindow (Set.pi Set.univ S) (fun x => ∑ i, E i (x i)) T ⊆
      Set.pi Set.univ (fun i => supportedWindow (S i) (E i)
        (T-∑ j ∈ Finset.univ.erase i, b j)) := by
  classical
  rintro x ⟨hx, hsum⟩ i hi
  have hxi : x i ∈ S i := hx i (Set.mem_univ i)
  have hrest : (∑ j ∈ Finset.univ.erase i, b j) ≤
      ∑ j ∈ Finset.univ.erase i, E j (x j) :=
    Finset.sum_le_sum (fun j hj => hb j (x j) (hx j (Set.mem_univ j)))
  have hsplit := Finset.sum_erase_add Finset.univ (fun j => E j (x j)) (Finset.mem_univ i)
  exact ⟨hxi, by change E i (x i) ≤ T-_; change (∑ j, E j (x j)) ≤ T at hsum; linarith⟩

/-- A finite product of continuous lower-bounded supported profile energies
has a compact common energy window whenever all individual windows do. -/
theorem isCompact_sum_supportedWindow {ι : Type*} [Fintype ι]
    {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    (S : ∀ i, Set (X i)) (hS : ∀ i, IsClosed (S i))
    (E : ∀ i, X i → ℝ) (hE : ∀ i, Continuous (E i)) (b : ι → ℝ)
    (hb : ∀ i x, x ∈ S i → b i ≤ E i x)
    (hcompact : ∀ i T, IsCompact (supportedWindow (S i) (E i) T)) (T : ℝ) :
    IsCompact (supportedWindow (Set.pi Set.univ S) (fun x => ∑ i, E i (x i)) T) := by
  classical
  have hm : Continuous (fun x : ∀ i, X i => ∑ i, E i (x i)) :=
    continuous_finsetSum _ (fun i hi => (hE i).comp (continuous_apply i))
  have hc : IsClosed (supportedWindow (Set.pi Set.univ S) (fun x => ∑ i, E i (x i)) T) :=
    (isClosed_set_pi (fun i hi => hS i)).inter (isClosed_le hm continuous_const)
  exact (isCompact_univ_pi (fun i => hcompact i
    (T-∑ j ∈ Finset.univ.erase i, b j))).of_isClosed_subset hc
      (sum_energyWindow_subset_pi S E b hb T)

/-- The everywhere-positive case has no support restriction. -/
theorem isCompact_sum_energyWindow {ι : Type*} [Fintype ι]
    {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    (E : ∀ i, X i → ℝ) (hE : ∀ i, Continuous (E i)) (b : ι → ℝ)
    (hb : ∀ i x, b i ≤ E i x)
    (hcompact : ∀ i T, IsCompact (energyWindow (E i) T)) (T : ℝ) :
    IsCompact (energyWindow (fun x : ∀ i, X i => ∑ i, E i (x i)) T) := by
  have h := isCompact_sum_supportedWindow (fun i => (Set.univ : Set (X i)))
    (fun _ => isClosed_univ) E hE b (fun i x _ => hb i x)
    (fun i T => by simpa [supportedWindow] using hcompact i T) T
  simpa [supportedWindow] using h

end UnitDistance
