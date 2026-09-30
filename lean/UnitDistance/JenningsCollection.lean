module

public import UnitDistance.GroupAugmentation
public import Mathlib.Data.List.Sort
public import Mathlib.Data.List.Duplicate
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section
set_option backward.privateInPublic true


/-!
# Collection of homogeneous words modulo the next actual augmentation power

The input coefficients specify literal commutator and square relations in
an actual group algebra. Their nonzero terms have the required homogeneous
degree, and their remainders lie in actual augmentation powers. The goal is
to derive ordered binary spanning from these relations, rather than assume
an adapted basis or a desired Hilbert value.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.JenningsCollection
open GroupAugmentation
variable (R G ι : Type*) [CommRing R] [Group G]
variable (x : ι → A R G) (w : ι → ℕ)

def wordValue (l : List ι) : A R G := (l.map x).prod

def wordDegree (l : List ι) : ℕ := (l.map w).sum

@[simp] theorem wordValue_nil : wordValue R G ι x [] = 1 := rfl
@[simp] theorem wordValue_cons (i : ι) (l : List ι) :
    wordValue R G ι x (i::l) = x i * wordValue R G ι x l := rfl
@[simp] theorem wordValue_append (l k : List ι) :
    wordValue R G ι x (l++k) = wordValue R G ι x l * wordValue R G ι x k := by
  simp [wordValue]
@[simp] theorem wordDegree_nil : wordDegree ι w [] = 0 := rfl
@[simp] theorem wordDegree_cons (i : ι) (l : List ι) :
    wordDegree ι w (i::l) = w i + wordDegree ι w l := rfl
@[simp] theorem wordDegree_append (l k : List ι) :
    wordDegree ι w (l++k) = wordDegree ι w l + wordDegree ι w k := by
  simp [wordDegree]

variable [LinearOrder ι]

def orderedSpan (n : ℕ) : Submodule R (A R G) :=
  Submodule.span R {a | ∃ l : List ι, l.Pairwise (· < ·) ∧
    n ≤ wordDegree ι w l ∧ a = wordValue R G ι x l}

def nextPowerSpan (n : ℕ) : Submodule R (A R G) :=
  orderedSpan R G ι x w n ⊔ power R G (n+1)

omit [LinearOrder ι] in
theorem wordValue_mem_power (hx : ∀ i, x i ∈ power R G (w i)) (l : List ι) :
    wordValue R G ι x l ∈ power R G (wordDegree ι w l) := by
  induction l with
  | nil => trivial
  | cons i l ih => exact mul_mem_add R G (hx i) ih

variable [Fintype ι]

/-- Actual finite coefficients for the homogeneous commutator and square
relations; no spanning or basis conclusion appears among these fields. -/
structure Relations where
  commutator : ι → ι → ι → R
  commutator_support : ∀ i j k, commutator i j k ≠ 0 → w k = w i + w j
  commutator_error : ∀ i j, x i*x j - x j*x i - ∑ k, commutator i j k • x k ∈
    power R G (w i+w j+1)
  square : ι → ι → R
  square_support : ∀ i k, square i k ≠ 0 → w k = 2*w i
  square_error : ∀ i, x i*x i - ∑ k, square i k • x k ∈ power R G (2*w i+1)

omit [Fintype ι] [LinearOrder ι] in
/-- The initial relation remains valid with actual words on both sides. -/
theorem context_error_mem_power (hx : ∀ i, x i ∈ power R G (w i))
    (l r : List ι) (a : A R G) (d : ℕ) (ha : a ∈ power R G d) :
    wordValue R G ι x l * a * wordValue R G ι x r ∈
      power R G (wordDegree ι w l+d+wordDegree ι w r) :=
  mul_mem_add R G (mul_mem_add R G (wordValue_mem_power R G ι x w hx l) ha)
    (wordValue_mem_power R G ι x w hx r)

omit [LinearOrder ι] in
/-- Inserting a linear combination is exactly the sum of the shorter words. -/
theorem context_sum (l r : List ι) (c : ι → R) :
    wordValue R G ι x l * (∑ k, c k • x k) * wordValue R G ι x r =
      ∑ k, c k • wordValue R G ι x (l++k::r) := by
  simp [Finset.mul_sum, Finset.sum_mul, mul_assoc]

/-- A homogeneous linear replacement is collected using only strictly
shorter words. -/
theorem context_linear_mem (N D : ℕ) (l r : List ι) (c : ι → R)
    (ih : ∀ q : List ι, q.length < N → wordValue R G ι x q ∈
      nextPowerSpan R G ι x w (wordDegree ι w q))
    (hlen : l.length+1+r.length < N)
    (hdegree : ∀ k, c k ≠ 0 → wordDegree ι w (l++k::r) = D) :
    wordValue R G ι x l * (∑ k, c k • x k) * wordValue R G ι x r ∈
      nextPowerSpan R G ι x w D := by
  rw [context_sum]
  apply Submodule.sum_mem
  intro k _
  by_cases hc : c k = 0
  · simp [hc]
  · have ht := ih (l++k::r) (by simp only [List.length_append, List.length_cons]; omega)
    rw [hdegree k hc] at ht
    exact Submodule.smul_mem _ _ ht

/-- An adjacent interchange is valid modulo the ordered span and the next
power, with only shorter-word collection used for its correction terms. -/
theorem swap_difference_mem (hx : ∀ i, x i ∈ power R G (w i))
    (rel : Relations R G ι x w) (N : ℕ)
    (ih : ∀ q : List ι, q.length < N → wordValue R G ι x q ∈
      nextPowerSpan R G ι x w (wordDegree ι w q))
    (l r : List ι) (i j : ι) (hlen : (l++i::j::r).length ≤ N) :
    wordValue R G ι x (l++i::j::r) - wordValue R G ι x (l++j::i::r) ∈
      nextPowerSpan R G ι x w (wordDegree ι w (l++i::j::r)) := by
  let D := wordDegree ι w (l++i::j::r)
  have hlinear := context_linear_mem R G ι x w N D l r (rel.commutator i j) ih
    (by simp only [List.length_append, List.length_cons] at hlen; omega) (by
      intro k hk
      simp only [wordDegree_append, wordDegree_cons, rel.commutator_support i j k hk, D]
      omega)
  have herr := context_error_mem_power R G ι x w hx l r
    (x i*x j - x j*x i - ∑ k, rel.commutator i j k • x k) (w i+w j+1)
    (rel.commutator_error i j)
  have hdegree : wordDegree ι w l+(w i+w j+1)+wordDegree ι w r = D+1 := by
    simp only [D,wordDegree_append,wordDegree_cons]
    omega
  rw [hdegree] at herr
  have herr' : wordValue R G ι x l *
      (x i*x j - x j*x i - ∑ k, rel.commutator i j k • x k) * wordValue R G ι x r ∈
      nextPowerSpan R G ι x w D :=
    (show power R G (D+1) ≤ nextPowerSpan R G ι x w D from le_sup_right) herr
  have he : wordValue R G ι x (l++i::j::r) - wordValue R G ι x (l++j::i::r) =
      wordValue R G ι x l * (∑ k, rel.commutator i j k • x k) * wordValue R G ι x r +
      wordValue R G ι x l * (x i*x j - x j*x i - ∑ k, rel.commutator i j k • x k) *
        wordValue R G ι x r := by
    simp only [wordValue_append, wordValue_cons]
    noncomm_ring
  rw [he]
  exact (nextPowerSpan R G ι x w D).add_mem hlinear herr'

/-- A repeated adjacent letter is replaced by strictly shorter words with
the same total homogeneous degree, modulo the next actual power. -/
theorem square_word_mem (hx : ∀ i, x i ∈ power R G (w i))
    (rel : Relations R G ι x w) (N : ℕ)
    (ih : ∀ q : List ι, q.length < N → wordValue R G ι x q ∈
      nextPowerSpan R G ι x w (wordDegree ι w q))
    (l r : List ι) (i : ι) (hlen : (l++i::i::r).length ≤ N) :
    wordValue R G ι x (l++i::i::r) ∈
      nextPowerSpan R G ι x w (wordDegree ι w (l++i::i::r)) := by
  let D := wordDegree ι w (l++i::i::r)
  have hlinear := context_linear_mem R G ι x w N D l r (rel.square i) ih
    (by simp only [List.length_append, List.length_cons] at hlen; omega) (by
      intro k hk
      simp only [wordDegree_append, wordDegree_cons, rel.square_support i k hk, D]
      omega)
  have herr := context_error_mem_power R G ι x w hx l r
    (x i*x i - ∑ k, rel.square i k • x k) (2*w i+1) (rel.square_error i)
  have hdegree : wordDegree ι w l+(2*w i+1)+wordDegree ι w r = D+1 := by
    simp only [D,wordDegree_append,wordDegree_cons]
    omega
  rw [hdegree] at herr
  have herr' : wordValue R G ι x l * (x i*x i - ∑ k, rel.square i k • x k) *
      wordValue R G ι x r ∈ nextPowerSpan R G ι x w D :=
    (show power R G (D+1) ≤ nextPowerSpan R G ι x w D from le_sup_right) herr
  have he : wordValue R G ι x (l++i::i::r) =
      wordValue R G ι x l * (∑ k, rel.square i k • x k) * wordValue R G ι x r +
      wordValue R G ι x l * (x i*x i - ∑ k, rel.square i k • x k) * wordValue R G ι x r := by
    simp only [wordValue_append, wordValue_cons]
    noncomm_ring
  rw [he]
  exact (nextPowerSpan R G ι x w D).add_mem hlinear herr'

/-- Permuting letters changes a word only by collected shorter correction
terms and the next augmentation power. Prefixes and suffixes are arbitrary. -/
theorem perm_difference_mem (hx : ∀ i, x i ∈ power R G (w i))
    (rel : Relations R G ι x w) (N : ℕ)
    (ih : ∀ q : List ι, q.length < N → wordValue R G ι x q ∈
      nextPowerSpan R G ι x w (wordDegree ι w q))
    {u v : List ι} (hp : u.Perm v) (l r : List ι)
    (hlen : (l++u++r).length ≤ N) :
    wordValue R G ι x (l++u++r) - wordValue R G ι x (l++v++r) ∈
      nextPowerSpan R G ι x w (wordDegree ι w (l++u++r)) := by
  induction hp generalizing l r with
  | nil => simp
  | cons a hp ihp =>
    simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using
      ihp (l++[a]) r (by simpa only [List.append_assoc, List.singleton_append,
        List.cons_append, List.nil_append] using hlen)
  | swap a b u =>
    simpa only [List.append_assoc, List.cons_append] using
      swap_difference_mem R G ι x w hx rel N ih l (u++r) b a
        (by simpa only [List.append_assoc,List.cons_append, List.nil_append] using hlen)
  | @trans u v t h₁ h₂ ih₁ ih₂ =>
    have hlen' : (l++v++r).length ≤ N := by
      simpa only [List.length_append, h₁.length_eq] using hlen
    have hv := ih₂ l r hlen'
    have hd : wordDegree ι w (l++v++r) = wordDegree ι w (l++u++r) := by
      exact (((h₁.append_left l).append_right r).map w).sum_eq.symm
    rw [hd] at hv
    have ht := (nextPowerSpan R G ι x w _).add_mem (ih₁ l r hlen) hv
    simpa only [sub_add_sub_cancel] using ht

/-- Homogeneous commutator and square collection proves binary ordered
spanning modulo the next actual power. The proof terminates on word length;
no rewrite-confluence or PBW spanning assumption is required. -/
theorem wordValue_mem_nextPowerSpan (hx : ∀ i, x i ∈ power R G (w i))
    (rel : Relations R G ι x w) (l : List ι) :
    wordValue R G ι x l ∈ nextPowerSpan R G ι x w (wordDegree ι w l) := by
  suffices ∀ N, ∀ q : List ι, q.length = N → wordValue R G ι x q ∈
      nextPowerSpan R G ι x w (wordDegree ι w q) from this l.length l rfl
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro q hq
    have hs : ∀ r : List ι, r.length < N → wordValue R G ι x r ∈
        nextPowerSpan R G ι x w (wordDegree ι w r) :=
      fun r hr => ih r.length hr r rfl
    by_cases hn : q.Nodup
    · let t := q.mergeSort (· ≤ ·)
      have hp : q.Perm t := (List.mergeSort_perm q (· ≤ ·)).symm
      have ht : t.Pairwise (· < ·) :=
        (List.sortedLE_mergeSort.sortedLT_of_nodup (hp.nodup_iff.mp hn)).pairwise
      have hd : wordDegree ι w t = wordDegree ι w q := (hp.map w).sum_eq.symm
      have hv : wordValue R G ι x t ∈ orderedSpan R G ι x w (wordDegree ι w q) :=
        Submodule.subset_span ⟨t, ht, hd.ge, rfl⟩
      have he := perm_difference_mem R G ι x w hx rel N hs hp [] [] (by simp [hq])
      simp only [List.nil_append,List.append_nil] at he
      have hv' : wordValue R G ι x t ∈ nextPowerSpan R G ι x w (wordDegree ι w q) :=
        (show orderedSpan R G ι x w _ ≤ nextPowerSpan R G ι x w _ from le_sup_left) hv
      simpa only [sub_add_cancel] using (nextPowerSpan R G ι x w _).add_mem he hv'
    · obtain ⟨i, hi⟩ := List.exists_duplicate_iff_not_nodup.mpr hn
      obtain ⟨r, hp⟩ := (List.duplicate_iff_sublist.mp hi).exists_perm_append
      have hp' : q.Perm (i::i::r) := hp
      have he := perm_difference_mem R G ι x w hx rel N hs hp' [] [] (by simp [hq])
      simp only [List.nil_append,List.append_nil] at he
      have hv := square_word_mem R G ι x w hx rel N hs [] r i
        (by simp only [List.nil_append]; exact hp'.length_eq ▸ hq.le)
      simp only [List.nil_append] at hv
      have hd : wordDegree ι w (i::i::r) = wordDegree ι w q := (hp'.map w).sum_eq.symm
      rw [hd] at hv
      simpa only [sub_add_cancel] using (nextPowerSpan R G ι x w _).add_mem he hv

end UnitDistance.JenningsCollection
