module

public import UnitDistance.JenningsCollection
public import UnitDistance.GroupAugmentationGenerators

@[expose] public section
set_option backward.privateInPublic true


/-!
# Exact augmentation filtration from collection and nilpotence

This proof converts literal homogeneous collection relations into exact
ordered spans. The hypotheses are group generation, positive actual letter
degrees, ordinary spanning, and actual augmentation nilpotence. The next
module supplies each of these for every finite 2-group.
-/

noncomputable section
namespace UnitDistance.JenningsCollection
open GroupAugmentation
variable (R G ι : Type*) [CommRing R] [Group G] [LinearOrder ι] [Fintype ι]
variable (x : ι → A R G) (w : ι → ℕ)

/-- Actual arbitrary words at or above a given weight. -/
def wordSpan (n : ℕ) : Submodule R (A R G) :=
  Submodule.span R {a | ∃ l : List ι, n ≤ wordDegree ι w l ∧ a = wordValue R G ι x l}

omit [Fintype ι] in
theorem orderedSpan_le_wordSpan (n : ℕ) :
    orderedSpan R G ι x w n ≤ wordSpan R G ι x w n := by
  apply Submodule.span_mono
  rintro a ⟨l,_,hl,rfl⟩
  exact ⟨l,hl,rfl⟩

omit [Fintype ι] in
theorem orderedSpan_antitone : Antitone (orderedSpan R G ι x w) := by
  intro n m hnm
  apply Submodule.span_mono
  rintro a ⟨l,hl,hm,rfl⟩
  exact ⟨l,hl,hnm.trans hm,rfl⟩

omit [Fintype ι] in
theorem nextPowerSpan_antitone : Antitone (nextPowerSpan R G ι x w) := by
  intro n m hnm
  exact sup_le_sup (orderedSpan_antitone R G ι x w hnm)
    (power_antitone R G (Nat.add_le_add_right hnm 1))

omit [Fintype ι] in
theorem orderedSpan_le_power (hx : ∀ i, x i ∈ power R G (w i)) (n : ℕ) :
    orderedSpan R G ι x w n ≤ power R G n := by
  apply Submodule.span_le.mpr
  rintro a ⟨l,_,hl,rfl⟩
  exact power_antitone R G hl (wordValue_mem_power R G ι x w hx l)

omit [LinearOrder ι] [Fintype ι] in
/-- Appending a positive-degree generator raises the word-span lower bound. -/
theorem wordSpan_mul_letter (hw : ∀ i, 1 ≤ w i) (n : ℕ) (i : ι) (a : A R G)
    (ha : a ∈ wordSpan R G ι x w n) : a*x i ∈ wordSpan R G ι x w (n+1) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨l,hl,rfl⟩ := ha
    apply Submodule.subset_span
    refine ⟨l++[i], ?_, ?_⟩
    · simp only [wordDegree_append, wordDegree_cons, wordDegree_nil]
      have hi := hw i
      omega
    · simp
  | zero => simp
  | add a b _ _ ha hb => simpa only [add_mul] using (wordSpan R G ι x w _).add_mem ha hb
  | smul c a _ ha => simpa only [smul_mul_assoc] using (wordSpan R G ι x w _).smul_mem c ha

omit [Fintype ι] in
/-- Group generation and ordinary spanning place each actual power in the
span of actual words of at least that weight. -/
theorem power_le_wordSpan (generators : ι → G)
    (hgen : Subgroup.closure (Set.range generators) = ⊤)
    (hx : ∀ i, x i = delta R (generators i)-1)
    (hw : ∀ i, 1 ≤ w i) (hspan : orderedSpan R G ι x w 0 = ⊤) (n : ℕ) :
    power R G n ≤ wordSpan R G ι x w n := by
  induction n with
  | zero =>
    exact (le_of_eq hspan.symm).trans (orderedSpan_le_wordSpan R G ι x w 0)
  | succ n ih =>
    rw [power_succ_eq_generatorImage R G generators hgen, generatorImage]
    apply iSup_le
    intro i
    rintro a ⟨b,hb,rfl⟩
    change b*(delta R (generators i)-1) ∈ _
    rw [← hx i]
    exact wordSpan_mul_letter R G ι x w hw n i b (ih hb)

/-- The collection theorem removes all ordering and repetition errors modulo
the next actual power, for every vector in the arbitrary-word span. -/
theorem wordSpan_le_nextPowerSpan (hx : ∀ i, x i ∈ power R G (w i))
    (rel : Relations R G ι x w) (n : ℕ) :
    wordSpan R G ι x w n ≤ nextPowerSpan R G ι x w n := by
  apply Submodule.span_le.mpr
  rintro a ⟨l,hl,rfl⟩
  exact nextPowerSpan_antitone R G ι x w hl
    (wordValue_mem_nextPowerSpan R G ι x w hx rel l)

/-- Nilpotence removes the next-power remainder by descending induction.
Consequently the actual powers are exactly the ordered weighted spans. -/
theorem orderedSpan_eq_power (generators : ι → G)
    (hgen : Subgroup.closure (Set.range generators) = ⊤)
    (hdelta : ∀ i, x i = delta R (generators i)-1)
    (hx : ∀ i, x i ∈ power R G (w i)) (hw : ∀ i, 1 ≤ w i)
    (hspan : orderedSpan R G ι x w 0 = ⊤) (rel : Relations R G ι x w)
    (N : ℕ) (hN : power R G N = ⊥) (n : ℕ) :
    orderedSpan R G ι x w n = power R G n := by
  apply le_antisymm (orderedSpan_le_power R G ι x w hx n)
  have happrox : ∀ n, power R G n ≤ nextPowerSpan R G ι x w n := fun n =>
    (power_le_wordSpan R G ι x w generators hgen hdelta hw hspan n).trans
      (wordSpan_le_nextPowerSpan R G ι x w hx rel n)
  have hdesc : ∀ k, power R G (N-k) ≤ orderedSpan R G ι x w (N-k) := by
    intro k
    induction k with
    | zero => simp [hN]
    | succ k ih =>
      by_cases hk : k < N
      · have he : N-k = (N-(k+1))+1 := by omega
        rw [he] at ih
        exact (happrox (N-(k+1))).trans (sup_le le_rfl
          (ih.trans (orderedSpan_antitone R G ι x w (Nat.le_succ _))))
      · have he : N-k = 0 := by omega
        have he' : N-(k+1) = 0 := by omega
        simpa only [he'] using (he ▸ ih)
  by_cases hn : n ≤ N
  · have he : N-(N-n) = n := by omega
    simpa only [he] using hdesc (N-n)
  · exact (power_antitone R G (by omega : N ≤ n)).trans (hN.le.trans bot_le)

end UnitDistance.JenningsCollection
