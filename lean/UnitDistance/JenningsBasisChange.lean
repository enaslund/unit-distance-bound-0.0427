module

public import UnitDistance.JenningsFilteredBasis

@[expose] public section
set_option backward.privateInPublic true


/-!
# Changing and reordering actual homogeneous Jennings directions

The finite-group weighted theorem is transported to any finite ordered family
of actual group differences spanning every actual dimension layer. The order
need not respect degree. This permits all prescribed subgroup directions to
come after their ambient complements.
-/

noncomputable section
open scoped BigOperators
namespace UnitDistance.JenningsCollection
open GroupAugmentation
variable (R G ι : Type*) [CommRing R] [Group G]
variable (x : ι → A R G) (w : ι → ℕ)

theorem wordSpan_le_power (hx : ∀ i, x i ∈ power R G (w i)) (n : ℕ) :
    wordSpan R G ι x w n ≤ power R G n := by
  apply Submodule.span_le.mpr
  rintro a ⟨l,hl,rfl⟩
  exact power_antitone R G hl (wordValue_mem_power R G ι x w hx l)

theorem wordSpan_antitone : Antitone (wordSpan R G ι x w) := by
  intro n m hnm
  apply Submodule.span_mono
  rintro a ⟨l,hl,rfl⟩
  exact ⟨l,hnm.trans hl,rfl⟩

theorem wordSpan_mul {m n : ℕ} {a b : A R G}
    (ha : a ∈ wordSpan R G ι x w m) (hb : b ∈ wordSpan R G ι x w n) :
    a*b ∈ wordSpan R G ι x w (m+n) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨l,hl,rfl⟩ := ha
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨k,hk,rfl⟩ := hb
      exact Submodule.subset_span ⟨l++k, by simpa using Nat.add_le_add hl hk, by simp⟩
    | zero => simp
    | add b c _ _ hb hc => simpa only [mul_add] using Submodule.add_mem _ hb hc
    | smul c b _ hb => simpa only [mul_smul_comm] using Submodule.smul_mem _ c hb
  | zero => simp
  | add a c _ _ ha hc => simpa only [add_mul] using Submodule.add_mem _ ha hc
  | smul c a _ ha => simpa only [smul_mul_assoc] using Submodule.smul_mem _ c ha

/-- Word spanning with a remainder in the next actual power. -/
def approximateWordSpan (n : ℕ) : Submodule R (A R G) :=
  wordSpan R G ι x w n ⊔ power R G (n+1)

theorem approximateWordSpan_antitone : Antitone (approximateWordSpan R G ι x w) := by
  intro n m hnm
  exact sup_le_sup (wordSpan_antitone R G ι x w hnm)
    (power_antitone R G (Nat.add_le_add_right hnm 1))

/-- Substituting homogeneous linear forms into a product preserves its
total degree, including all mixed error terms. -/
theorem approximateWordSpan_mul (hx : ∀ i, x i ∈ power R G (w i))
    {m n : ℕ} {a b : A R G}
    (ha : a ∈ approximateWordSpan R G ι x w m)
    (hb : b ∈ approximateWordSpan R G ι x w n) :
    a*b ∈ approximateWordSpan R G ι x w (m+n) := by
  obtain ⟨a₀,ha₀,a₁,ha₁,rfl⟩ := Submodule.mem_sup.mp ha
  obtain ⟨b₀,hb₀,b₁,hb₁,rfl⟩ := Submodule.mem_sup.mp hb
  have h₀ : a₀*b₀ ∈ approximateWordSpan R G ι x w (m+n) :=
    (show wordSpan R G ι x w (m+n) ≤ approximateWordSpan R G ι x w (m+n)
      from le_sup_left) (wordSpan_mul R G ι x w ha₀ hb₀)
  have h₁ : a₀*b₁ ∈ power R G (m+n+1) := by
    simpa only [Nat.add_assoc] using
      mul_mem_add R G (wordSpan_le_power R G ι x w hx m ha₀) hb₁
  have h₂ : a₁*b₀ ∈ power R G (m+n+1) := by
    have he : (m+1)+n = m+n+1 := by omega
    simpa only [he] using mul_mem_add R G ha₁ (wordSpan_le_power R G ι x w hx n hb₀)
  have h₃ : a₁*b₁ ∈ power R G (m+n+1) :=
    power_antitone R G (by omega : m+n+1 ≤ (m+1)+(n+1)) (mul_mem_add R G ha₁ hb₁)
  have hle : power R G (m+n+1) ≤ approximateWordSpan R G ι x w (m+n) := le_sup_right
  rw [add_mul, mul_add, mul_add]
  exact Submodule.add_mem _ (Submodule.add_mem _ h₀ (hle h₁))
    (Submodule.add_mem _ (hle h₂) (hle h₃))

theorem homogeneousLinearSpan_le_wordSpan (n : ℕ) :
    homogeneousLinearSpan R G ι x w n ≤ wordSpan R G ι x w n := by
  apply Submodule.span_le.mpr
  rintro a ⟨i,hi,rfl⟩
  exact Submodule.subset_span ⟨[i], by simp [hi], by simp⟩

end UnitDistance.JenningsCollection

namespace UnitDistance.GroupAugmentation
open JenningsCollection
variable (G : Type*) [Group G] [Finite G] (hG : IsPGroup 2 G)
variable (ι : Type*) [LinearOrder ι] [Fintype ι]
variable (g : ι → G) (w : ι → ℕ)

/-- A finite family spans actual homogeneous group differences if each
dimension-subgroup difference has a linear expansion of the same degree
modulo the next actual augmentation power. -/
def SpansActualLayers : Prop :=
  ∀ n, 1 ≤ n → ∀ a : dimensionSubgroup (ZMod 2) G n,
    ∃ b ∈ homogeneousLinearSpan (ZMod 2) G ι (fun i => delta (ZMod 2) (g i)-1) w n,
      delta (ZMod 2) (a : G)-1-b ∈ power (ZMod 2) G (n+1)

omit hG in
/-- Actual layer spanning supplies literal collection coefficients for any
chosen order of the directions. -/
def relationsOfSpansActualLayers
    (hw : ∀ i, 1 ≤ w i)
    (hg : ∀ i, g i ∈ dimensionSubgroup (ZMod 2) G (w i))
    (hspan : SpansActualLayers G ι g w) :
    Relations (ZMod 2) G ι (fun i => delta (ZMod 2) (g i)-1) w := by
  apply Relations.of_remainders
  · intro i j
    let a : dimensionSubgroup (ZMod 2) G (w i) := ⟨g i,hg i⟩
    let b : dimensionSubgroup (ZMod 2) G (w j) := ⟨g j,hg j⟩
    let c : dimensionSubgroup (ZMod 2) G (w i+w j) :=
      ⟨g i*g j*(g i)⁻¹*(g j)⁻¹,commutator_mem (ZMod 2) G (hg i) (hg j)⟩
    letI : Fact (1 ≤ w i+w j) := ⟨by have := hw i; omega⟩
    obtain ⟨v,hv,he⟩ := hspan (w i+w j) Fact.out c
    refine ⟨v,hv,?_⟩
    have hc := commutator_initial_form G (w j) (w i) a b
    have hd := difference_sub_initial_mem G (w i+w j) c
    have ht := (power (ZMod 2) G (w i+w j+1)).add_mem
      ((power (ZMod 2) G (w i+w j+1)).sub_mem hc hd) he
    convert ht using 1 <;> dsimp [a,b,c] <;> abel
  · intro i
    let a : dimensionSubgroup (ZMod 2) G (w i) := ⟨g i,hg i⟩
    let c : dimensionSubgroup (ZMod 2) G (2*w i) := ⟨g i^2,square_mem (ZMod 2) G (hg i)⟩
    letI : Fact (1 ≤ 2*w i) := ⟨by have := hw i; omega⟩
    obtain ⟨v,hv,he⟩ := hspan (2*w i) Fact.out c
    refine ⟨v,hv,?_⟩
    have hc := square_initial_form G (w i) a
    have hd := difference_sub_initial_mem G (2*w i) c
    have ht := (power (ZMod 2) G (2*w i+1)).add_mem
      ((power (ZMod 2) G (2*w i+1)).sub_mem hc hd) he
    convert ht using 1 <;> dsimp [a,c] <;> abel

include hG in
/-- The already-proved canonical Jennings monomials can be expanded in any
actual homogeneous spanning family, preserving weights modulo the next power. -/
theorem power_le_approximateWordSpan_of_spansActualLayers
    (hg : ∀ i, g i ∈ dimensionSubgroup (ZMod 2) G (w i))
    (hspan : SpansActualLayers G ι g w) (n : ℕ) :
    power (ZMod 2) G n ≤
      approximateWordSpan (ZMod 2) G ι (fun i => delta (ZMod 2) (g i)-1) w n := by
  have hletter : ∀ i : Fin (homogeneousDifferences G).length,
      (homogeneousDifferences G).get i ∈
        approximateWordSpan (ZMod 2) G ι (fun i => delta (ZMod 2) (g i)-1) w
          (groupDegree G hG (monomialLetter G i)) := by
    intro i
    obtain ⟨b,hb,he⟩ := hspan (groupDegree G hG (monomialLetter G i))
      (monomialLetter_degree_pos G hG i)
      ⟨monomialLetter G i, mem_dimensionSubgroup_groupDegree G hG _⟩
    rw [get_homogeneousDifferences]
    apply Submodule.mem_sup.mpr
    exact ⟨b,homogeneousLinearSpan_le_wordSpan (ZMod 2) G ι _ w _ hb,
      delta (ZMod 2) (monomialLetter G i)-1-b,he,by abel⟩
  have hword : ∀ l : List (Fin (homogeneousDifferences G).length),
      wordValue (ZMod 2) G _ (fun i => (homogeneousDifferences G).get i) l ∈
        approximateWordSpan (ZMod 2) G ι (fun i => delta (ZMod 2) (g i)-1) w
          (wordDegree _ (fun i => groupDegree G hG (monomialLetter G i)) l) := by
    intro l
    induction l with
    | nil =>
      apply (show wordSpan (ZMod 2) G ι _ w 0 ≤ approximateWordSpan (ZMod 2) G ι _ w 0
        from le_sup_left)
      exact Submodule.subset_span ⟨[],by simp,by simp⟩
    | cons i l ih => exact approximateWordSpan_mul (ZMod 2) G ι _ w hg (hletter i) ih
  rw [← weightedMonomialSpan_eq_power G hG n, ← orderedSpan_eq_weightedMonomialSpan]
  apply Submodule.span_le.mpr
  rintro a ⟨l,_,hl,rfl⟩
  exact approximateWordSpan_antitone (ZMod 2) G ι _ w hl (hword l)

include hG in
/-- The actual weighted Jennings spanning theorem is independent of the
chosen spanning directions and of their total order. -/
theorem orderedSpan_eq_power_of_spansActualLayers
    (hw : ∀ i, 1 ≤ w i)
    (hg : ∀ i, g i ∈ dimensionSubgroup (ZMod 2) G (w i))
    (hspan : SpansActualLayers G ι g w) (n : ℕ) :
    orderedSpan (ZMod 2) G ι (fun i => delta (ZMod 2) (g i)-1) w n =
      power (ZMod 2) G n := by
  let x := fun i => delta (ZMod 2) (g i)-1
  let rel := relationsOfSpansActualLayers G ι g w hw hg hspan
  apply le_antisymm (orderedSpan_le_power (ZMod 2) G ι x w hg n)
  have happrox : ∀ n, power (ZMod 2) G n ≤ nextPowerSpan (ZMod 2) G ι x w n := by
    intro n
    exact (power_le_approximateWordSpan_of_spansActualLayers G hG ι g w hg hspan n).trans
      (sup_le (wordSpan_le_nextPowerSpan (ZMod 2) G ι x w hg rel n) le_sup_right)
  let N := Nat.card G
  have hN : power (ZMod 2) G N = ⊥ := power_card_eq_bot G 2 hG
  have hdesc : ∀ k, power (ZMod 2) G (N-k) ≤ orderedSpan (ZMod 2) G ι x w (N-k) := by
    intro k
    induction k with
    | zero => simp [hN]
    | succ k ih =>
      by_cases hk : k < N
      · have he : N-k = (N-(k+1))+1 := by omega
        rw [he] at ih
        exact (happrox (N-(k+1))).trans (sup_le le_rfl
          (ih.trans (orderedSpan_antitone (ZMod 2) G ι x w (Nat.le_succ _))))
      · have he : N-k = 0 := by omega
        have he' : N-(k+1) = 0 := by omega
        simpa only [he'] using (he ▸ ih)
  by_cases hn : n ≤ N
  · have he : N-(N-n) = n := by omega
    simpa only [he] using hdesc (N-n)
  · exact (power_antitone (ZMod 2) G (by omega : N ≤ n)).trans (hN.le.trans bot_le)

end UnitDistance.GroupAugmentation
