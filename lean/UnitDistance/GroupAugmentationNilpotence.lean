module

public import UnitDistance.GroupAugmentation
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

@[expose] public section
set_option backward.privateInPublic true


/-!
# Nilpotence of the actual augmentation ideal for finite p-groups

The proof proceeds through fixed vectors over the finite field, obtained
from the orbit-counting theorem for p-group actions. This avoids assuming
Jennings or nilpotence as an input to the ambient filtration construction.
-/

noncomputable section
namespace UnitDistance.GroupAugmentation

/-- Every nonzero finite-dimensional representation of a p-group over
`𝔽_p` has a nonzero invariant vector. This is a consequence of actual orbit
counting on the finite underlying vector space. -/
theorem exists_nonzero_fixed_vector
    (p : ℕ) [Fact p.Prime] (G V : Type*) [Group G]
    [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    [Nontrivial V] (hG : IsPGroup p G) (ρ : Representation (ZMod p) G V) :
    ∃ v : V, v ≠ 0 ∧ ∀ g : G, ρ g v = v := by
  letI : MulAction G V := {
    smul g v := ρ g v
    one_smul v := by change ρ 1 v = v; simp
    mul_smul g h v := by change ρ (g*h) v = ρ g (ρ h v); simp [map_mul] }
  have hcard : Nat.card V = p ^ Module.finrank (ZMod p) V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  haveI : Finite V := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  have hpV : p ∣ Nat.card V := by
    rw [hcard]
    exact dvd_pow_self _ (Nat.ne_of_gt (Module.finrank_pos (R := ZMod p) (M := V)))
  have hz : (0 : V) ∈ MulAction.fixedPoints G V := by
    intro g
    exact map_zero (ρ g)
  obtain ⟨v,hv,hnz⟩ := hG.exists_fixed_point_of_prime_dvd_card_of_fixed_point V hpV hz
  exact ⟨v, Ne.symm hnz, hv⟩

variable (R G : Type*) [CommRing R] [Group G]

/-- Vectors annihilated on the left by every element of the n-th actual
augmentation power. This is the natural increasing annihilator filtration. -/
def annihilator (n : ℕ) : Submodule R (A R G) where
  carrier := {a | ∀ b ∈ power R G n, b*a = 0}
  zero_mem' := by intro b _; simp
  add_mem' ha hb := by intro b h; simp [mul_add, ha b h, hb b h]
  smul_mem' r a ha := by intro b h; simp [ha b h]

@[simp] theorem mem_annihilator (n : ℕ) (a : A R G) :
    a ∈ annihilator R G n ↔ ∀ b ∈ power R G n, b*a = 0 := Iff.rfl

@[simp] theorem annihilator_zero : annihilator R G 0 = ⊥ := by
  ext a
  constructor
  · intro ha
    have ht := ha 1 (by trivial)
    simpa using ht
  · intro ha
    rw [Submodule.mem_bot] at ha
    subst a
    exact Submodule.zero_mem _

theorem annihilator_mono : Monotone (annihilator R G) := by
  intro m n h a ha b hb
  exact ha b (power_antitone R G h hb)

/-- These annihilators are invariant under the actual left regular action. -/
theorem mul_mem_annihilator (n : ℕ) (a c : A R G)
    (ha : a ∈ annihilator R G n) : c*a ∈ annihilator R G n := by
  intro b hb
  rw [← mul_assoc]
  exact ha (b*c) (mul_mem_right R G n b c hb)

/-- The ordinary left regular representation in the group algebra. -/
def leftRegular : Representation R G (A R G) where
  toFun g :=
    { toFun := fun a => delta R g * a
      map_add' := fun _ _ => mul_add ..
      map_smul' := fun _ _ => mul_smul_comm .. }
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [← mul_assoc]

/-- The left regular representation on the quotient by an actual
annihilator layer. -/
def annihilatorQuotient (n : ℕ) :
    Representation R G (A R G ⧸ annihilator R G n) :=
  (leftRegular R G).quotient (annihilator R G n)
    (fun g a ha => mul_mem_annihilator R G n a (delta R g) ha)

@[simp] theorem annihilatorQuotient_mk (n : ℕ) (g : G) (a : A R G) :
    annihilatorQuotient R G n g ((annihilator R G n).mkQ a) =
      (annihilator R G n).mkQ (delta R g * a) := rfl

/-- A quotient-fixed vector belongs to the next annihilator layer.
This connects the finite orbit argument to the actual augmentation powers. -/
theorem mem_annihilator_succ_of_fixed (n : ℕ) (a : A R G)
    (ha : ∀ g : G, delta R g*a - a ∈ annihilator R G n) :
    a ∈ annihilator R G (n+1) := by
  have hres : ∀ b : A R G, (b - augmentation R G b • 1)*a ∈ annihilator R G n := by
    intro b
    induction b using MonoidAlgebra.induction_linear with
    | zero => simp
    | add b c hb hc =>
      have he : (b+c - augmentation R G (b+c) • 1)*a =
          (b - augmentation R G b • 1)*a + (c - augmentation R G c • 1)*a := by
        simp only [map_add, add_smul]
        noncomm_ring
      rw [he]
      exact (annihilator R G n).add_mem hb hc
    | single g r =>
      have he : MonoidAlgebra.single g r = r • delta R g := by simp [delta]
      rw [augmentation_single, he, ← smul_sub, smul_mul_assoc]
      simpa [sub_mul] using (annihilator R G n).smul_mem r (ha g)
  intro b hb
  induction hb using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨x,hx,y,hy,rfl⟩ := hv
    rw [mul_assoc]
    have ht : y*a ∈ annihilator R G n := by simpa [hy] using hres y
    exact ht x hx
  | zero => simp
  | add b c _ _ hb hc => simp [add_mul, hb, hc]
  | smul r b _ hb => simp [hb]

variable (p : ℕ) [Fact p.Prime] [Finite G]

/-- If an annihilator layer is still proper, finite p-group orbit counting
forces the next actual annihilator layer to be strictly larger. -/
theorem annihilator_lt_succ (hG : IsPGroup p G) (n : ℕ)
    (hn : annihilator (ZMod p) G n ≠ ⊤) :
    annihilator (ZMod p) G n < annihilator (ZMod p) G (n+1) := by
  letI : Module.Finite (ZMod p) (A (ZMod p) G) :=
    Module.Finite.of_basis (MonoidAlgebra.basis G (ZMod p))
  letI : Nontrivial (A (ZMod p) G ⧸ annihilator (ZMod p) G n) :=
    Submodule.Quotient.nontrivial_iff.mpr hn
  obtain ⟨x,hx,hfixed⟩ := exists_nonzero_fixed_vector p G
    (A (ZMod p) G ⧸ annihilator (ZMod p) G n) hG (annihilatorQuotient (ZMod p) G n)
  obtain ⟨a,rfl⟩ := (annihilator (ZMod p) G n).mkQ_surjective x
  have hnext : a ∈ annihilator (ZMod p) G (n+1) := by
    apply mem_annihilator_succ_of_fixed
    intro g
    have ht := hfixed g
    rw [annihilatorQuotient_mk] at ht
    exact (Submodule.Quotient.eq _).mp ht
  refine lt_of_le_of_ne (annihilator_mono (ZMod p) G (Nat.le_succ n)) ?_
  intro heq
  apply hx
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact heq.symm ▸ hnext

/-- The increasing annihilator filtration fills the regular module in at
most its dimension. This step uses actual strict dimension growth. -/
theorem annihilator_finrank_eq_top (hG : IsPGroup p G) :
    annihilator (ZMod p) G (Module.finrank (ZMod p) (A (ZMod p) G)) = ⊤ := by
  letI : Module.Finite (ZMod p) (A (ZMod p) G) :=
    Module.Finite.of_basis (MonoidAlgebra.basis G (ZMod p))
  let N := Module.finrank (ZMod p) (A (ZMod p) G)
  by_contra hN
  have hproper : ∀ n ≤ N, annihilator (ZMod p) G n ≠ ⊤ := by
    intro n hn heq
    apply hN
    exact top_le_iff.mp (heq ▸ annihilator_mono (ZMod p) G hn)
  have hlower : ∀ n ≤ N, n ≤ Module.finrank (ZMod p) (annihilator (ZMod p) G n) := by
    intro n
    induction n with
    | zero => intro _; exact Nat.zero_le _
    | succ n ih =>
      intro hn
      have hprev := ih (by omega)
      have hlt := Submodule.finrank_lt_finrank_of_lt
        (annihilator_lt_succ G p hG n (hproper n (by omega)))
      omega
  have hlo := hlower N (le_refl N)
  have hhi := Submodule.finrank_lt hN
  dsimp [N] at hlo
  omega

/-- The actual augmentation ideal of a finite p-group over `𝔽_p` is
nilpotent. An explicit general bound is the order of the group. -/
theorem power_card_eq_bot (hG : IsPGroup p G) :
    power (ZMod p) G (Nat.card G) = ⊥ := by
  letI : Fintype G := Fintype.ofFinite G
  have hdim : Module.finrank (ZMod p) (A (ZMod p) G) = Nat.card G := by
    rw [Module.finrank_eq_card_basis (MonoidAlgebra.basis G (ZMod p)),
      Nat.card_eq_fintype_card]
  have hann := annihilator_finrank_eq_top G p hG
  rw [hdim] at hann
  apply le_bot_iff.mp
  intro b hb
  have hOne : (1 : A (ZMod p) G) ∈ annihilator (ZMod p) G (Nat.card G) := by
    rw [hann]
    trivial
  have hz := hOne b hb
  simpa using hz

/-- Every later actual augmentation power vanishes as well. -/
theorem power_eq_bot_of_card_le (hG : IsPGroup p G) (n : ℕ) (hn : Nat.card G ≤ n) :
    power (ZMod p) G n = ⊥ := by
  apply le_bot_iff.mp
  rw [← power_card_eq_bot G p hG]
  exact power_antitone (ZMod p) G hn

/-- The actual dimension-subgroup filtration of a finite p-group terminates.
This supplies the finite filtration required before choosing homogeneous
ambient directions. -/
theorem dimensionSubgroup_eq_bot_of_card_le (hG : IsPGroup p G) (n : ℕ)
    (hn : Nat.card G ≤ n) : dimensionSubgroup (ZMod p) G n = ⊥ := by
  ext g
  change delta (ZMod p) g - 1 ∈ power (ZMod p) G n ↔ g = 1
  rw [power_eq_bot_of_card_le G p hG n hn, Submodule.mem_bot, sub_eq_zero]
  constructor
  · intro hg
    exact MonoidAlgebra.single_left_injective (one_ne_zero : (1 : ZMod p) ≠ 0) hg
  · rintro rfl
    rfl

end UnitDistance.GroupAugmentation
