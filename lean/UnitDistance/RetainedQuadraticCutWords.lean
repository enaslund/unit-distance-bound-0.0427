module

public import UnitDistance.ClassTwoTameWords
public import UnitDistance.TruncatedMagnusPresentationWords
public import UnitDistance.GroupAugmentationRetainedQuadratic
public import Mathlib.Algebra.Module.Pi

@[expose] public section
set_option backward.privateInPublic true


/-! Actual retention of the quadratic model by the full literal cut kernel.
Every displayed relation vanishes for arbitrary lifts with the specified
genus coordinates. The actual number-field quotient can therefore descend
through this kernel once its arithmetic projection is supplied. -/
noncomputable section
namespace UnitDistance.RetainedQuadratic.Cut
open ClassTwo GroupAugmentation
local instance : AddCommGroup F := Ring.toAddCommGroup
local instance : Module F F := Semiring.toModule
local instance : AddCommGroup V := Pi.addCommGroup
local instance : AddCommGroup W := Pi.addCommGroup
local instance : Module (ZMod 2) V := Pi.Function.module (Fin 7) (ZMod 2) (ZMod 2)
local instance : Module (ZMod 2) W := Pi.Function.module (Fin 12) (ZMod 2) (ZMod 2)
attribute [local irreducible] cocycle
open TruncatedMagnus.Certificate (presentationWords dyadicWord map_presentationWords map_dyadicWord)
abbrev vector := TruncatedMagnus.Certificate.vector
abbrev inertiaVector := TruncatedMagnus.Certificate.inertiaVector
abbrev frobeniusVector := TruncatedMagnus.Certificate.frobeniusVector
abbrev oddPrimes := TruncatedMagnus.Certificate.oddPrimes

def squareForm (v : V) : W := cocycle v v
def bracketForm (v w : V) : W := cocycle v w-cocycle w v
def oddForm (i : Fin 5) : W := bracketForm (inertiaVector i) (frobeniusVector i)+
  (if oddPrimes i%4=3 then 1 else 0 : F) • squareForm (inertiaVector i)

def forms : Fin 16 → W :=
  ![squareForm (vector 1),oddForm 0,oddForm 1,oddForm 2,oddForm 3,oddForm 4,
    squareForm (vector 4),squareForm (vector 8),squareForm (vector 16),
    squareForm (vector 32),squareForm (vector 64),squareForm (vector 2),
    bracketForm (vector 2) (vector 53),bracketForm (vector 2) (vector 89),
    squareForm (vector 43),squareForm (vector 86)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem forms_zero_certificate : ∀ (i : Fin 16) (j : Fin 12),forms i j=0 := by decide +kernel

theorem forms_zero (i : Fin 16) : forms i=0 := funext (forms_zero_certificate i)

theorem odd_word_coordinates (i : Fin 5) (t f : Q)
    (ht : t.base=inertiaVector i) (hf : f.base=frobeniusVector i) :
    ClassTwo.Tame.word cocycle (oddPrimes i) t f=(⟨0,oddForm i⟩ : Q) := by
  have hp : oddPrimes i%4=1 ∨ oddPrimes i%4=3 := by
    have h : ∀ i : Fin 5, oddPrimes i%4=1 ∨ oddPrimes i%4=3 := by decide +kernel
    exact h i
  have hfour : t^4=1 := by
    change t^(2*2)=1
    rw [pow_mul, GroupModel.square_coordinates, GroupModel.square_coordinates]
    apply GroupModel.ext <;> simp
  have hmod : ClassTwo.Tame.word cocycle (oddPrimes i) t f =
      ClassTwo.Tame.word cocycle (oddPrimes i%4) t f := by
    unfold ClassTwo.Tame.word
    rw [pow_eq_pow_mod (oddPrimes i) hfour]
  have hneg (w : W) : -w=w := by
    apply neg_eq_iff_add_eq_zero.mpr
    exact GroupModel.add_self_of_charTwo (R := ZMod 2) w
  have hone : ClassTwo.Tame.word cocycle 1 t f =
      (⟨0,cocycle t.base f.base-cocycle f.base t.base⟩ : Q) := by
    have he := GroupModel.commutator_coordinates cocycle f⁻¹ t⁻¹
    simp only [inv_inv] at he
    change f*t*f⁻¹*(t^1)⁻¹=_
    rw [pow_one,he]
    apply GroupModel.ext
    · rfl
    · simp only [GroupModel.inv_base,map_neg,LinearMap.neg_apply,neg_neg,
        sub_eq_add_neg,hneg]
      abel
  have ht3 : t^3=t⁻¹ := eq_inv_iff_mul_eq_one.mpr (by
    rw [← pow_succ]
    exact hfour)
  have hthree : ClassTwo.Tame.word cocycle 3 t f =
      (⟨0,cocycle t.base f.base-cocycle f.base t.base+
        cocycle t.base t.base⟩ : Q) := by
    change f*t*f⁻¹*(t^3)⁻¹=_
    rw [ht3,inv_inv]
    calc
      f*t*f⁻¹*t = ClassTwo.Tame.word cocycle 1 t f*t^2 := by
        simp only [ClassTwo.Tame.word,pow_one,pow_two,mul_assoc,
          inv_mul_cancel_left]
      _ = (⟨0,cocycle t.base f.base-cocycle f.base t.base⟩ : Q) *
          ⟨0,cocycle t.base t.base⟩ := by
        rw [hone,GroupModel.square_coordinates]
      _ = _ := by ext <;> simp
  rw [hmod]
  rcases hp with hp | hp
  · rw [hp,hone,ht,hf]
    simp [oddForm,bracketForm,squareForm,hp]
  · rw [hp,hthree,ht,hf]
    simp [oddForm,bracketForm,squareForm,hp]

theorem presentationWords_coordinates (c : Q) (t f : Fin 5 → Q) (a b d : Q)
    (hc : c.base=vector 1)
    (ht : ∀ i,(t i).base=inertiaVector i) (hf : ∀ i,(f i).base=frobeniusVector i)
    (ha : a.base=vector 2) (hb : b.base=vector 53) (hd : d.base=vector 89)
    (i : Fin 16) : presentationWords c t f a b d i=(⟨0,forms i⟩ : Q) := by
  fin_cases i
  · change c^2=(⟨0,squareForm (vector 1)⟩ : Q)
    rw [GroupModel.square_coordinates,hc]
    rfl
  · change ClassTwo.Tame.word cocycle 3 (t 0) (f 0)=(⟨0,oddForm 0⟩ : Q)
    exact odd_word_coordinates 0 (t 0) (f 0) (ht 0) (hf 0)
  · change ClassTwo.Tame.word cocycle 5 (t 1) (f 1)=(⟨0,oddForm 1⟩ : Q)
    exact odd_word_coordinates 1 (t 1) (f 1) (ht 1) (hf 1)
  · change ClassTwo.Tame.word cocycle 7 (t 2) (f 2)=(⟨0,oddForm 2⟩ : Q)
    exact odd_word_coordinates 2 (t 2) (f 2) (ht 2) (hf 2)
  · change ClassTwo.Tame.word cocycle 11 (t 3) (f 3)=(⟨0,oddForm 3⟩ : Q)
    exact odd_word_coordinates 3 (t 3) (f 3) (ht 3) (hf 3)
  · change ClassTwo.Tame.word cocycle 13 (t 4) (f 4)=(⟨0,oddForm 4⟩ : Q)
    exact odd_word_coordinates 4 (t 4) (f 4) (ht 4) (hf 4)
  · change (t 0)^2=(⟨0,squareForm (inertiaVector 0)⟩ : Q)
    rw [GroupModel.square_coordinates,ht 0]
    rfl
  · change (t 1)^2=(⟨0,squareForm (inertiaVector 1)⟩ : Q)
    rw [GroupModel.square_coordinates,ht 1]
    rfl
  · change (t 2)^2=(⟨0,squareForm (inertiaVector 2)⟩ : Q)
    rw [GroupModel.square_coordinates,ht 2]
    rfl
  · change (t 3)^2=(⟨0,squareForm (inertiaVector 3)⟩ : Q)
    rw [GroupModel.square_coordinates,ht 3]
    rfl
  · change (t 4)^2=(⟨0,squareForm (inertiaVector 4)⟩ : Q)
    rw [GroupModel.square_coordinates,ht 4]
    rfl
  · change a^2=(⟨0,squareForm (vector 2)⟩ : Q)
    rw [GroupModel.square_coordinates,ha]
    rfl
  · change a⁻¹*b⁻¹*a*b=(⟨0,bracketForm (vector 2) (vector 53)⟩ : Q)
    rw [GroupModel.commutator_coordinates,ha,hb]
    rfl
  · change a⁻¹*d⁻¹*a*d=(⟨0,bracketForm (vector 2) (vector 89)⟩ : Q)
    rw [GroupModel.commutator_coordinates,ha,hd]
    rfl
  · change (f 0)^2=(⟨0,squareForm (frobeniusVector 0)⟩ : Q)
    rw [GroupModel.square_coordinates,hf 0]
    rfl
  · change (f 1)^2=(⟨0,squareForm (frobeniusVector 1)⟩ : Q)
    rw [GroupModel.square_coordinates,hf 1]
    rfl

/-- All sixteen literal cut relations vanish in the retained model. -/
theorem presentationWords_eq_one (c : Q) (t f : Fin 5 → Q) (a b d : Q)
    (hc : c.base=vector 1)
    (ht : ∀ i,(t i).base=inertiaVector i) (hf : ∀ i,(f i).base=frobeniusVector i)
    (ha : a.base=vector 2) (hb : b.base=vector 53) (hd : d.base=vector 89)
    (i : Fin 16) : presentationWords c t f a b d i=1 := by
  rw [presentationWords_coordinates _ _ _ _ _ _ hc ht hf ha hb hd,forms_zero]
  rfl

/-- The actual cubic dyadic relation vanishes in every class-two model. -/
theorem dyadicWord_eq_one (b d : Q) : dyadicWord b d=1 := by
  unfold dyadicWord
  rw [GroupModel.commutator_coordinates,GroupModel.commutator_coordinates]
  apply GroupModel.ext <;> simp

open ProCGroups ProCGroups.ProC ProCGroups.Presentations
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [TopologicalSpace Q] [IsTopologicalGroup Q] [T2Space Q]

/-- The actual retained projection kills the entire closed normal cut kernel.
For the constructed arithmetic projection this proves actual retained-field retention. -/
theorem literal_closedNormalClosure_le_ker (ρ : G →ₜ* Q)
    (c : G) (t f : Fin 5 → G) (a b d : G)
    (hc : (ρ c).base=vector 1)
    (ht : ∀ i,(ρ (t i)).base=inertiaVector i)
    (hf : ∀ i,(ρ (f i)).base=frobeniusVector i)
    (ha : (ρ a).base=vector 2) (hb : (ρ b).base=vector 53) (hd : (ρ d).base=vector 89)
    (deep : Set G) (hdeep : ∀ g∈deep,g∈dimensionSubgroup F G 4) :
    closedNormalClosure (Set.range (presentationWords c t f a b d) ∪ {dyadicWord b d} ∪ deep) ≤
      ρ.toMonoidHom.ker := by
  apply closedNormalClosure_le_closed_normal (ProCGroups.ContinuousMonoidHom.isClosed_ker ρ)
  intro g hg
  change ρ g=1
  rcases hg with (⟨i,rfl⟩ | rfl) | hg
  · have hm := map_presentationWords ρ.toMonoidHom c t f a b d i
    change ρ (presentationWords c t f a b d i)=_ at hm
    rw [hm]
    exact presentationWords_eq_one _ _ _ _ _ _ hc ht hf ha hb hd i
  · have hm := map_dyadicWord ρ.toMonoidHom b d
    change ρ (dyadicWord b d)=_ at hm
    rw [hm]
    exact dyadicWord_eq_one _ _
  · have hm := map_dimensionSubgroup_le F G ρ.toMonoidHom 4 ⟨g,hdeep g hg,rfl⟩
    have h3 := dimensionSubgroup_antitone F Q (by decide : 3≤4) hm
    rw [GroupModel.dimensionSubgroup_three,Subgroup.mem_bot] at h3
    exact h3

end UnitDistance.RetainedQuadratic.Cut
