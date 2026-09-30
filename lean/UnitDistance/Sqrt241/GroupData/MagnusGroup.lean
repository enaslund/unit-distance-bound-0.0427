module

public import UnitDistance.GroupAugmentationLayers
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Module.Pi
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.Abel
public import Mathlib.SetTheory.Cardinal.NatCard

@[expose] public section
set_option backward.privateInPublic true


/-!
# The degree-three truncated Magnus group on `n` generators

Copy of `TruncatedMagnusGroup`, `TruncatedMagnusAugmentation` and
`TruncatedMagnusQuotient` (seven generators over `ℚ`) with the number of
generators `n` as a parameter. Coordinates are the coefficients of words of
lengths one, two and three; multiplication is truncated noncommutative
multiplication. The fourth augmentation dimension subgroup is trivial, and a
linear annihilator of the cubic brackets of a space of quadratic relations
defines a normal subgroup containing them with arbitrary cubic tails.
-/

noncomputable section
namespace UnitDistance.Sqrt241.Magnus
variable (n : ℕ) (R : Type*) [CommRing R]
abbrev V₁ := Fin n → R
abbrev V₂ := Fin n → Fin n → R
abbrev V₃ := Fin n → Fin n → Fin n → R

@[ext] structure Group where
  first : V₁ n R
  second : V₂ n R
  third : V₃ n R

namespace Group
variable {n R}

def mul (g h : Group n R) : Group n R :=
  ⟨g.first+h.first,
   fun i j => g.second i j+h.second i j+g.first i*h.first j,
   fun i j k => g.third i j k+h.third i j k+
     g.first i*h.second j k+g.second i j*h.first k⟩

def inv (g : Group n R) : Group n R :=
  ⟨-g.first,
   fun i j => -g.second i j+g.first i*g.first j,
   fun i j k => -g.third i j k+g.first i*g.second j k+
     g.second i j*g.first k-g.first i*g.first j*g.first k⟩

instance : _root_.Group (Group n R) where
  one := ⟨0,0,0⟩
  mul := mul
  inv := inv
  mul_assoc g h k := by
    change mul (mul g h) k = mul g (mul h k)
    ext <;> simp [mul] <;> ring
  one_mul g := by
    change mul ⟨0,0,0⟩ g = g
    ext <;> simp [mul]
  mul_one g := by
    change mul g ⟨0,0,0⟩ = g
    ext <;> simp [mul]
  inv_mul_cancel g := by
    change mul (inv g) g = ⟨0,0,0⟩
    ext <;> simp [mul,inv]
    ring

@[simp] theorem one_first : (1 : Group n R).first = 0 := rfl
@[simp] theorem one_second : (1 : Group n R).second = 0 := rfl
@[simp] theorem one_third : (1 : Group n R).third = 0 := rfl
@[simp] theorem mul_first (g h : Group n R) : (g*h).first = g.first+h.first := rfl
@[simp] theorem mul_second (g h : Group n R) (i j : Fin n) :
    (g*h).second i j = g.second i j+h.second i j+g.first i*h.first j := rfl
@[simp] theorem mul_third (g h : Group n R) (i j k : Fin n) :
    (g*h).third i j k = g.third i j k+h.third i j k+
      g.first i*h.second j k+g.second i j*h.first k := rfl
@[simp] theorem inv_first (g : Group n R) : (g⁻¹).first = -g.first := rfl
@[simp] theorem inv_second (g : Group n R) (i j : Fin n) :
    (g⁻¹).second i j = -g.second i j+g.first i*g.first j := rfl
@[simp] theorem inv_third (g : Group n R) (i j k : Fin n) :
    (g⁻¹).third i j k = -g.third i j k+g.first i*g.second j k+
      g.second i j*g.first k-g.first i*g.first j*g.first k := rfl

def equivProd : Group n R ≃ V₁ n R × V₂ n R × V₃ n R where
  toFun g := (g.first,g.second,g.third)
  invFun p := ⟨p.1,p.2.1,p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Finite R] : Finite (Group n R) := Finite.of_equiv _ equivProd.symm

def firstHom : Group n R →* Multiplicative (V₁ n R) where
  toFun g := Multiplicative.ofAdd g.first
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Conjugation of degree-two elements is the literal cubic bracket. -/
theorem conjugate_degreeTwo (g : Group n R) (y : V₂ n R) (z : V₃ n R) :
    g*(⟨0,y,z⟩ : Group n R)*g⁻¹ =
      (⟨0,y,fun i j k => z i j k+g.first i*y j k-y i j*g.first k⟩ : Group n R) := by
  ext <;> simp <;> ring

/-- The quadratic component of a commutator is its alternating tensor. -/
theorem commutator_second (g h : Group n R) (i j : Fin n) :
    (g*h*g⁻¹*h⁻¹).second i j = g.first i*h.first j-h.first i*g.first j := by
  simp
  ring

end Group

/-- The group over `F₂` has order `2^(n + n² + n³)`. -/
theorem card_binaryGroup : Nat.card (Group n (ZMod 2)) = 2^(n+n*n+n*n*n) := by
  rw [Nat.card_congr Group.equivProd,Nat.card_prod,Nat.card_prod]
  simp only [V₁,V₂,V₃,Nat.card_fun,Nat.card_fin,Nat.card_zmod]
  rw [← pow_mul,← pow_mul,← pow_add,← pow_add]
  ring_nf

theorem binaryGroup_isTwoGroup : IsPGroup 2 (Group n (ZMod 2)) :=
  IsPGroup.of_card (card_binaryGroup n)

/-! ### The fourth dimension subgroup is trivial -/

section Augmentation
open _root_.UnitDistance.Sqrt241.Magnus.Group GroupAugmentation
variable {n R}

abbrev RepresentationSpace := R × V₁ n R × V₂ n R × V₃ n R

def rhoLinear (g : Group n R) : Module.End R (RepresentationSpace (n := n) (R := R)) where
  toFun p := (p.1,
    fun i => p.2.1 i+p.1*g.first i,
    fun i j => p.2.2.1 i j+g.first i*p.2.1 j+p.1*g.second i j,
    fun i j k => p.2.2.2 i j k+g.first i*p.2.2.1 j k+
      g.second i j*p.2.1 k+p.1*g.third i j k)
  map_add' p q := by ext <;> simp <;> ring
  map_smul' r p := by ext <;> simp [smul_eq_mul] <;> ring

def rho : Representation R (Group n R) (RepresentationSpace (n := n) (R := R)) where
  toFun := rhoLinear
  map_one' := by ext p <;> simp [rhoLinear]
  map_mul' g h := by ext p <;> simp [rhoLinear] <;> ring

@[simp] theorem rho_apply (g : Group n R) (p : RepresentationSpace (n := n) (R := R)) :
    rho g p = (p.1,
    fun i => p.2.1 i+p.1*g.first i,
    fun i j => p.2.2.1 i j+g.first i*p.2.1 j+p.1*g.second i j,
    fun i j k => p.2.2.2 i j k+g.first i*p.2.2.1 j k+
      g.second i j*p.2.1 k+p.1*g.third i j k) := rfl

def rhoAlgebra : A R (Group n R) →ₐ[R] Module.End R (RepresentationSpace (n := n) (R := R)) :=
  MonoidAlgebra.lift R _ _ rho

@[simp] theorem rhoAlgebra_delta (g : Group n R) : rhoAlgebra (delta R g) = rho g := by
  simp [rhoAlgebra,delta,MonoidAlgebra.lift_single]

theorem rhoAlgebra_scalar (a : A R (Group n R)) (p : RepresentationSpace (n := n) (R := R)) :
    (rhoAlgebra a p).1 = augmentation R (Group n R) a*p.1 := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha,hb,add_mul]
  | single g r =>
    have he : MonoidAlgebra.single g r = r • delta R g := by simp [delta]
    rw [augmentation_single,he,map_smul,rhoAlgebra_delta]
    rfl

theorem rhoAlgebra_first (a : A R (Group n R)) (u : V₁ n R) (v : V₂ n R) (w : V₃ n R) :
    (rhoAlgebra a (0,u,v,w)).2.1 = augmentation R (Group n R) a • u := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha,hb,add_smul]
  | single g r =>
    have he : MonoidAlgebra.single g r = r • delta R g := by simp [delta]
    rw [augmentation_single,he,map_smul,rhoAlgebra_delta]
    simp

theorem rhoAlgebra_second (a : A R (Group n R)) (v : V₂ n R) (w : V₃ n R) :
    (rhoAlgebra a (0,0,v,w)).2.2.1 = augmentation R (Group n R) a • v := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha,hb,add_smul]
  | single g r =>
    have he : MonoidAlgebra.single g r = r • delta R g := by simp [delta]
    rw [augmentation_single,he,map_smul,rhoAlgebra_delta]
    simp

theorem rhoAlgebra_last (a : A R (Group n R)) (w : V₃ n R) :
    rhoAlgebra a (0,0,0,w) = (0,0,0,augmentation R (Group n R) a • w) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp only [map_zero,LinearMap.zero_apply,zero_smul]; rfl
  | add a b ha hb => simp [ha,hb,add_smul]
  | single g r =>
    have he : MonoidAlgebra.single g r = r • delta R g := by simp [delta]
    rw [augmentation_single,he,map_smul,rhoAlgebra_delta]
    ext <;> simp

theorem rhoAlgebra_power_two_tail (a : A R (Group n R)) (ha : a ∈ power R (Group n R) 2)
    (v : V₂ n R) (w : V₃ n R) : rhoAlgebra a (0,0,v,w) = 0 := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨b,hb,c,hc,rfl⟩ := ha
    have hb0 : augmentation R (Group n R) b = 0 := by
      rw [power_one] at hb
      exact LinearMap.mem_ker.mp hb
    have he : rhoAlgebra c (0,0,v,w) = (0,0,0,(rhoAlgebra c (0,0,v,w)).2.2.2) := by
      apply Prod.ext
      · simp [rhoAlgebra_scalar,hc]
      apply Prod.ext
      · simp [rhoAlgebra_first]
      apply Prod.ext
      · simp [rhoAlgebra_second,hc]
      · rfl
    rw [map_mul,Module.End.mul_apply,he,rhoAlgebra_last,hb0]
    simp
  | zero => simp
  | add a b _ _ ha hb => simp [ha,hb]
  | smul r a _ ha => simp [ha]

theorem rhoAlgebra_power_three_tail (a : A R (Group n R)) (ha : a ∈ power R (Group n R) 3)
    (u : V₁ n R) (v : V₂ n R) (w : V₃ n R) : rhoAlgebra a (0,u,v,w) = 0 := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨b,hb,c,hc,rfl⟩ := ha
    have he : rhoAlgebra c (0,u,v,w) =
        (0,0,(rhoAlgebra c (0,u,v,w)).2.2.1,(rhoAlgebra c (0,u,v,w)).2.2.2) := by
      apply Prod.ext
      · simp [rhoAlgebra_scalar,hc]
      apply Prod.ext
      · simp [rhoAlgebra_first,hc]
      · rfl
    rw [map_mul,Module.End.mul_apply,he,rhoAlgebra_power_two_tail b hb]
  | zero => simp
  | add a b _ _ ha hb => simp [ha,hb]
  | smul r a _ ha => simp [ha]

theorem rhoAlgebra_power_four (a : A R (Group n R)) (ha : a ∈ power R (Group n R) 4) :
    rhoAlgebra a = 0 := by
  apply LinearMap.ext
  intro p
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨b,hb,c,hc,rfl⟩ := ha
    have he : rhoAlgebra c p =
        (0,(rhoAlgebra c p).2.1,(rhoAlgebra c p).2.2.1,(rhoAlgebra c p).2.2.2) := by
      apply Prod.ext
      · simp [rhoAlgebra_scalar,hc]
      · rfl
    rw [map_mul,Module.End.mul_apply,he,rhoAlgebra_power_three_tail b hb]
    rfl
  | zero => simp
  | add a b _ _ ha hb => simp [ha,hb]
  | smul r a _ ha => simp [ha]

/-- No nonidentity element has augmentation degree four. -/
theorem dimensionSubgroup_four : dimensionSubgroup R (Group n R) 4 = ⊥ := by
  apply le_bot_iff.mp
  intro g hg
  have he := rhoAlgebra_power_four (delta R g-1) hg
  have hp := congrArg (fun a : Module.End R (RepresentationSpace (n := n) (R := R)) =>
    a (1,0,0,0)) he
  have h1 : g.first = 0 := by
    simpa using congrArg (fun p : RepresentationSpace (n := n) (R := R) => p.2.1) hp
  have h2 : g.second = 0 := by
    simpa using congrArg (fun p : RepresentationSpace (n := n) (R := R) => p.2.2.1) hp
  have h3 : g.third = 0 := by
    simpa using congrArg (fun p : RepresentationSpace (n := n) (R := R) => p.2.2.2) hp
  change g = 1
  exact Group.ext h1 h2 h3

end Augmentation

/-! ### Normal quotients by quadratic relations with cubic tails -/

section Quotient
open _root_.UnitDistance.Sqrt241.Magnus.Group
variable {n R}
variable {W : Type*} [AddCommGroup W] [Module R W]

def bracket (x : V₁ n R) (y : V₂ n R) : V₃ n R :=
  fun i j k => x i*y j k-y i j*x k

variable (S : Submodule R (V₂ n R)) (L : V₃ n R →ₗ[R] W) (T : V₂ n R →ₗ[R] W)

/-- Quadratic relations with arbitrary compatible cubic tails. -/
def relationSubgroup : Subgroup (Group n R) where
  carrier := {g | g.first = 0 ∧ g.second ∈ S ∧ L g.third = T g.second}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    rcases ha with ⟨ha,has,hat⟩
    rcases hb with ⟨hb,hbs,hbt⟩
    have h2 : (a*b).second = a.second+b.second := by ext i j; simp [ha]
    have h3 : (a*b).third = a.third+b.third := by ext i j k; simp [ha,hb]
    exact ⟨by simp [ha,hb],by rw [h2]; exact S.add_mem has hbs,
      by rw [h2,h3,map_add,map_add,hat,hbt]⟩
  inv_mem' := by
    intro a ha
    rcases ha with ⟨ha,has,hat⟩
    have h2 : (a⁻¹).second = -a.second := by ext i j; simp [ha]
    have h3 : (a⁻¹).third = -a.third := by ext i j k; simp [ha]
    exact ⟨by simp [ha],by rw [h2]; exact S.neg_mem has,
      by rw [h2,h3,map_neg,map_neg,hat]⟩

@[simp] theorem mem_relationSubgroup (g : Group n R) :
    g ∈ relationSubgroup S L T ↔ g.first = 0 ∧ g.second ∈ S ∧ L g.third = T g.second := Iff.rfl

theorem relationSubgroup_normal
    (hL : ∀ (x : V₁ n R) (y : V₂ n R), y ∈ S → L (bracket x y) = 0) :
    (relationSubgroup S L T).Normal := by
  constructor
  intro m hm g
  rcases hm with ⟨hm,hms,hmt⟩
  have he : m = (⟨0,m.second,m.third⟩ : Group n R) := by ext <;> simp [hm]
  rw [he,conjugate_degreeTwo]
  have ht : (fun i j k => m.third i j k+g.first i*m.second j k-m.second i j*g.first k) =
      m.third+bracket g.first m.second := by
    ext i j k
    simp only [Pi.add_apply,bracket]
    ring
  change (0 : V₁ n R) = 0 ∧ m.second ∈ S ∧
    L (fun i j k => m.third i j k+g.first i*m.second j k-m.second i j*g.first k) = T m.second
  rw [ht]
  exact ⟨rfl,hms,by rw [map_add,hL _ _ hms,add_zero,hmt]⟩

@[simp] theorem central_mem_relationSubgroup (z : V₃ n R) :
    (⟨0,0,z⟩ : Group n R) ∈ relationSubgroup S L T ↔ L z = 0 := by simp

theorem relation_mem (y : V₂ n R) (z : V₃ n R) (hy : y ∈ S) (hz : L z = T y) :
    (⟨0,y,z⟩ : Group n R) ∈ relationSubgroup S L T := ⟨rfl,hy,hz⟩

end Quotient
end UnitDistance.Sqrt241.Magnus
