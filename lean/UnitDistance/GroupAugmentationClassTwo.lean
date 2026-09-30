module

public import UnitDistance.GroupAugmentationLayers
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.GroupTheory.PGroup

@[expose] public section
set_option backward.privateInPublic true


/-!
# Bilinear class-two groups and their actual augmentation layers

The group law is an independently defined central extension. A faithful
three-step triangular representation detects its actual augmentation
filtration; the third dimension subgroup is trivial, without an assumed
identification with an abstract lower central or restricted Lie series.
-/

noncomputable section
namespace UnitDistance.ClassTwo
open UnitDistance.GroupAugmentation
variable {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

/-- A bilinear central-extension law. -/
@[ext] structure GroupModel (β : V →ₗ[R] V →ₗ[R] W) where
  base : V
  central : W
  deriving DecidableEq

namespace GroupModel
variable (β : V →ₗ[R] V →ₗ[R] W)

/-- The two coordinates are independent; only multiplication uses `β`. -/
def equivProd : GroupModel β ≃ V × W where
  toFun g := (g.base,g.central)
  invFun p := ⟨p.1,p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Finite V] [Finite W] : Finite (GroupModel β) :=
  Finite.of_equiv (V × W) (equivProd β).symm

def mul (g h : GroupModel β) : GroupModel β :=
  ⟨g.base+h.base,g.central+h.central+β g.base h.base⟩

def inv (g : GroupModel β) : GroupModel β :=
  ⟨-g.base,-g.central+β g.base g.base⟩

instance : Group (GroupModel β) where
  mul := mul β
  one := ⟨0,0⟩
  inv := inv β
  mul_assoc g h k := by
    change mul β (mul β g h) k = mul β g (mul β h k)
    ext <;> simp only [mul,map_add,LinearMap.add_apply] <;> abel
  one_mul g := by
    change mul β ⟨0,0⟩ g = g
    ext <;> simp [mul]
  mul_one g := by
    change mul β g ⟨0,0⟩ = g
    ext <;> simp [mul]
  inv_mul_cancel g := by
    change mul β (inv β g) g = ⟨0,0⟩
    ext <;> simp only [mul,inv,map_neg,LinearMap.neg_apply] <;> abel

@[simp] theorem one_base : (1 : GroupModel β).base = 0 := rfl
@[simp] theorem one_central : (1 : GroupModel β).central = 0 := rfl
@[simp] theorem mul_base (g h : GroupModel β) : (g*h).base = g.base+h.base := rfl
@[simp] theorem mul_central (g h : GroupModel β) :
    (g*h).central = g.central+h.central+β g.base h.base := rfl
@[simp] theorem inv_base (g : GroupModel β) : (g⁻¹).base = -g.base := rfl
@[simp] theorem inv_central (g : GroupModel β) :
    (g⁻¹).central = -g.central+β g.base g.base := rfl

def baseHom : GroupModel β →* Multiplicative V where
  toFun g := Multiplicative.ofAdd g.base
  map_one' := rfl
  map_mul' _ _ := rfl

def centralHom : Multiplicative W →* GroupModel β where
  toFun z := ⟨0,z.toAdd⟩
  map_one' := rfl
  map_mul' z z' := by ext <;> simp

@[simp] theorem centralHom_base (z : Multiplicative W) : (centralHom β z).base = 0 := rfl
@[simp] theorem centralHom_central (z : Multiplicative W) :
    (centralHom β z).central = z.toAdd := rfl

theorem centralHom_injective : Function.Injective (centralHom β) := by
  intro z z' h
  exact congrArg GroupModel.central h

theorem central_mul (g : GroupModel β) (z : Multiplicative W) :
    centralHom β z*g = g*centralHom β z := by
  ext <;> simp [add_comm]


/-- Commutation is measured by the antisymmetric part of the actual
bilinear law. -/
theorem commutator_coordinates (g h : GroupModel β) :
    g⁻¹*h⁻¹*g*h = (⟨0,β g.base h.base-β h.base g.base⟩ : GroupModel β) := by
  ext <;> simp only [mul_base,mul_central,inv_base,inv_central,map_add,map_neg,
    LinearMap.add_apply,LinearMap.neg_apply] <;> abel

theorem add_self_of_charTwo [CharP R 2] (v : V) : v+v = 0 := by
  have h2 : (2 : R) = 0 := by simpa using (CharP.cast_eq_zero R 2)
  rw [← two_smul R,h2,zero_smul]

/-- Every square is the displayed central quadratic value. -/
theorem square_coordinates [CharP R 2] (g : GroupModel β) :
    g^2 = (⟨0,β g.base g.base⟩ : GroupModel β) := by
  ext <;> simp [pow_two,add_self_of_charTwo (R := R)]

/-- These independently defined characteristic-two models are 2-groups. -/
theorem isTwoGroup [CharP R 2] : IsPGroup 2 (GroupModel β) := by
  intro g
  refine ⟨2,?_⟩
  change g^(2*2) = 1
  rw [pow_mul,square_coordinates,square_coordinates]
  ext <;> simp

/-- The faithful triangular action on scalar, first, and second coordinates. -/
def rhoLinear (g : GroupModel β) : Module.End R (R × V × W) where
  toFun p := (p.1,p.2.1+p.1 • g.base,p.2.2+β g.base p.2.1+p.1 • g.central)
  map_add' p q := by
    ext <;> simp only [Prod.fst_add,Prod.snd_add,map_add,add_smul] <;> abel
  map_smul' r p := by
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · change r • p.2.1+(r*p.1) • g.base = r • (p.2.1+p.1 • g.base)
        simp [smul_add,smul_smul]
      · change r • p.2.2+β g.base (r • p.2.1)+(r*p.1) • g.central =
          r • (p.2.2+β g.base p.2.1+p.1 • g.central)
        simp [map_smul,smul_add,smul_smul]

/-- This action uses the actual central-extension multiplication. -/
def rho : Representation R (GroupModel β) (R × V × W) where
  toFun := rhoLinear β
  map_one' := by
    ext p <;> simp [rhoLinear]
  map_mul' g h := by
    ext p <;> simp [rhoLinear,map_add,map_smul,smul_add,add_smul] <;> abel

@[simp] theorem rho_apply (g : GroupModel β) (p : R × V × W) :
    rho β g p = (p.1,p.2.1+p.1 • g.base,p.2.2+β g.base p.2.1+p.1 • g.central) := rfl

/-- The ordinary group-algebra extension of the triangular action. -/
def rhoAlgebra : A R (GroupModel β) →ₐ[R] Module.End R (R × V × W) :=
  MonoidAlgebra.lift R _ _ (rho β)

@[simp] theorem rhoAlgebra_delta (g : GroupModel β) :
    rhoAlgebra β (delta R g) = rho β g := by
  simp [rhoAlgebra,delta,MonoidAlgebra.lift_single]


/-- Every algebra element acts on the scalar coordinate by augmentation. -/
theorem rhoAlgebra_scalar (a : A R (GroupModel β)) (p : R × V × W) :
    (rhoAlgebra β a p).1 = augmentation R (GroupModel β) a*p.1 := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha,hb,add_mul]
  | single g r =>
    have he : MonoidAlgebra.single g r = r • delta R g := by simp [delta]
    rw [augmentation_single,he,map_smul,rhoAlgebra_delta]
    rfl

/-- On vectors with zero scalar coordinate, the first coordinate is acted
on only by augmentation. -/
theorem rhoAlgebra_base_of_scalar_zero (a : A R (GroupModel β)) (v : V) (z : W) :
    (rhoAlgebra β a (0,v,z)).2.1 = augmentation R (GroupModel β) a • v := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha,hb,add_smul]
  | single g r =>
    have he : MonoidAlgebra.single g r = r • delta R g := by simp [delta]
    rw [augmentation_single,he,map_smul,rhoAlgebra_delta]
    simp [rho_apply]

/-- The last coordinate alone is the trivial representation. -/
theorem rhoAlgebra_central (a : A R (GroupModel β)) (z : W) :
    rhoAlgebra β a (0,0,z) = (0,0,augmentation R (GroupModel β) a • z) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp only [map_zero,LinearMap.zero_apply,zero_smul]; rfl
  | add a b ha hb => simp [ha,hb,add_smul]
  | single g r =>
    have he : MonoidAlgebra.single g r = r • delta R g := by simp [delta]
    rw [augmentation_single,he,map_smul,rhoAlgebra_delta]
    simp [rho_apply]

/-- The actual second augmentation power kills the final two-step tail. -/
theorem rhoAlgebra_power_two_tail (a : A R (GroupModel β))
    (ha : a ∈ power R (GroupModel β) 2) (v : V) (z : W) :
    rhoAlgebra β a (0,v,z) = 0 := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨b,hb,c,hc,rfl⟩ := ha
    have hb0 : augmentation R (GroupModel β) b = 0 := by
      rw [power_one] at hb
      exact LinearMap.mem_ker.mp hb
    have he : rhoAlgebra β c (0,v,z) = (0,0,(rhoAlgebra β c (0,v,z)).2.2) := by
      ext <;> simp [rhoAlgebra_scalar,rhoAlgebra_base_of_scalar_zero,hc]
    rw [map_mul,Module.End.mul_apply,he,rhoAlgebra_central,hb0]
    simp
  | zero => simp
  | add a b _ _ ha hb => simp [ha,hb]
  | smul r a _ ha => simp [ha]

/-- Every vector is carried into the final coordinate by the actual second
augmentation power. -/
theorem rhoAlgebra_power_two_base (a : A R (GroupModel β))
    (ha : a ∈ power R (GroupModel β) 2) (p : R × V × W) :
    (rhoAlgebra β a p).2.1 = 0 := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨b,hb,c,hc,rfl⟩ := ha
    have hb0 : augmentation R (GroupModel β) b = 0 := by
      rw [power_one] at hb
      exact LinearMap.mem_ker.mp hb
    have he : rhoAlgebra β c p = (0,(rhoAlgebra β c p).2.1,(rhoAlgebra β c p).2.2) := by
      ext <;> simp [rhoAlgebra_scalar,hc]
    rw [map_mul,Module.End.mul_apply,he,rhoAlgebra_base_of_scalar_zero,hb0,zero_smul]
  | zero => simp
  | add a b _ _ ha hb => simp [ha,hb]
  | smul r a _ ha => simp [ha]

/-- The actual third augmentation power acts by zero in the faithful
triangular representation. -/
theorem rhoAlgebra_power_three (a : A R (GroupModel β))
    (ha : a ∈ power R (GroupModel β) 3) : rhoAlgebra β a = 0 := by
  apply LinearMap.ext
  intro p
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨b,hb,c,hc,rfl⟩ := ha
    have he : rhoAlgebra β c p = (0,(rhoAlgebra β c p).2.1,(rhoAlgebra β c p).2.2) := by
      ext <;> simp [rhoAlgebra_scalar,hc]
    rw [map_mul,Module.End.mul_apply,he,rhoAlgebra_power_two_tail β b hb]
    rfl
  | zero => simp
  | add a b _ _ ha hb => simp [ha,hb]
  | smul r a _ ha => simp [ha]

/-- The actual second dimension subgroup lies in the displayed center. -/
theorem base_eq_zero_of_mem_dimension_two (g : GroupModel β)
    (hg : g ∈ dimensionSubgroup R (GroupModel β) 2) : g.base = 0 := by
  have h := rhoAlgebra_power_two_base β (delta R g-1) hg (1,0,0)
  simpa [rho_apply] using h

/-- No nonidentity element of the independently defined group can have
actual augmentation degree three. -/
theorem dimensionSubgroup_three : dimensionSubgroup R (GroupModel β) 3 = ⊥ := by
  apply le_bot_iff.mp
  intro g hg
  have he := rhoAlgebra_power_three β (delta R g-1) hg
  have hp := congrArg (fun a : Module.End R (R × V × W) => a (1,0,0)) he
  have hb : g.base = 0 := by simpa [rho_apply] using congrArg (fun p : R × V × W => p.2.1) hp
  have hz : g.central = 0 := by simpa [rho_apply] using congrArg (fun p : R × V × W => p.2.2) hp
  change g = 1
  ext <;> assumption

end GroupModel
end UnitDistance.ClassTwo
