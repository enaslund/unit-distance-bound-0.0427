module

public import UnitDistance.TruncatedMagnusGroup
public import UnitDistance.GroupAugmentationLayers
public import Mathlib.RepresentationTheory.Basic

@[expose] public section
set_option backward.privateInPublic true


/-! The actual fourth augmentation dimension subgroup of the truncated
Magnus group is trivial. The proof uses a faithful four-step triangular
representation, with no identification of augmentation and lower central series. -/
noncomputable section
namespace UnitDistance.TruncatedMagnus
open Group GroupAugmentation
variable {R : Type*} [CommRing R]

abbrev RepresentationSpace := R × V₁ R × V₂ R × V₃ R

def rhoLinear (g : Group R) : Module.End R (RepresentationSpace (R := R)) where
  toFun p := (p.1,
    fun i => p.2.1 i+p.1*g.first i,
    fun i j => p.2.2.1 i j+g.first i*p.2.1 j+p.1*g.second i j,
    fun i j k => p.2.2.2 i j k+g.first i*p.2.2.1 j k+
      g.second i j*p.2.1 k+p.1*g.third i j k)
  map_add' p q := by ext <;> simp <;> ring
  map_smul' r p := by ext <;> simp [smul_eq_mul] <;> ring

def rho : Representation R (Group R) (RepresentationSpace (R := R)) where
  toFun := rhoLinear
  map_one' := by ext p <;> simp [rhoLinear]
  map_mul' g h := by ext p <;> simp [rhoLinear] <;> ring

@[simp] theorem rho_apply (g : Group R) (p : RepresentationSpace (R := R)) :
    rho g p=(p.1,
    fun i => p.2.1 i+p.1*g.first i,
    fun i j => p.2.2.1 i j+g.first i*p.2.1 j+p.1*g.second i j,
    fun i j k => p.2.2.2 i j k+g.first i*p.2.2.1 j k+
      g.second i j*p.2.1 k+p.1*g.third i j k) := rfl

def rhoAlgebra : A R (Group R) →ₐ[R] Module.End R (RepresentationSpace (R := R)) :=
  MonoidAlgebra.lift R _ _ rho

@[simp] theorem rhoAlgebra_delta (g : Group R) : rhoAlgebra (delta R g)=rho g := by
  simp [rhoAlgebra,delta,MonoidAlgebra.lift_single]

theorem rhoAlgebra_scalar (a : A R (Group R)) (p : RepresentationSpace (R := R)) :
    (rhoAlgebra a p).1=augmentation R (Group R) a*p.1 := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha,hb,add_mul]
  | single g r =>
    have he : MonoidAlgebra.single g r=r • delta R g := by simp [delta]
    rw [augmentation_single,he,map_smul,rhoAlgebra_delta]
    rfl

theorem rhoAlgebra_first (a : A R (Group R)) (u : V₁ R) (v : V₂ R) (w : V₃ R) :
    (rhoAlgebra a (0,u,v,w)).2.1=augmentation R (Group R) a • u := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha,hb,add_smul]
  | single g r =>
    have he : MonoidAlgebra.single g r=r • delta R g := by simp [delta]
    rw [augmentation_single,he,map_smul,rhoAlgebra_delta]
    simp

theorem rhoAlgebra_second (a : A R (Group R)) (v : V₂ R) (w : V₃ R) :
    (rhoAlgebra a (0,0,v,w)).2.2.1=augmentation R (Group R) a • v := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [ha,hb,add_smul]
  | single g r =>
    have he : MonoidAlgebra.single g r=r • delta R g := by simp [delta]
    rw [augmentation_single,he,map_smul,rhoAlgebra_delta]
    simp

theorem rhoAlgebra_last (a : A R (Group R)) (w : V₃ R) :
    rhoAlgebra a (0,0,0,w)=(0,0,0,augmentation R (Group R) a • w) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp only [map_zero,LinearMap.zero_apply,zero_smul]; rfl
  | add a b ha hb => simp [ha,hb,add_smul]
  | single g r =>
    have he : MonoidAlgebra.single g r=r • delta R g := by simp [delta]
    rw [augmentation_single,he,map_smul,rhoAlgebra_delta]
    ext <;> simp

/-- Two actual augmentation factors kill the final two-step tail. -/
theorem rhoAlgebra_power_two_tail (a : A R (Group R)) (ha : a∈power R (Group R) 2)
    (v : V₂ R) (w : V₃ R) : rhoAlgebra a (0,0,v,w)=0 := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨b,hb,c,hc,rfl⟩ := ha
    have hb0 : augmentation R (Group R) b=0 := by
      rw [power_one] at hb
      exact LinearMap.mem_ker.mp hb
    have he : rhoAlgebra c (0,0,v,w)=(0,0,0,(rhoAlgebra c (0,0,v,w)).2.2.2) := by
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

/-- Three actual augmentation factors kill the final three-step tail. -/
theorem rhoAlgebra_power_three_tail (a : A R (Group R)) (ha : a∈power R (Group R) 3)
    (u : V₁ R) (v : V₂ R) (w : V₃ R) : rhoAlgebra a (0,u,v,w)=0 := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨b,hb,c,hc,rfl⟩ := ha
    have he : rhoAlgebra c (0,u,v,w)=
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

/-- The actual fourth augmentation power annihilates the faithful representation. -/
theorem rhoAlgebra_power_four (a : A R (Group R)) (ha : a∈power R (Group R) 4) :
    rhoAlgebra a=0 := by
  apply LinearMap.ext
  intro p
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨b,hb,c,hc,rfl⟩ := ha
    have he : rhoAlgebra c p=
        (0,(rhoAlgebra c p).2.1,(rhoAlgebra c p).2.2.1,(rhoAlgebra c p).2.2.2) := by
      apply Prod.ext
      · simp [rhoAlgebra_scalar,hc]
      · rfl
    rw [map_mul,Module.End.mul_apply,he,rhoAlgebra_power_three_tail b hb]
    rfl
  | zero => simp
  | add a b _ _ ha hb => simp [ha,hb]
  | smul r a _ ha => simp [ha]

/-- No nonidentity element of the concrete group has augmentation degree four. -/
theorem dimensionSubgroup_four : dimensionSubgroup R (Group R) 4=⊥ := by
  apply le_bot_iff.mp
  intro g hg
  have he := rhoAlgebra_power_four (delta R g-1) hg
  have hp := congrArg (fun a : Module.End R (RepresentationSpace (R := R)) => a (1,0,0,0)) he
  have h1 : g.first=0 := by simpa using congrArg (fun p : RepresentationSpace (R := R) => p.2.1) hp
  have h2 : g.second=0 := by simpa using congrArg (fun p : RepresentationSpace (R := R) => p.2.2.1) hp
  have h3 : g.third=0 := by simpa using congrArg (fun p : RepresentationSpace (R := R) => p.2.2.2) hp
  change g=1
  exact Group.ext h1 h2 h3

end UnitDistance.TruncatedMagnus
