module

public import UnitDistance.LocalQuadraticModel

@[expose] public section
set_option backward.privateInPublic true


/-! The universal three-generator quadratic two-group, its actual degree-256
quotient, and the cyclic-four character detecting the omitted relation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace UnitDistance.FreeThreeQuadratic
open ClassTwo
abbrev F := ZMod 2
abbrev V := Fin 3 → F
abbrev W := Fin 6 → F

def cocycleMasks : Fin 3 → Fin 3 → ℕ := ![![1,0,0],![8,2,0],![16,32,4]]

def cocycle : V →ₗ[F] V →ₗ[F] W where
  toFun v :=
    { toFun := fun w => ∑i,∑j,(v i*w j) • RetainedQuadratic.binaryVector 6 (cocycleMasks i j)
      map_add' w w' := by simp only [Pi.add_apply,mul_add,add_smul,Finset.sum_add_distrib]
      map_smul' r w := by
        simp only [Pi.smul_apply,smul_eq_mul,Finset.smul_sum,smul_smul]
        simp only [RingHom.id_apply,mul_left_comm] }
  map_add' v v' := by
    apply LinearMap.ext
    intro w
    change (∑i,∑j,((v i+v' i)*w j) • RetainedQuadratic.binaryVector 6 (cocycleMasks i j))=_
    simp only [add_mul,add_smul,Finset.sum_add_distrib]
    rfl
  map_smul' r v := by
    apply LinearMap.ext
    intro w
    change (∑i,∑j,((r*v i)*w j) • RetainedQuadratic.binaryVector 6 (cocycleMasks i j))=
      r • (∑i,∑j,(v i*w j) • RetainedQuadratic.binaryVector 6 (cocycleMasks i j))
    simp only [Finset.smul_sum,smul_smul,mul_assoc]

abbrev Q := GroupModel cocycle

def basis (i : Fin 3) : Q := ⟨Pi.single i 1,0⟩

def columns : Fin 6 → ℕ := ![16,4,8,17,18,16]

def centralMap : W →ₗ[F] LocalQuadraticModel.W where
  toFun w := ∑i,w i • RetainedQuadratic.binaryVector 5 (columns i)
  map_add' v w := by simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' r w := by simp only [Pi.smul_apply,smul_eq_mul,Finset.smul_sum,smul_smul,RingHom.id_apply]

theorem centralMap_cocycle : ∀u v : V,centralMap (cocycle u v)=LocalQuadraticModel.cocycle u v := by
  decide +kernel

/-- The actual quadratic quotient with precisely the local relation omitted. -/
def quotient : Q →* LocalQuadraticModel.Q where
  toFun q := ⟨q.base,centralMap q.central⟩
  map_one' := by ext <;> simp
  map_mul' q r := by
    ext
    · rfl
    · simp only [GroupModel.mul_central,map_add,centralMap_cocycle]

@[simp] theorem quotient_basis (i : Fin 3) : quotient (basis i)=LocalQuadraticModel.basis i := by
  ext <;> simp [basis,quotient,LocalQuadraticModel.basis]

/-- The central vector representing a²+[b,c]. -/
def relation : Q := ⟨0,Pi.single 0 1+Pi.single 5 1⟩

set_option maxRecDepth 100000 in
theorem centralMap_kernel : ∀w : W,(∀i,centralMap w i=0) ↔
    (∀i,w i=0) ∨ (∀i,w i=(relation.central i)) := by
  decide +kernel

theorem quotient_relation : quotient relation=1 := by
  apply GroupModel.ext
  · rfl
  · funext i
    have h : ∀i,centralMap relation.central i=0 := by decide +kernel
    exact h i

theorem quotient_eq_one_iff (q : Q) : quotient q=1 ↔ q=1 ∨ q=relation := by
  constructor
  · intro h
    have hb : q.base=0 := congrArg GroupModel.base h
    have hc : ∀i,centralMap q.central i=0 := fun i ↦ congrArg (fun r => r.central i) h
    rcases (centralMap_kernel q.central).mp hc with hz | hz
    · left
      exact GroupModel.ext hb (funext hz)
    · right
      exact GroupModel.ext hb (funext hz)
  · rintro (rfl | rfl)
    · exact map_one quotient
    · exact quotient_relation

theorem relation_ne_one : relation≠1 := by decide +kernel

theorem relation_as_word : relation=basis 0^2*(basis 1)⁻¹*(basis 2)⁻¹*basis 1*basis 2 := by
  apply GroupModel.ext
  · funext i
    have h : ∀i : Fin 3,relation.base i=
        (basis 0^2*(basis 1)⁻¹*(basis 2)⁻¹*basis 1*basis 2).base i := by decide +kernel
    exact h i
  · funext i
    have h : ∀i : Fin 6,relation.central i=
        (basis 0^2*(basis 1)⁻¹*(basis 2)⁻¹*basis 1*basis 2).central i := by decide +kernel
    exact h i

abbrev C4 := Multiplicative (ZMod 4)
instance c4Topology : TopologicalSpace C4 := ⊥
instance c4Discrete : DiscreteTopology C4 := ⟨rfl⟩
instance c4TopologicalGroup : IsTopologicalGroup C4 := inferInstance
instance c4T2 : T2Space C4 := inferInstance

def quarticValue (q : Q) : ZMod 4 := (q.base 0).val+2*(q.central 0).val

theorem cocycle_zero (u v : V) : cocycle u v 0=u 0*v 0 := by
  have h : ∀u v : V,cocycle u v 0=u 0*v 0 := by decide +kernel
  exact h u v

/-- The a-coordinate lifts its binary sign to a genuine cyclic-four character. -/
def quartic : Q →* C4 where
  toFun q := Multiplicative.ofAdd (quarticValue q)
  map_one' := by decide +kernel
  map_mul' q r := by
    apply Multiplicative.toAdd.injective
    change quarticValue (q*r)=quarticValue q+quarticValue r
    have h : ∀a b c d : F,
        (((a+b).val : ZMod 4)+2*(c+d+a*b).val)=
          (a.val+2*c.val)+(b.val+2*d.val) := by decide +kernel
    simpa only [quarticValue,GroupModel.mul_base,GroupModel.mul_central,Pi.add_apply,cocycle_zero] using
      h (q.base 0) (r.base 0) (q.central 0) (r.central 0)

@[simp] theorem quartic_basis (i : Fin 3) : quartic (basis i)=
    Multiplicative.ofAdd (if i=0 then 1 else 0) := by
  have h : ∀i : Fin 3,quartic (basis i)=Multiplicative.ofAdd (if i=0 then 1 else 0) := by decide +kernel
  exact h i

theorem quartic_relation : quartic relation=Multiplicative.ofAdd (2 : ZMod 4) := by decide +kernel

theorem quartic_surjective : Function.Surjective quartic := by
  intro z
  refine ⟨basis 0^z.toAdd.val,?_⟩
  rw [map_pow,quartic_basis,if_pos rfl]
  apply Multiplicative.toAdd.injective
  change z.toAdd.val • (1 : ZMod 4)=z.toAdd
  simp

end UnitDistance.FreeThreeQuadratic
