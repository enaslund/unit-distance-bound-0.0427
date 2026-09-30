module

public import UnitDistance.DyadicClosedPresentation
public import UnitDistance.FreeThreeDyadicQuotient
public import UnitDistance.DyadicTopology
public import UnitDistance.PadicTwoQuadraticRelation
public import UnitDistance.ClassTwoCentralCharacters
public import UnitDistance.RelativeRelatorReplacement

@[expose] public section
set_option backward.privateInPublic true


/-! The genuine local arithmetic relation can replace the literal square
relation in the exact dyadic presentation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace UnitDistance.Dyadic.ArithmeticPresentation
open ProCGroups ProCGroups.Presentations ClassTwo
abbrev Source := FiniteFreeProTwo.Carrier 3
abbrev detector := PadicTwoQuadraticRelation.detector

def x : Source := FiniteFreeProTwo.generator 3 1
def y : Source := FiniteFreeProTwo.generator 3 0
def z : Source := FiniteFreeProTwo.generator 3 0*FiniteFreeProTwo.generator 3 2

/-- Actual dyadic quotient of the free local source. -/
def model : Source →ₜ* D where
  toMonoidHom := FreeThreeDyadicQuotient.quotient.comp detector.toMonoidHom
  continuous_toFun := (show Continuous (FreeThreeDyadicQuotient.quotient :
    PadicTwoQuadraticRelation.U.Q → D) from continuous_of_discreteTopology).comp detector.continuous

@[simp] theorem model_generator (i : Fin 3) : model (FiniteFreeProTwo.generator 3 i)=
    ![D.y,D.x,D.y*D.z] i := by
  change FreeThreeDyadicQuotient.quotient (detector (FiniteFreeProTwo.generator 3 i))=_
  rw [PadicTwoQuadraticRelation.detector_generator,FreeThreeDyadicQuotient.quotient_basis]

@[simp] theorem model_x : model x=D.x := model_generator 1
@[simp] theorem model_y : model y=D.y := model_generator 0
@[simp] theorem model_z : model z=D.z := by
  simp only [z,map_mul,model_generator,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Matrix.cons_val_fin_one]
  change D.y*(D.y*D.z)=D.z
  rw [←mul_assoc,←pow_two,D.y_sq,one_mul]

theorem generators : (Subgroup.closure ({x,y,z}:Set Source)).topologicalClosure=⊤ := by
  let H := Subgroup.closure ({x,y,z}:Set Source)
  have hx : x∈H := Subgroup.subset_closure (by simp)
  have hy : y∈H := Subgroup.subset_closure (by simp)
  have hz : z∈H := Subgroup.subset_closure (by simp)
  have hlast : FiniteFreeProTwo.generator 3 2∈H := by
    convert H.mul_mem (H.inv_mem hy) hz using 1
    simp [y,z]
  have hs : Subgroup.closure (Set.range (FiniteFreeProTwo.generator 3))≤H := by
    apply (Subgroup.closure_le _).mpr
    rintro g ⟨i,rfl⟩
    fin_cases i
    · exact hy
    · exact hx
    · exact hlast
  have ht := Subgroup.topologicalClosure_mono hs
  rw [(FiniteFreeProTwo.isFree 3).generates_range] at ht
  exact top_unique ht

theorem model_surjective : Function.Surjective model := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [←D.generators]
  apply (Subgroup.closure_le _).mpr
  intro d hd
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hd
  rcases hd with rfl|rfl|rfl
  · exact ⟨x,model_x⟩
  · exact ⟨y,model_y⟩
  · exact ⟨z,model_z⟩

def relationKernel : ClosedSubgroup Source where
  toSubgroup := model.toMonoidHom.ker
  isClosed' := ProCGroups.ContinuousMonoidHom.isClosed_ker model
instance relationKernel_normal : relationKernel.Normal :=
  inferInstanceAs model.toMonoidHom.ker.Normal

def relations : Fin 7 → Source := Presentation.literalRelations x y z

theorem literal_presentation : closedNormalClosure (Set.range relations)=
    (relationKernel : Subgroup Source) :=
  Presentation.closedNormalClosure_literalRelations x y z generators model.toMonoidHom
    relationKernel.isClosed' model_surjective model_x model_y model_z

theorem detector_base_zero (r : relationKernel) : (detector r).base=0 :=
  FreeThreeDyadicQuotient.base_zero_of_quotient_eq_one (detector r) r.property

/-- The square coefficient of the first original local generator. -/
def squareCharacter : relationKernel →ₜ* Multiplicative (ZMod 2) :=
  ClassTwo.centralCharacter FreeThreeQuadratic.cocycle detector
    (relationKernel : Subgroup Source) detector_base_zero (LinearMap.proj 0)

theorem squareCharacter_invariant (f : Source) (r : relationKernel) :
    squareCharacter (MulAut.conjNormal f r)=squareCharacter r :=
  ClassTwo.centralCharacter_conjNormal _ _ _ _ _ f r

@[simp] theorem squareCharacter_apply (r : relationKernel) :
    (squareCharacter r).toAdd=(detector r).central 0 := rfl

theorem detector_relations (i : Fin 7) :
    detector (relations i)=Presentation.literalRelations
      (FreeThreeQuadratic.basis 1) (FreeThreeQuadratic.basis 0)
      (FreeThreeQuadratic.basis 0*FreeThreeQuadratic.basis 2) i := by
  change detector.toMonoidHom (Presentation.literalRelations x y z i)=_
  rw [Presentation.map_literalRelations]
  simp only [x,y,z,map_mul]
  change Presentation.literalRelations (detector (FiniteFreeProTwo.generator 3 1))
    (detector (FiniteFreeProTwo.generator 3 0))
    (detector (FiniteFreeProTwo.generator 3 0)*detector (FiniteFreeProTwo.generator 3 2)) i=_
  simp only [PadicTwoQuadraticRelation.detector_generator]

theorem relations_square_coordinate (i : Fin 7) :
    (detector (relations i)).central 0=if i=1 then 1 else 0 := by
  rw [detector_relations]
  have h : ∀i : Fin 7,(Presentation.literalRelations
      (FreeThreeQuadratic.basis 1) (FreeThreeQuadratic.basis 0)
      (FreeThreeQuadratic.basis 0*FreeThreeQuadratic.basis 2) i).central 0=
        if i=1 then 1 else 0 := by decide +kernel
  exact h i

/-- The six added dyadic cuts, excluding the old square relation. -/
def cuts : Set Source := {g | ∃i : Fin 7,i≠1 ∧ g=relations i}

theorem relation_mem_kernel (i : Fin 7) : relations i∈relationKernel := by
  change relations i∈(relationKernel : Subgroup Source)
  rw [←literal_presentation]
  exact subset_closedNormalClosure _ ⟨i,rfl⟩

theorem insert_square_cuts : insert (y^2) cuts=Set.range relations := by
  ext g
  constructor
  · rintro (rfl|⟨i,hi,rfl⟩)
    · exact ⟨1,rfl⟩
    · exact ⟨i,rfl⟩
  · rintro ⟨i,rfl⟩
    by_cases hi : i=1
    · subst i
      exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ ⟨i,hi,rfl⟩

/-- Replacing y² by any genuine local relation with the proved quadratic
initial leaves exactly the same closed kernel, hence the same D32 quotient. -/
theorem arithmetic_presentation (r : Source)
    (hr : detector r=FreeThreeQuadratic.relation) :
    closedNormalClosure (insert r cuts)=(relationKernel : Subgroup Source) := by
  have hrmem : r∈relationKernel := by
    change FreeThreeDyadicQuotient.quotient (detector r)=1
    rw [hr,FreeThreeDyadicQuotient.quotient_relation]
  let s : relationKernel := ⟨y^2,relation_mem_kernel 1⟩
  apply RelativeRelatorReplacement.closedNormalClosure_replace
    (FiniteFreeProTwo.isFree 3).hasOpenNormalBasisInClass relationKernel s ⟨r,hrmem⟩ cuts
    (by simpa only [s,insert_square_cuts] using literal_presentation)
    squareCharacter squareCharacter_invariant
  · intro h
    have hh := congrArg Multiplicative.toAdd h
    change (detector (relations 1)).central 0=0 at hh
    rw [relations_square_coordinate,if_pos rfl] at hh
    exact one_ne_zero hh
  · intro u hu
    obtain ⟨i,hi,hei⟩ := hu
    apply Multiplicative.toAdd.injective
    change (detector u).central 0=0
    rw [hei,relations_square_coordinate,if_neg hi]
  · intro h
    have hh := congrArg Multiplicative.toAdd h
    change (detector r).central 0=0 at hh
    rw [hr] at hh
    have he : FreeThreeQuadratic.relation.central 0=(1 : ZMod 2) := by decide +kernel
    rw [he] at hh
    exact one_ne_zero hh

/-- Any continuous quotient killing the actual relation and the six cuts
factors through the explicit finite dyadic group. -/
theorem factors_through_model
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (φ : Source →ₜ* H) (r : Source) (hr : detector r=FreeThreeQuadratic.relation)
    (hφr : φ r=1) (hcuts : ∀g∈cuts,φ g=1) :
    ∃f : D →ₜ* H,f.comp model=φ := by
  have hk : model.toMonoidHom.ker≤φ.toMonoidHom.ker := by
    change (relationKernel : Subgroup Source)≤_
    rw [←arithmetic_presentation r hr]
    apply closedNormalClosure_le_closed_normal (ProCGroups.ContinuousMonoidHom.isClosed_ker φ)
    intro g hg
    rcases hg with rfl|hg
    · exact hφr
    · exact hcuts g hg
  let e := QuotientGroup.quotientKerEquivOfSurjective model.toMonoidHom model_surjective
  let f : D →ₜ* H :=
    ⟨(QuotientGroup.lift model.toMonoidHom.ker φ.toMonoidHom hk).comp e.symm.toMonoidHom,
      continuous_of_discreteTopology⟩
  refine ⟨f,?_⟩
  apply ContinuousMonoidHom.ext
  intro g
  have he : e (QuotientGroup.mk' model.toMonoidHom.ker g)=model g := rfl
  change QuotientGroup.lift model.toMonoidHom.ker φ.toMonoidHom hk (e.symm (model g))=φ g
  rw [←he,e.symm_apply_apply]
  rfl

/-- The actual image after the six cuts is finite and has order at most32. -/
theorem image_finite_and_card_le
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (φ : Source →ₜ* H) (r : Source) (hr : detector r=FreeThreeQuadratic.relation)
    (hφr : φ r=1) (hcuts : ∀g∈cuts,φ g=1) :
    Finite φ.toMonoidHom.range ∧ Nat.card φ.toMonoidHom.range≤32 := by
  obtain ⟨f,hf⟩ := factors_through_model φ r hr hφr hcuts
  have hfac (g : Source) : f (model g)=φ g :=
    congrArg (fun ψ : Source →ₜ* H => ψ g) hf
  let f' : D → φ.toMonoidHom.range := fun d => ⟨f d,by
    obtain ⟨g,rfl⟩ := model_surjective d
    exact ⟨g,(hfac g).symm⟩⟩
  have hsurj : Function.Surjective f' := by
    rintro ⟨h,g,hg⟩
    refine ⟨model g,?_⟩
    apply Subtype.ext
    exact (hfac g).trans hg
  refine ⟨Finite.of_surjective f' hsurj,?_⟩
  simpa only [Nat.card_eq_fintype_card,D.card] using Nat.card_le_card_of_surjective f' hsurj

end UnitDistance.Dyadic.ArithmeticPresentation
