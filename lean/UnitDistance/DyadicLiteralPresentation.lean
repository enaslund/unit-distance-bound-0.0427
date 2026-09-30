module

public import UnitDistance.DyadicPresentationIdentities
public import UnitDistance.LocalQuadraticModel

@[expose] public section
set_option backward.privateInPublic true


/-! The literal dyadic presentation has at most thirty-two elements. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace UnitDistance.Dyadic.Presentation
open ClassTwo.Collection
variable {G : Type*} [Group G]

private theorem bit_commute {u v : G} (h : Commute u v) (a b : ZMod 2) :
    Commute (bit u a) (bit v b) := by
  rcases binary_cases a with rfl | rfl <;>
    rcases binary_cases b with rfl | rfl <;> simp only [bit_zero,bit_one]
  · exact Commute.one_left _
  · exact Commute.one_left _
  · exact Commute.one_right _
  · exact h

/-- A binary two-coordinate central map. -/
def twoCentralHom (u v : G) (hu : u^2=1) (hv : v^2=1) (huv : Commute u v) :
    Multiplicative (Fin 2 → ZMod 2) →* G where
  toFun t := bit u (t.toAdd 0)*bit v (t.toAdd 1)
  map_one' := by simp
  map_mul' a b := by
    change bit u (a.toAdd 0+b.toAdd 0)*bit v (a.toAdd 1+b.toAdd 1)=_
    rw [bit_add u hu,bit_add v hv]
    exact (bit_commute huv (b.toAdd 0) (a.toAdd 1)).mul_mul_mul_comm _ _

def centerCoordinates : LocalQuadraticModel.W →ₗ[ZMod 2] (Fin 2 → ZMod 2) where
  toFun v := ![v 1+v 3,v 3]
  map_add' v w := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a v := by ext i; fin_cases i <;> simp <;> ring

def centerHom (y z : G) (hw : (comm y z)^2=1) (hz : z^4=1)
    (hwz : Commute (comm y z) z) : Multiplicative LocalQuadraticModel.W →* G :=
  (twoCentralHom (comm y z) (z^2) hw (by simpa only [←pow_mul] using hz)
    (hwz.pow_right 2)).comp centerCoordinates.toAddMonoidHom.toMultiplicative

@[simp] theorem centerHom_apply (y z : G) (hw : (comm y z)^2=1) (hz : z^4=1)
    (hwz : Commute (comm y z) z) (v : LocalQuadraticModel.W) :
    centerHom y z hw hz hwz (Multiplicative.ofAdd v)=
      bit (comm y z) (v 1+v 3)*bit (z^2) (v 3) := rfl

variable (x y z : G) (hx : x^2=1) (hy : y^2=1) (hz : z^4=1)
  (hxy : Commute x y) (hxz : Commute x z)
  (hw : (comm y z)^2=1) (hwz : Commute (comm y z) z)

def localGenerators : Fin 3 → G := ![y,x,y*z]

include hx hy hz hw hwz in
theorem generator_squares (i : Fin 3) :
    localGenerators x y z i^2=centerHom y z hw hz hwz
      (Multiplicative.ofAdd (LocalQuadraticModel.cocycle (Pi.single i 1) (Pi.single i 1))) := by
  rw [LocalQuadraticModel.cocycle_single_single,centerHom_apply]
  fin_cases i <;>
    norm_num [localGenerators,LocalQuadraticModel.cocycleMasks,RetainedQuadratic.binaryVector,bit]
  · exact hy
  · exact hx
  · exact yz_square y z hy hw hwz

include hy hz hxy hxz hw hwz in
theorem generator_swaps (i j : Fin 3) :
    localGenerators x y z i*localGenerators x y z j=
      centerHom y z hw hz hwz (Multiplicative.ofAdd (LocalQuadraticModel.swapCoordinate i j))*
        localGenerators x y z j*localGenerators x y z i := by
  have hxy' := hxy.eq
  have hxyz := hxy.mul_right hxz
  have hyz := y_yz_swap y z hy hw hwz
  have hyz' : y*z*y=comm y z*(y*(y*z)) := by
    calc
      y*z*y=1*(y*z*y) := by simp
      _ = (comm y z*comm y z)*(y*z*y) := by rw [←pow_two,hw]
      _ = comm y z*(comm y z*(y*z)*y) := by group
      _ = comm y z*(y*(y*z)) := by rw [←hyz]
  have hc0 : ∀i j : Fin 3, LocalQuadraticModel.swapCoordinate i j 1+
      LocalQuadraticModel.swapCoordinate i j 3 =
      if (i=0 ∧ j=2) ∨ (i=2 ∧ j=0) then 1 else 0 := by decide +kernel
  have hc1 : ∀i j : Fin 3, LocalQuadraticModel.swapCoordinate i j 3=0 := by decide +kernel
  rw [centerHom_apply,hc0,hc1,bit_zero,mul_one]
  fin_cases i <;> fin_cases j <;> norm_num [localGenerators,bit,Fin.ext_iff]
  · exact hxy'.symm
  · exact hyz
  · exact hxy'
  · exact hxyz.eq
  · simpa only [mul_assoc] using hyz'
  · exact hxyz.symm.eq

section Topology
variable [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  (hgen : (Subgroup.closure ({x,y,z}:Set G)).topologicalClosure=⊤)

include hy hz hxy hxz hw hwz hgen in
theorem centerHom_central (v : Multiplicative LocalQuadraticModel.W) (g : G) :
    Commute (centerHom y z hw hz hwz v) g := by
  have hcw : ∀g,Commute (comm y z) g := central_of_generator_commutes x y z hgen _
    ⟨w_commute_x x y z hxy hxz,w_commute_y y z hy hw,hwz⟩
  have hcz : ∀g,Commute (z^2) g := central_of_generator_commutes x y z hgen _
    ⟨(hxz.pow_right 2).symm,z_square_commute_y y z hw hwz,(Commute.refl z).pow_left 2⟩
  change Commute (bit (comm y z) (v.toAdd 1+v.toAdd 3)*bit (z^2) (v.toAdd 3)) g
  apply Commute.mul_left
  · rcases binary_cases (v.toAdd 1+v.toAdd 3) with h|h <;> simp only [h,bit_zero,bit_one]
    · exact Commute.one_left _
    · exact hcw g
  · rcases binary_cases (v.toAdd 3) with h|h <;> simp only [h,bit_zero,bit_one]
    · exact Commute.one_left _
    · exact hcz g

/-- A collected map from the actual finite quadratic model. -/
def literalModelHom : LocalQuadraticModel.Q →* G :=
  LocalQuadraticModel.modelHom (centerHom y z hw hz hwz)
    (centerHom_central x y z hy hz hxy hxz hw hwz hgen)
    (localGenerators x y z) (generator_squares x y z hx hy hz hw hwz)
    (generator_swaps x y z hy hz hxy hxz hw hwz)

@[simp] theorem literalModelHom_basis (i : Fin 3) :
    literalModelHom x y z hx hy hz hxy hxz hw hwz hgen (LocalQuadraticModel.basis i)=
      localGenerators x y z i :=
  LocalQuadraticModel.modelMap_basis _ _ i

include hx hy hz hxy hxz hw hwz hgen in
theorem literalModelHom_surjective :
    Function.Surjective (literalModelHom x y z hx hy hz hxy hxz hw hwz hgen) := by
  let f := literalModelHom x y z hx hy hz hxy hxz hw hwz hgen
  have hxmem : x∈f.range := ⟨LocalQuadraticModel.basis 1,literalModelHom_basis _ _ _ _ _ _ _ _ _ _ _ 1⟩
  have hymem : y∈f.range := ⟨LocalQuadraticModel.basis 0,literalModelHom_basis _ _ _ _ _ _ _ _ _ _ _ 0⟩
  have hyzmem : y*z∈f.range := ⟨LocalQuadraticModel.basis 2,literalModelHom_basis _ _ _ _ _ _ _ _ _ _ _ 2⟩
  have hzmem : z∈f.range := by
    convert f.range.mul_mem (f.range.inv_mem hymem) hyzmem using 1
    simp
  have hs : Subgroup.closure ({x,y,z}:Set G)≤f.range := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
    rcases hg with rfl|rfl|rfl
    · exact hxmem
    · exact hymem
    · exact hzmem
  have hclosed : IsClosed (f.range : Set G) := (Set.finite_range f).isClosed
  have ht := Subgroup.topologicalClosure_minimal _ hs hclosed
  rw [hgen] at ht
  exact MonoidHom.range_eq_top.mp (le_antisymm le_top ht)

include hx hy hz hxy hxz hw hwz hgen in
/-- The literal quotient is genuinely finite, independently of its cardinal bound. -/
theorem finite_of_literal_relators : Finite G :=
  Finite.of_surjective (literalModelHom x y z hx hy hz hxy hxz hw hwz hgen)
    (literalModelHom_surjective x y z hx hy hz hxy hxz hw hwz hgen)

include hx hy hz hxy hxz hw hwz hgen in
/-- Only five binary coordinates survive in the collected image. -/
theorem card_le_thirty_two : Nat.card G≤32 := by
  let f := literalModelHom x y z hx hy hz hxy hxz hw hwz hgen
  let normalWord : (Fin 3 → ZMod 2) × (Fin 2 → ZMod 2) → G := fun t =>
    (bit (comm y z) (t.2 0)*bit (z^2) (t.2 1))*
      word (localGenerators x y z) LocalQuadraticModel.indices t.1
  have hsurj : Function.Surjective normalWord := by
    intro g
    obtain ⟨q,hq⟩ := literalModelHom_surjective x y z hx hy hz hxy hxz hw hwz hgen g
    refine ⟨(q.base,centerCoordinates q.central),?_⟩
    exact hq
  have h := Nat.card_le_card_of_surjective normalWord hsurj
  have hc : Nat.card ((Fin 3 → ZMod 2) × (Fin 2 → ZMod 2))=32 := by
    rw [Nat.card_eq_fintype_card]
    decide
  simpa only [hc] using h

end Topology
end UnitDistance.Dyadic.Presentation
