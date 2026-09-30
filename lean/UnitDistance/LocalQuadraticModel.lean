module

public import UnitDistance.GroupAugmentationRetainedQuadratic
public import UnitDistance.ClassTwoCollectionDiagonal

@[expose] public section
set_option backward.privateInPublic true


/-! The explicit local bilinear group maps to every actual group with
central coordinates and three generators with their actual central squares satisfying its displayed
commutation equations. The homomorphism is proved by collecting actual words. -/
noncomputable section
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
namespace UnitDistance.LocalQuadraticModel
open ClassTwo ClassTwo.Collection GroupAugmentation

abbrev F := ZMod 2
abbrev V := Fin 3 → F
abbrev W := Fin 5 → F

def cocycleMasks : Fin 3 → Fin 3 → ℕ := ![![16,0,0],![17,4,0],![18,16,8]]

def cocycle : V →ₗ[F] V →ₗ[F] W where
  toFun v :=
    { toFun := fun w => ∑ i, ∑ j, (v i*w j) • RetainedQuadratic.binaryVector 5 (cocycleMasks i j)
      map_add' w w' := by
        simp only [Pi.add_apply,mul_add,add_smul,Finset.sum_add_distrib]
      map_smul' r w := by
        simp only [Pi.smul_apply,smul_eq_mul,Finset.smul_sum,smul_smul]
        simp only [RingHom.id_apply,mul_left_comm] }
  map_add' v v' := by
    apply LinearMap.ext
    intro w
    change (∑ i, ∑ j, ((v i+v' i)*w j) • RetainedQuadratic.binaryVector 5 (cocycleMasks i j)) = _
    simp only [add_mul,add_smul,Finset.sum_add_distrib]
    rfl
  map_smul' r v := by
    apply LinearMap.ext
    intro w
    change (∑ i, ∑ j, ((r*v i)*w j) • RetainedQuadratic.binaryVector 5 (cocycleMasks i j)) =
      r • (∑ i, ∑ j, (v i*w j) • RetainedQuadratic.binaryVector 5 (cocycleMasks i j))
    simp only [Finset.smul_sum,smul_smul,mul_assoc]

abbrev Q := GroupModel cocycle

def basis (i : Fin 3) : Q := ⟨Pi.single i 1,0⟩
def indices : List (Fin 3) := [0,1,2]
def before : Fin 3 → List (Fin 3) :=
  ![[],[0],[0,1]]
def after : Fin 3 → List (Fin 3) :=
  ![[1,2],[2],[]]

def swapCoordinate (i j : Fin 3) : W :=
  cocycle (Pi.single i 1) (Pi.single j 1)+cocycle (Pi.single j 1) (Pi.single i 1)

theorem split_indices (i : Fin 3) : before i++i::after i=indices := by
  have h : ∀ i : Fin 3, before i++i::after i=indices := by decide +kernel
  exact h i

theorem not_mem_before (i : Fin 3) : i∉before i := by
  have h : ∀ i : Fin 3, i∉before i := by decide +kernel
  exact h i

theorem not_mem_after (i : Fin 3) : i∉after i := by
  have h : ∀ i : Fin 3, i∉after i := by decide +kernel
  exact h i

variable {G : Type*} [Group G]

theorem word_single (g : Fin 3 → G) (i : Fin 3) :
    word g indices (Pi.single i 1)=g i := by
  fin_cases i <;> simp [word,indices,bit]

theorem word_zero (g : Fin 3 → G) : word g indices 0=1 := by
  simp [word,indices]

theorem cocycle_single_single (i j : Fin 3) :
    cocycle (Pi.single i 1) (Pi.single j 1)=RetainedQuadratic.binaryVector 5 (cocycleMasks i j) := by
  classical
  simp [cocycle,Pi.single_apply]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
theorem cocycle_basis_upper (i j : Fin 3) (h : i<j) :
    cocycle (Pi.single i 1) (Pi.single j 1)=0 := by
  rw [cocycle_single_single]
  have hh : ∀ (i j : Fin 3) (k : Fin 5), i<j →
      RetainedQuadratic.binaryVector 5 (cocycleMasks i j) k=0 := by decide +kernel
  exact funext (fun k => hh i j k h)

theorem bit_basis (i : Fin 3) (t : F) :
    bit (basis i) t=(⟨t • Pi.single i 1,0⟩ : Q) := by
  rcases binary_cases t with rfl | rfl
  · simp only [bit_zero,zero_smul]
    rfl
  · simp [basis]

/-- The sorted product has no central correction because the cocycle is lower triangular. -/
theorem model_word (v : V) : word basis indices v=(⟨v,0⟩ : Q) := by
  apply GroupModel.ext
  · simp only [word,indices,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
      bit_basis,GroupModel.mul_base,GroupModel.one_base]
    funext i
    fin_cases i <;> simp
  · simp only [word,indices,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,
      bit_basis,GroupModel.mul_base,GroupModel.one_base,GroupModel.mul_central,
      GroupModel.one_central,map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply,
      map_zero,zero_add,add_zero,smul_zero]
    simp [cocycle_basis_upper]

/-- The three basis generators and all central elements generate the model. -/
def generators : Fin 3 ⊕ W → Q
  | .inl i => basis i
  | .inr w => GroupModel.centralHom cocycle (Multiplicative.ofAdd w)

theorem generators_closure : Subgroup.closure (Set.range generators)=⊤ := by
  apply top_unique
  intro q hq
  let H := Subgroup.closure (Set.range generators)
  have hb : ∀ i, basis i∈H := fun i => Subgroup.subset_closure ⟨Sum.inl i,rfl⟩
  have hc : ∀ w, GroupModel.centralHom cocycle (Multiplicative.ofAdd w)∈H :=
    fun w => Subgroup.subset_closure ⟨Sum.inr w,rfl⟩
  have hw : word basis indices q.base∈H := by
    unfold word
    apply H.list_prod_mem
    intro x hx
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    by_cases h : q.base i=0
    · simpa [bit,h] using H.one_mem
    · simpa [bit,h] using hb i
  have he : q=word basis indices q.base*
      GroupModel.centralHom cocycle (Multiplicative.ofAdd q.central) := by
    rw [model_word]
    ext <;> simp
  rw [he]
  exact H.mul_mem hw (hc q.central)

/-- Collection includes the nonzero diagonal generator squares. -/
theorem correction_eq_cocycle (v : V) (i : Fin 3) :
    correction (fun t => swapCoordinate t i) (after i) v+
      v i • cocycle (Pi.single i 1) (Pi.single i 1)=cocycle v (Pi.single i 1) := by
  have h : ∀ (v : V) (i : Fin 3),
    correction (fun t => swapCoordinate t i) (after i) v+
      v i • cocycle (Pi.single i 1) (Pi.single i 1)=cocycle v (Pi.single i 1) := by
    decide +kernel
  exact h v i

attribute [local irreducible] cocycle

variable (z : Multiplicative W →* G) (hz : ∀ w g, Commute (z w) g)
  (g : Fin 3 → G) (hg : ∀ i, g i^2=z (Multiplicative.ofAdd (cocycle (Pi.single i 1) (Pi.single i 1))))
  (hs : ∀ i j, g i*g j=z (Multiplicative.ofAdd (swapCoordinate i j))*g j*g i)

include hz hg hs in
/-- Actual ordered words obey each right Cayley edge of the bilinear law. -/
theorem word_right_basis (v : V) (i : Fin 3) :
    word g indices v*g i=z (Multiplicative.ofAdd (cocycle v (Pi.single i 1)))*
      word g indices (v+Pi.single i 1) := by
  have h := word_toggle_diagonal z hz g i (before i) (after i) v
    (fun j => swapCoordinate j i) (cocycle (Pi.single i 1) (Pi.single i 1)) (hg i) (not_mem_before i) (not_mem_after i)
    (fun j _ => hs j i)
  rw [split_indices,correction_eq_cocycle] at h
  exact h

/-- The prospective homomorphism is a literal collected word in the actual generators. -/
def modelMap (q : Q) : G := z (Multiplicative.ofAdd q.central)*word g indices q.base

theorem modelMap_one : modelMap z g 1=1 := by
  simp [modelMap,word_zero]

theorem modelMap_basis (i : Fin 3) : modelMap z g (basis i)=g i := by
  simp [modelMap,basis,word_single]

theorem modelMap_central (w : W) :
    modelMap z g (GroupModel.centralHom cocycle (Multiplicative.ofAdd w))=
      z (Multiplicative.ofAdd w) := by
  simp [modelMap,word_zero]

include hz hg hs in
/-- The collected map preserves every basis Cayley edge. -/
theorem modelMap_right_basis (q : Q) (i : Fin 3) :
    modelMap z g (q*basis i)=modelMap z g q*modelMap z g (basis i) := by
  rw [modelMap_basis]
  change z (Multiplicative.ofAdd (q.central+0+cocycle q.base (Pi.single i 1)))*
      word g indices (q.base+Pi.single i 1)=
    (z (Multiplicative.ofAdd q.central)*word g indices q.base)*g i
  rw [add_zero,mul_assoc,word_right_basis z hz g hg hs,← mul_assoc,← map_mul]
  rfl

include hz in
/-- The collected map preserves every central Cayley edge. -/
theorem modelMap_right_central (q : Q) (w : W) :
    modelMap z g (q*GroupModel.centralHom cocycle (Multiplicative.ofAdd w))=
      modelMap z g q*modelMap z g (GroupModel.centralHom cocycle (Multiplicative.ofAdd w)) := by
  rw [modelMap_central]
  change z (Multiplicative.ofAdd (q.central+w+cocycle q.base 0))*word g indices (q.base+0)=
    (z (Multiplicative.ofAdd q.central)*word g indices q.base)*z (Multiplicative.ofAdd w)
  rw [map_zero,add_zero,add_zero]
  rw [show Multiplicative.ofAdd (q.central+w)=
    Multiplicative.ofAdd q.central*Multiplicative.ofAdd w from rfl,map_mul]
  rw [mul_assoc,(hz (Multiplicative.ofAdd w) (word g indices q.base)).eq,← mul_assoc]

/-- Universal property of the independently defined local bilinear group. -/
def modelHom : Q →* G :=
  homOfRightGenerators (modelMap z g) (modelMap_one z g) generators generators_closure (by
    intro q i
    cases i with
    | inl i => exact modelMap_right_basis z hz g hg hs q i
    | inr w => exact modelMap_right_central z hz g q w)

end UnitDistance.LocalQuadraticModel
