module

public import UnitDistance.PadicTwoQuadraticModelGenerators

@[expose] public section
set_option backward.privateInPublic true


/-! An actual isomorphism between the independently constructed retained
number field's Galois group and the independently defined bilinear finite
group. It is assembled from actual automorphisms, their proved actions on
actual radicals, and the proved collection law. -/
noncomputable section
namespace UnitDistance.PadicTwoQuadratic
open Multiquadratic ClassTwo.Collection PadicTwoGenus PadicTwoNormCatalog
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The true genus coordinates vanish on every automorphism fixing the genus field. -/
theorem genusVector_eq_zero_of_fixes (σ : G)
    (h : ∀ a : E, σ (algebraMap E QuadraticField a)=
      algebraMap E QuadraticField a) : genusVector σ=0 := by
  have he : σ.restrictNormal E=1 := by
    ext a
    apply (algebraMap E QuadraticField).injective
    simpa only [AlgEquiv.one_apply,AlgEquiv.restrictNormal_commutes] using h a
  change (signEquiv (σ.restrictNormal E)).toAdd=0
  rw [he,map_one]
  rfl

@[simp] theorem genusVector_one : genusVector (1 : G)=0 :=
  genusVector_eq_zero_of_fixes _ (fun _ => rfl)

@[simp] theorem genusVector_centralSignHom (v : Multiplicative LocalQuadraticModel.W) :
    genusVector (centralSignHom v)=0 :=
  genusVector_eq_zero_of_fixes _ (centralSignHom_fixes_genus v)

theorem genusVector_bit_basis (i : Fin 3) (t : ZMod 2) :
    genusVector (bit (basisLift i) t)=t • Pi.single i 1 := by
  rcases binary_cases t with rfl | rfl <;>
    simp [genusVector_basisLift]

theorem genusVector_basis_word (v : LocalQuadraticModel.V) :
    genusVector (word basisLift LocalQuadraticModel.indices v)=v := by
  simp only [word,LocalQuadraticModel.indices,List.map_cons,List.map_nil,
    List.prod_cons,List.prod_nil,genusVector_mul,genusVector_one,genusVector_bit_basis]
  funext i
  fin_cases i <;> simp

/-- The actual homomorphism evaluating model coordinates in the actual Galois group. -/
def quadraticModelHom : LocalQuadraticModel.Q →* G :=
  LocalQuadraticModel.modelHom centralSignHom centralSignHom_central basisLift
    basisLift_square basisLift_swap

theorem genusVector_quadraticModelHom (q : LocalQuadraticModel.Q) :
    genusVector (quadraticModelHom q)=q.base := by
  change genusVector (centralSignHom (Multiplicative.ofAdd q.central)*
    word basisLift LocalQuadraticModel.indices q.base)=q.base
  rw [genusVector_mul,genusVector_centralSignHom,genusVector_basis_word,zero_add]

theorem quadraticModelHom_injective : Function.Injective quadraticModelHom := by
  intro q r h
  have hb : q.base=r.base := by
    simpa only [genusVector_quadraticModelHom] using congrArg genusVector h
  have hc : q.central=r.central := by
    have he : centralSignHom (Multiplicative.ofAdd q.central)=
        centralSignHom (Multiplicative.ofAdd r.central) := by
      apply mul_right_cancel (b := word basisLift LocalQuadraticModel.indices r.base)
      change centralSignHom (Multiplicative.ofAdd q.central)*
          word basisLift LocalQuadraticModel.indices q.base=
        centralSignHom (Multiplicative.ofAdd r.central)*
          word basisLift LocalQuadraticModel.indices r.base at h
      simpa only [hb] using h
    exact congrArg Multiplicative.toAdd (centralSignHom_injective he)
  exact ClassTwo.GroupModel.ext hb hc

theorem quadraticModelHom_bijective : Function.Bijective quadraticModelHom := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨quadraticModelHom_injective,?_⟩
  rw [Nat.card_congr (ClassTwo.GroupModel.equivProd LocalQuadraticModel.cocycle),Nat.card_prod,galoisGroup_card]
  simp [LocalQuadraticModel.V,LocalQuadraticModel.W,Nat.card_fun,Nat.card_fin,Nat.card_zmod]

/-- The independent finite group model is the actual local quadratic Galois group. -/
def quadraticModelEquiv : LocalQuadraticModel.Q ≃* G :=
  MulEquiv.ofBijective quadraticModelHom quadraticModelHom_bijective

theorem quadraticModelEquiv_basis (i : Fin 3) :
    quadraticModelEquiv (LocalQuadraticModel.basis i)=basisLift i :=
  LocalQuadraticModel.modelMap_basis centralSignHom basisLift i

theorem quadraticModelEquiv_central (v : LocalQuadraticModel.W) :
    quadraticModelEquiv (ClassTwo.GroupModel.centralHom LocalQuadraticModel.cocycle
      (Multiplicative.ofAdd v))=centralSignHom (Multiplicative.ofAdd v) :=
  LocalQuadraticModel.modelMap_central centralSignHom basisLift v

/-- The actual local Galois group has trivial third augmentation dimension subgroup. -/
theorem dimensionSubgroup_three :
    GroupAugmentation.dimensionSubgroup (ZMod 2) G 3=⊥ := by
  apply le_bot_iff.mp
  intro g hg
  have hh := GroupAugmentation.map_dimensionSubgroup_le (ZMod 2) G
    quadraticModelEquiv.symm.toMonoidHom 3 ⟨g,hg,rfl⟩
  rw [ClassTwo.GroupModel.dimensionSubgroup_three,Subgroup.mem_bot] at hh
  change g=1
  exact quadraticModelEquiv.symm.injective (hh.trans (map_one _).symm)

end UnitDistance.PadicTwoQuadratic
