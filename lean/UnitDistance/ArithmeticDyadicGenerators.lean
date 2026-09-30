module

public import UnitDistance.ArithmeticDyadicGenus
public import Mathlib.GroupTheory.Frattini
public import UnitDistance.PadicTwoQuadraticClosure
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.ProP.FinitePGroupMaximal

@[expose] public section
set_option backward.privateInPublic true


/-! The actual three local lifts generate the actual dyadic Galois group.
Quadratic-subfield exhaustion proves the Frattini kernel inclusion. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.ArithmeticDyadic
open ArithmeticRetained Multiquadratic
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

abbrev G := Gal(LocalField/ℚ_[2])
theorem isTwoGroup : IsPGroup 2 G :=
  RationalGaloisBaseChange.isPGroup RetainedField ℚ_[2] retained_isPGroup

def genusLocal : IntermediateField ℚ_[2] LocalField :=
  IntermediateField.adjoin ℚ_[2] (Set.range (fun i : Fin 3 => genusRoot (independentIndex i)))

def genusLocalRoot (i : Fin 3) : genusLocal :=
  ⟨genusRoot (independentIndex i),IntermediateField.subset_adjoin ℚ_[2] _ ⟨i,rfl⟩⟩

theorem genusLocalRoot_sq : (genusLocalRoot 0)^2=-1 ∧
    (genusLocalRoot 1)^2=2 ∧ (genusLocalRoot 2)^2=5 := by
  refine ⟨?_,?_,?_⟩
  · apply Subtype.ext
    change (genusRoot 0)^2=(-1 : LocalField)
    simpa [ArithmeticChosenGenus.radicands] using genusRoot_sq 0
  · apply Subtype.ext
    change (genusRoot 1)^2=(2 : LocalField)
    have h := genusRoot_sq 1
    norm_num [ArithmeticChosenGenus.radicands] at h
    exact h
  · apply Subtype.ext
    change (genusRoot 3)^2=(5 : LocalField)
    have h := genusRoot_sq 3
    norm_num [ArithmeticChosenGenus.radicands,Matrix.cons_val_succ] at h
    exact h

theorem signMap_ker_le_genusFixing : signMap.ker≤genusLocal.fixingSubgroup := by
  intro σ hσ
  apply (IntermediateField.mem_fixingSubgroup_iff genusLocal σ).mpr
  apply (IntermediateField.forall_mem_adjoin_smul_eq_self_iff (F := ℚ_[2]) σ).mpr
  rintro z ⟨i,rfl⟩
  have hv : (model σ).base (independentIndex i)=0 :=
    congrFun (congrArg Multiplicative.toAdd hσ) i
  change σ (genusRoot (independentIndex i))=genusRoot (independentIndex i)
  rw [genusRoot_action,hv,binarySign_zero,one_mul]

/-- Every maximal subgroup contains the kernel of the true three-sign map. -/
theorem signMap_ker_le_frattini : signMap.ker≤frattini G := by
  rw [frattini,Order.radical]
  refine le_iInf fun H => le_iInf fun hH => ?_
  letI : H.Normal := ClassFieldTower.ProP.isCoatom_normal_of_isPGroup isTwoGroup hH
  have hd : Module.finrank ℚ_[2] (IntermediateField.fixedField H)=2 := by
    calc
      Module.finrank ℚ_[2] (IntermediateField.fixedField H)=
          Nat.card Gal(IntermediateField.fixedField H/ℚ_[2]) :=
        (IsGalois.card_aut_eq_finrank _ _).symm
      _ = Nat.card (G ⧸ H) :=
        (Nat.card_congr (IsGalois.normalAutEquivQuotient H).toEquiv).symm
      _ = 2 := ClassFieldTower.ProP.card_quotient_eq_prime_of_isCoatom_isPGroup isTwoGroup hH
  have he : IntermediateField.fixedField H≤genusLocal :=
    PadicTwo.quadratic_le LocalField genusLocal (IntermediateField.fixedField H)
      (genusLocalRoot 0) (genusLocalRoot 1) (genusLocalRoot 2)
      genusLocalRoot_sq.1 genusLocalRoot_sq.2.1 genusLocalRoot_sq.2.2 hd
  have hfix := IntermediateField.fixingSubgroup_le he
  rw [IntermediateField.fixingSubgroup_fixedField] at hfix
  exact signMap_ker_le_genusFixing.trans hfix

/-- A literal word in the three local signs realizes every vector. -/
theorem localSign_generates : ∀ v : Fin 3 → ZMod 2,
    localSign 0 ^ (v 1).val * localSign 1 ^ (v 0+v 2).val *
      localSign 2 ^ (v 2).val=Multiplicative.ofAdd v := by decide +kernel

/-- The chosen actual local lifts generate the whole actual dyadic Galois group. -/
theorem generators : Subgroup.closure (Set.range generator)=⊤ := by
  apply frattini_nongenerating
  apply top_unique
  intro σ hσ
  let H := Subgroup.closure (Set.range generator)
  let v := (signMap σ).toAdd
  let τ := generator 0 ^ (v 1).val * generator 1 ^ (v 0+v 2).val * generator 2 ^ (v 2).val
  have ht : τ∈H := by
    apply H.mul_mem (H.mul_mem _ _) _
    all_goals exact H.pow_mem (Subgroup.subset_closure ⟨_,rfl⟩) _
  have hq : signMap τ=signMap σ := by
    simp only [τ,map_mul,map_pow,generator_sign]
    exact localSign_generates v
  have hk : σ*τ⁻¹∈signMap.ker := by
    change signMap (σ*τ⁻¹)=1
    rw [map_mul,map_inv,hq,mul_inv_cancel]
  have hl : H≤H⊔frattini G := le_sup_left
  have hr : frattini G≤H⊔frattini G := le_sup_right
  have hm : (σ*τ⁻¹)*τ∈H⊔frattini G :=
    Subgroup.mul_mem _ (hr (signMap_ker_le_frattini hk)) (hl ht)
  simpa using hm

end UnitDistance.ArithmeticDyadic
