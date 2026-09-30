module

public import UnitDistance.TruncatedMagnusFree

@[expose] public section
set_option backward.privateInPublic true


/-! The conjugacy certificate applies to any actual element with the
infinity genus vector. Its arbitrary quadratic and cubic coordinates give
fixed offsets which cancel between conjugates. -/
noncomputable section
namespace UnitDistance.TruncatedMagnus.Certificate
open Group

def conjugateOf (c : Group F) (u v : U) : Group F :=
  conjugator u v*c*(conjugator u v)⁻¹

theorem conjugateOf_second_detect (c : Group F) (hc : c.first=e 0) (u v : U) :
    secondDetector (conjugateOf c u v).second=secondDetector c.second+u := by
  have h : (conjugateOf c u v).second=c.second+quadraticBracket (baseMap u) (e 0) := by
    rw [conjugateOf,conjugate_second]
    ext i j
    simp [conjugator,hc,quadraticBracket]
    ring
  rw [h,map_add,quadraticBracket_comm,secondDetector_bracket_baseMap]

theorem quadratic_conjugateOf_third_detect (c : Group F) (hc : c.first=e 0) (v : U) :
    thirdDetector (quadraticWord v*c*(quadraticWord v)⁻¹).third=thirdDetector c.third-v := by
  rw [conjugate_of_first_zero _ _ (quadraticWord_first v)]
  change thirdDetector (c.third-bracket c.first (quadraticWord v).second)=_
  rw [map_sub,hc,quadraticWord_second,thirdDetector_bracket_selectedMap]
  rfl

/-- The twelve-bit conjugacy certificate tolerates every higher coefficient of the actual element. -/
theorem conjugateOf_injective (tails : Fin 16 → V₃ F) (c : Group F) (hc : c.first=e 0) :
    Function.Injective (fun p : U × U => quotientMap tails (conjugateOf c p.1 p.2)) := by
  intro p q hpq
  have hu : p.1=q.1 := by
    have h := secondDetector_eq_of_quotient tails (conjugateOf c p.1 p.2) (conjugateOf c q.1 q.2)
      (by simp [conjugateOf, conjugator, hc, add_assoc]; abel) hpq
    have hh : secondDetector c.second+p.1=secondDetector c.second+q.1 := by
      simpa only [conjugateOf_second_detect c hc] using h
    exact add_left_cancel hh
  have hv : p.2=q.2 := by
    have hq : quotientMap tails (quadraticWord p.2*c*(quadraticWord p.2)⁻¹)=
        quotientMap tails (quadraticWord q.2*c*(quadraticWord q.2)⁻¹) := by
      have h := congrArg (fun x : Cut tails =>
        (quotientMap tails (baseWord q.1))⁻¹*x*quotientMap tails (baseWord q.1)) hpq
      simpa [conjugateOf,conjugator,hu,map_mul,map_inv,mul_assoc] using h
    have h := thirdDetector_eq_of_quotient tails
      (quadraticWord p.2*c*(quadraticWord p.2)⁻¹) (quadraticWord q.2*c*(quadraticWord q.2)⁻¹)
      (by simp)
      (by rw [conjugate_of_first_zero _ _ (quadraticWord_first p.2),
        conjugate_of_first_zero _ _ (quadraticWord_first q.2)]) hq
    have hh : thirdDetector c.third-p.2=thirdDetector c.third-q.2 := by
      simpa only [quadratic_conjugateOf_third_detect c hc] using h
    exact sub_right_inj.mp hh
  exact Prod.ext hu hv

/-- Every actual generated subgroup retains the same large conjugacy class of such an element. -/
theorem conjugacy_index_lower_subgroup_of_first
    (tails : Fin 16 → V₃ F) (c : Group F) (hc : c.first=e 0) (H : Subgroup (Cut tails))
    (hcH : quotientMap tails c∈H) (hgen : ∀ i,quotientMap tails (generator i)∈H) :
    4096 ≤ (Subgroup.centralizer ({(⟨quotientMap tails c,hcH⟩ : H)} : Set H)).index := by
  rw [← card_parameters]
  let cH : H := ⟨quotientMap tails c,hcH⟩
  let g : U × U → H := fun p =>
    ⟨quotientMap tails (conjugator p.1 p.2),conjugator_mem_subgroup tails H hgen p.1 p.2⟩
  apply card_le_centralizer_index_of_conjugates_injective cH g
  intro p q hpq
  apply conjugateOf_injective tails c hc
  have h := congrArg (fun x : H => (x : Cut tails)) hpq
  simpa only [g,cH,Subgroup.coe_mul,Subgroup.coe_inv,conjugateOf,map_mul,map_inv] using h

open ProCGroups ProCGroups.ProC ProCGroups.FreeProC
variable {G : Type} [_root_.Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] {x : Fin 7 → G}

/-- The actual finite image has the required conjugacy index for any actual infinity lift. -/
theorem freeCut_image_conjugacy_index_of_first
    (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x)
    (tails : Fin 16 → V₃ F) (c : G) (hc : (freeDetector hfree c).first=e 0) :
    4096 ≤ (Subgroup.centralizer
      ({(⟨freeCut hfree tails c,⟨c,rfl⟩⟩ : (freeCut hfree tails).toMonoidHom.range)} :
        Set (freeCut hfree tails).toMonoidHom.range)).index := by
  let H := (freeCut hfree tails).toMonoidHom.range
  have hgen (i : Fin 7) : quotientMap tails (generator i)∈H :=
    ⟨x i,freeCut_generator hfree tails i⟩
  exact conjugacy_index_lower_subgroup_of_first tails (freeDetector hfree c) hc H
    ⟨c,rfl⟩ hgen

end UnitDistance.TruncatedMagnus.Certificate
