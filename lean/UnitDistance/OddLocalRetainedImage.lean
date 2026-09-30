module

public import UnitDistance.RetainedOddLocalModels
public import Mathlib.GroupTheory.OrderOfElement

@[expose] public section
set_option backward.privateInPublic true


/-! Exact odd local groups and layer injections in every ambient group
with the displayed relations and the actual retained quadratic diagram. -/
noncomputable section
namespace UnitDistance.OddLocal
open GroupAugmentation RetainedQuadratic
variable {P : Type*} [Group P] (i : Fin 5) (t f : P)
  (ht : t^2=1) (hf : f^residueDegree i=1) (hc : Commute t f)
  (ρ : P →* Q) (htbase : (ρ t).base=Cut.inertiaVector i)
  (hfbase : (ρ f).base=Cut.frobeniusVector i)
include ht hf hc ρ htbase hfbase

theorem map_retained_diagram :
    ρ.comp (map i t f ht hf hc)=oddMapOfLifts i (ρ t) (ρ f) := by
  apply hom_ext
  · simp only [MonoidHom.coe_comp,Function.comp_apply,map_inertia,
      oddMapOfLifts_inertia i _ _ htbase]
  · simp only [MonoidHom.coe_comp,Function.comp_apply,map_frobenius,
      oddMapOfLifts_frobenius i _ _ hfbase]

theorem map_injective_of_retained : Function.Injective (map i t f ht hf hc) := by
  intro x y h
  apply oddMapOfLifts_injective i (ρ t) (ρ f)
  rw [←DFunLike.congr_fun (map_retained_diagram i t f ht hf hc ρ htbase hfbase) x,
    ←DFunLike.congr_fun (map_retained_diagram i t f ht hf hc ρ htbase hfbase) y]
  exact congrArg ρ h

theorem map_layers_of_retained (n : ℕ) :
    Function.Injective (layerMap (ZMod 2) (D i) (map i t f ht hf hc) n) := by
  apply (layerMap_injective_iff (ZMod 2) (D i) (map i t f ht hf hc) n).mpr
  intro g _ hg
  have hm := map_dimensionSubgroup_le (ZMod 2) P ρ (n+1) ⟨map i t f ht hf hc g,hg,rfl⟩
  change (ρ.comp (map i t f ht hf hc)) g∈_ at hm
  rw [map_retained_diagram i t f ht hf hc ρ htbase hfbase] at hm
  rw [←oddMapOfLifts_comap_dimensionSubgroup i (ρ t) (ρ f) (n+1)]
  exact hm

omit ρ htbase hfbase in
theorem map_range : (map i t f ht hf hc).range=Subgroup.closure ({t,f} : Set P) := by
  have he : (map i t f ht hf hc).range=(⊤ : Subgroup (D i)).map (map i t f ht hf hc) := by
    ext g
    simp
  rw [he,←generators i,MonoidHom.map_closure]
  simp only [Set.image_insert_eq,Set.image_singleton,map_inertia,map_frobenius]

theorem card_decomposition_of_retained : Nat.card (Subgroup.closure ({t,f} : Set P))=2*residueDegree i := by
  classical
  rw [←map_range i t f ht hf hc,Nat.card_eq_fintype_card,
    Fintype.card_coeSort_range (map_injective_of_retained i t f ht hf hc ρ htbase hfbase),
    ←Nat.card_eq_fintype_card,card]

omit ht hf hc ρ htbase hfbase in
theorem inertia_order (i : Fin 5) : orderOf (inertia i)=2 := by
  apply orderOf_eq_prime
  · fin_cases i <;> decide
  · fin_cases i <;> decide

theorem card_inertia_of_retained : Nat.card (Subgroup.zpowers t)=2 := by
  rw [Nat.card_zpowers,←map_inertia i t f ht hf hc,
    orderOf_injective _ (map_injective_of_retained i t f ht hf hc ρ htbase hfbase),inertia_order]

end UnitDistance.OddLocal
