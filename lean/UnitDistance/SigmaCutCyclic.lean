module

public import UnitDistance.SigmaCutDyadic
public import UnitDistance.SigmaExtraFrobenius
public import UnitDistance.RetainedCyclicLocalModels

@[expose] public section
set_option backward.privateInPublic true


/-! The actual infinity and extra-prime cyclic subgroups survive the global
cut with exact orders and every inherited augmentation layer. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace UnitDistance.ArithmeticProP.SigmaCut
open OddLocal GroupAugmentation

private theorem cyclic_hom_ext {H : Type*} [Group H] (n : ℕ)
    (f g : Cyclic n →* H) (h : f (cyclicGenerator n)=g (cyclicGenerator n)) : f=g := by
  apply MonoidHom.ext
  intro x
  obtain ⟨k,rfl⟩ := cyclic_eq_generator_zpow n x
  rw [map_zpow,map_zpow,h]

def infinityElement (s : Fin 5 → Source) : Quotient s := projection s sigmaFreeConjugation

theorem infinity_square (s : Fin 5 → Source) : infinityElement s^2=1 := by
  have h := (QuotientGroup.eq_one_iff (quadratics 0)).mpr (quadratic_mem_kernel s 0)
  change projection s (sigmaFreeConjugation^2)=1 at h
  change projection s sigmaFreeConjugation^2=1
  simpa only [map_pow] using h

def infinityMap (s : Fin 5 → Source) : Cyclic 2 →* Quotient s :=
  cyclicMap 2 (infinityElement s) (infinity_square s)

def infinityRetainedElement : RetainedQuadratic.Q := sigmaFreeRetainedMap sigmaFreeConjugation

theorem infinityRetained_square : infinityRetainedElement^2=1 := by
  have h := congrArg (retained ExtraPrime.freeFrobenius) (infinity_square ExtraPrime.freeFrobenius)
  change sigmaFreeRetainedMap sigmaFreeConjugation^2=1
  simpa only [map_pow,map_one,infinityElement,retained_projection] using h

theorem infinityRetained_base_ne_zero : infinityRetainedElement.base≠0 := by
  change (sigmaFreeRetainedMap sigmaFreeConjugation).base≠0
  rw [sigmaFreeConjugation_base]
  decide +kernel

def infinityRetained : Cyclic 2 →* RetainedQuadratic.Q :=
  cyclicMap 2 infinityRetainedElement infinityRetained_square

theorem infinityMap_retained (s : Fin 5 → Source) :
    (retained s).toMonoidHom.comp (infinityMap s)=infinityRetained := by
  apply cyclic_hom_ext
  simp [infinityMap,infinityRetained,infinityElement,infinityRetainedElement]

theorem infinityMap_injective (s : Fin 5 → Source) : Function.Injective (infinityMap s) := by
  intro x y h
  apply RetainedCyclic.cyclicTwo_injective infinityRetainedElement infinityRetained_square infinityRetained_base_ne_zero
  change infinityRetained x=infinityRetained y
  rw [←DFunLike.congr_fun (infinityMap_retained s) x,←DFunLike.congr_fun (infinityMap_retained s) y]
  exact congrArg (retained s) h

theorem infinityMap_layers (s : Fin 5 → Source) (n : ℕ) :
    Function.Injective (layerMap (ZMod 2) (Cyclic 2) (infinityMap s) n) := by
  apply (layerMap_injective_iff (ZMod 2) (Cyclic 2) (infinityMap s) n).mpr
  intro x _ hx
  have hm := map_dimensionSubgroup_le (ZMod 2) (Quotient s)
    (retained s).toMonoidHom (n+1) ⟨infinityMap s x,hx,rfl⟩
  change ((retained s).toMonoidHom.comp (infinityMap s)) x∈_ at hm
  rw [infinityMap_retained] at hm
  rw [←RetainedCyclic.cyclicTwo_strict infinityRetainedElement infinityRetained_square infinityRetained_base_ne_zero (n+1)]
  exact hm

def extraElement (s : Fin 5 → Source) (i : Fin 5) : Quotient s := projection s (s i)

theorem extra_fourth (s : Fin 5 → Source) (i : Fin 5) : extraElement s i^4=1 := by
  have h := (QuotientGroup.eq_one_iff (deep s ⟨i.val+5,by omega⟩)).mpr
    (deep_mem_kernel s ⟨i.val+5,by omega⟩)
  have he : deep s ⟨i.val+5,by omega⟩=(s i)^4 := by fin_cases i <;> rfl
  change projection s (deep s ⟨i.val+5,by omega⟩)=1 at h
  rw [he,map_pow] at h
  exact h

def extraMap (s : Fin 5 → Source) (i : Fin 5) : Cyclic 4 →* Quotient s :=
  cyclicMap 4 (extraElement s i) (extra_fourth s i)

theorem extraRetained_fourth (s : Fin 5 → Source) (i : Fin 5) : sigmaFreeRetainedMap (s i)^4=1 := by
  have h := congrArg (retained s) (extra_fourth s i)
  simpa only [map_pow,map_one,extraElement,retained_projection] using h

def extraRetained (s : Fin 5 → Source) (i : Fin 5) : Cyclic 4 →* RetainedQuadratic.Q :=
  cyclicMap 4 (sigmaFreeRetainedMap (s i)) (extraRetained_fourth s i)

theorem extraMap_retained (s : Fin 5 → Source) (i : Fin 5) :
    (retained s).toMonoidHom.comp (extraMap s i)=extraRetained s i := by
  apply cyclic_hom_ext
  simp [extraMap,extraRetained,extraElement]

theorem extraMap_injective (i : Fin 5) : Function.Injective (extraMap ExtraPrime.freeFrobenius i) := by
  intro x y h
  apply RetainedCyclic.cyclicMap_injective 4 (sigmaFreeRetainedMap (ExtraPrime.freeFrobenius i))
    (extraRetained_fourth _ i) (ExtraPrime.retained_order i _ (ExtraPrime.freeFrobenius_base i))
  change extraRetained ExtraPrime.freeFrobenius i x=extraRetained ExtraPrime.freeFrobenius i y
  rw [←DFunLike.congr_fun (extraMap_retained _ i) x,←DFunLike.congr_fun (extraMap_retained _ i) y]
  exact congrArg (retained ExtraPrime.freeFrobenius) h

theorem extraMap_layers (i : Fin 5) (n : ℕ) :
    Function.Injective (layerMap (ZMod 2) (Cyclic 4) (extraMap ExtraPrime.freeFrobenius i) n) := by
  apply (layerMap_injective_iff (ZMod 2) (Cyclic 4) (extraMap ExtraPrime.freeFrobenius i) n).mpr
  intro x _ hx
  have hm := map_dimensionSubgroup_le (ZMod 2) (Quotient ExtraPrime.freeFrobenius)
    (retained ExtraPrime.freeFrobenius).toMonoidHom (n+1) ⟨extraMap ExtraPrime.freeFrobenius i x,hx,rfl⟩
  change ((retained ExtraPrime.freeFrobenius).toMonoidHom.comp (extraMap ExtraPrime.freeFrobenius i)) x∈_ at hm
  rw [extraMap_retained] at hm
  have hb : (sigmaFreeRetainedMap (ExtraPrime.freeFrobenius i)).base≠0 := by
    rw [ExtraPrime.freeFrobenius_base]
    exact ExtraPrime.vector_ne_zero i
  rw [←RetainedCyclic.cyclicFour_strict (sigmaFreeRetainedMap (ExtraPrime.freeFrobenius i))
    (extraRetained_fourth _ i) (ExtraPrime.retained_order i _ (ExtraPrime.freeFrobenius_base i)) hb (n+1)]
  exact hm

end UnitDistance.ArithmeticProP.SigmaCut
