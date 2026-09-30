module

public import UnitDistance.SigmaCutDyadic
public import UnitDistance.RetainedOddLocalModels
public import UnitDistance.ProfiniteGeneratedTameFiniteImage

@[expose] public section
set_option backward.privateInPublic true


/-! Exact odd local subgroups of the actual global cut. Literal cut words
give the upper bound; retention of M gives injectivity and all layers. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.ArithmeticProP.SigmaCut
open ProCGroups

def oddInertia (s : Fin 5 → Source) (i : Fin 5) : Quotient s := projection s (sigmaFreeOddInertia i)
def oddFrobenius (s : Fin 5 → Source) (i : Fin 5) : Quotient s := projection s (sigmaFreeOddFrobenius i)

theorem oddInertia_square (s : Fin 5 → Source) (i : Fin 5) : oddInertia s i^2=1 := by
  have h := (QuotientGroup.eq_one_iff (quadratics ⟨i.val+6,by omega⟩)).mpr
    (quadratic_mem_kernel s ⟨i.val+6,by omega⟩)
  change projection s (quadratics ⟨i.val+6,by omega⟩)=1 at h
  have he : quadratics ⟨i.val+6,by omega⟩=(sigmaFreeOddInertia i)^2 := by fin_cases i <;> rfl
  rw [he,map_pow] at h
  exact h

theorem oddFrobenius_power (s : Fin 5 → Source) (i : Fin 5) :
    oddFrobenius s i^OddLocal.residueDegree i=1 := by
  fin_cases i
  all_goals first
  | exact (show projection s (quadratics 14)=1 from
      (QuotientGroup.eq_one_iff _).mpr (quadratic_mem_kernel s 14))
  | exact (show projection s (quadratics 15)=1 from
      (QuotientGroup.eq_one_iff _).mpr (quadratic_mem_kernel s 15))
  | exact (show projection s (deep s 2)=1 from
      (QuotientGroup.eq_one_iff _).mpr (deep_mem_kernel s 2))
  | exact (show projection s (deep s 3)=1 from
      (QuotientGroup.eq_one_iff _).mpr (deep_mem_kernel s 3))
  | exact (show projection s (deep s 4)=1 from
      (QuotientGroup.eq_one_iff _).mpr (deep_mem_kernel s 4))

theorem odd_commute (s : Fin 5 → Source) (i : Fin 5) :
    Commute (oddInertia s i) (oddFrobenius s i) := by
  have h := (QuotientGroup.eq_one_iff (sigmaOriginalRelator (UniversalQuadratic.oddIndex i) : Source)).mpr
    (original_mem_kernel s (UniversalQuadratic.oddIndex i))
  change projection s (sigmaOriginalRelator (UniversalQuadratic.oddIndex i))=1 at h
  rw [sigmaOriginalRelator_odd,map_mul,map_mul,map_mul,map_inv,map_inv,map_pow] at h
  change oddFrobenius s i*oddInertia s i*(oddFrobenius s i)⁻¹*
    (oddInertia s i^UniversalQuadratic.oddPrimes i)⁻¹=1 at h
  have hm : UniversalQuadratic.oddPrimes i%2=1 := by fin_cases i <;> decide
  rw [pow_eq_pow_mod _ (oddInertia_square s i),hm,pow_one] at h
  exact (mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp h)).symm

def oddMap (s : Fin 5 → Source) (i : Fin 5) : OddLocal.D i →* Quotient s :=
  OddLocal.map i (oddInertia s i) (oddFrobenius s i)
    (oddInertia_square s i) (oddFrobenius_power s i) (odd_commute s i)

@[simp] theorem oddMap_inertia (s : Fin 5 → Source) (i : Fin 5) :
    oddMap s i (OddLocal.inertia i)=oddInertia s i := OddLocal.map_inertia ..
@[simp] theorem oddMap_frobenius (s : Fin 5 → Source) (i : Fin 5) :
    oddMap s i (OddLocal.frobenius i)=oddFrobenius s i := OddLocal.map_frobenius ..

def oddRetained (i : Fin 5) : OddLocal.D i →* RetainedQuadratic.Q :=
  RetainedQuadratic.oddMapOfLifts i (sigmaFreeRetainedMap (sigmaFreeOddInertia i))
    (sigmaFreeRetainedMap (sigmaFreeOddFrobenius i))

theorem oddMap_retained (s : Fin 5 → Source) (i : Fin 5) :
    (retained s).toMonoidHom.comp (oddMap s i)=oddRetained i := by
  apply OddLocal.hom_ext
  · simp only [MonoidHom.coe_comp,Function.comp_apply,oddMap_inertia,oddInertia,retained_projection]
    exact (RetainedQuadratic.oddMapOfLifts_inertia i _ _ (inertia_base i)).symm
  · simp only [MonoidHom.coe_comp,Function.comp_apply,oddMap_frobenius,oddFrobenius,retained_projection]
    exact (RetainedQuadratic.oddMapOfLifts_frobenius i _ _ (frobenius_base i)).symm

theorem oddMap_injective (s : Fin 5 → Source) (i : Fin 5) : Function.Injective (oddMap s i) := by
  intro x y h
  apply RetainedQuadratic.oddMapOfLifts_injective i
    (sigmaFreeRetainedMap (sigmaFreeOddInertia i)) (sigmaFreeRetainedMap (sigmaFreeOddFrobenius i))
  change oddRetained i x=oddRetained i y
  rw [←DFunLike.congr_fun (oddMap_retained s i) x,←DFunLike.congr_fun (oddMap_retained s i) y]
  exact congrArg (retained s) h

theorem oddMap_layers (s : Fin 5 → Source) (i : Fin 5) (n : ℕ) :
    Function.Injective (GroupAugmentation.layerMap (ZMod 2) (OddLocal.D i) (oddMap s i) n) := by
  apply (GroupAugmentation.layerMap_injective_iff (ZMod 2) (OddLocal.D i) (oddMap s i) n).mpr
  intro g _ hg
  have hm := GroupAugmentation.map_dimensionSubgroup_le (ZMod 2) (Quotient s)
    (retained s).toMonoidHom (n+1) ⟨oddMap s i g,hg,rfl⟩
  change ((retained s).toMonoidHom.comp (oddMap s i)) g∈_ at hm
  rw [oddMap_retained] at hm
  have hs := RetainedQuadratic.oddMapOfLifts_comap_dimensionSubgroup i
    (sigmaFreeRetainedMap (sigmaFreeOddInertia i)) (sigmaFreeRetainedMap (sigmaFreeOddFrobenius i)) (n+1)
  rw [←hs]
  exact hm

end UnitDistance.ArithmeticProP.SigmaCut
