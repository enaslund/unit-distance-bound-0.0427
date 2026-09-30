module

public import UnitDistance.SigmaCutDyadicDecomposition

@[expose] public section
set_option backward.privateInPublic true


/-! Actual dyadic inertia survives unchanged in every cut quotient retaining M. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.ArithmeticProP.SigmaCut
open ProCGroups.Presentations PadicTwoGlobalMap

variable (s : Fin 5 → Source)
  (hgen : closedNormalClosure (Set.range (fun i ↦ (sigmaOriginalRelator i : Source)))=
    (sigmaRelationKernel : Subgroup Source))

theorem retained_arithmeticProjection_hom :
    (retained s).comp (arithmeticProjection s hgen)=sigmaRetainedModelMap := by
  apply ContinuousMonoidHom.ext
  intro σ
  obtain ⟨r,rfl⟩ := sigmaFreeMap_surjective σ
  change retained s (arithmeticProjection s hgen (sigmaFreeMap r))=sigmaRetainedModelMap (sigmaFreeMap r)
  rw [arithmeticProjection_free]
  exact retained_projection s r

def dyadicInertiaMap : PrimeCompletion.AbsoluteInertia prime →* Quotient s :=
  (dyadicDecompositionMap s hgen).toMonoidHom.comp (PrimeCompletion.AbsoluteInertia prime).subtype

def retainedDyadicInertiaMap : PrimeCompletion.AbsoluteInertia prime →* RetainedQuadratic.Q :=
  (sigmaRetainedModelMap.comp (SigmaUnramified.decompositionMap prime)).toMonoidHom.comp
    (PrimeCompletion.AbsoluteInertia prime).subtype

theorem dyadicInertiaMap_retained : (retained s).toMonoidHom.comp (dyadicInertiaMap s hgen)=
    retainedDyadicInertiaMap := by
  apply MonoidHom.ext
  intro σ
  exact DFunLike.congr_fun (retained_arithmeticProjection_hom s hgen)
    (SigmaUnramified.decompositionMap prime σ.val)

theorem retained_dyadic_eq_one_iff (d : PrimeCompletion.AbsoluteDecomposition prime) :
    retained s (dyadicDecompositionMap s hgen d)=1 ↔ dyadicDecompositionMap s hgen d=1 := by
  constructor
  · intro h
    have hd : dyadicDecompositionMap s hgen d∈(dyadicMap s hgen).toMonoidHom.range := by
      rw [←dyadic_decomposition_range]
      exact ⟨d,rfl⟩
    obtain ⟨x,hx⟩ := hd
    change dyadicMap s hgen x=dyadicDecompositionMap s hgen d at hx
    have he : SigmaDyadic.retainedDyadic x=1 := by
      rw [←DFunLike.congr_fun (dyadicMap_retained s hgen) x]
      change retained s (dyadicMap s hgen x)=1
      rwa [hx]
    have hxone : x=1 := SigmaDyadic.retainedDyadic_injective (he.trans (map_one _).symm)
    rw [←hx,hxone,map_one]
  · intro h
    rw [h,map_one]

variable {H : Type*} [Group H] (q : Quotient s →* H)
  (r : H →* RetainedQuadratic.Q) (hr : r.comp q=(retained s).toMonoidHom)

include r hr in
/-- Keeping the retained field preserves the kernel of actual dyadic inertia. -/
theorem dyadic_finite_inertia_kernel :
    (q.comp (dyadicInertiaMap s hgen)).ker=retainedDyadicInertiaMap.ker := by
  ext σ
  change q (dyadicDecompositionMap s hgen σ.val)=1 ↔ retainedDyadicInertiaMap σ=1
  have hret : retainedDyadicInertiaMap σ=retained s (dyadicDecompositionMap s hgen σ.val) :=
    (DFunLike.congr_fun (dyadicInertiaMap_retained s hgen) σ).symm
  rw [hret,retained_dyadic_eq_one_iff]
  constructor
  · intro h
    apply (retained_dyadic_eq_one_iff s hgen σ.val).mp
    have hc : r (q (dyadicDecompositionMap s hgen σ.val))=retained s (dyadicDecompositionMap s hgen σ.val) :=
      DFunLike.congr_fun hr _
    rw [←hc]
    rw [h,map_one]
  · intro h
    rw [h,map_one]

include r hr in
/-- The actual inertia image has the same cardinality as in M. -/
theorem dyadic_finite_inertia_card_eq_retained :
    Nat.card (q.comp (dyadicInertiaMap s hgen)).range=Nat.card retainedDyadicInertiaMap.range := by
  calc
    Nat.card (q.comp (dyadicInertiaMap s hgen)).range=
        Nat.card (PrimeCompletion.AbsoluteInertia prime ⧸ (q.comp (dyadicInertiaMap s hgen)).ker) :=
      (Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv).symm
    _ = Nat.card (PrimeCompletion.AbsoluteInertia prime ⧸ retainedDyadicInertiaMap.ker) := by
      rw [dyadic_finite_inertia_kernel s hgen q r hr]
    _ = Nat.card retainedDyadicInertiaMap.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv

end UnitDistance.ArithmeticProP.SigmaCut
