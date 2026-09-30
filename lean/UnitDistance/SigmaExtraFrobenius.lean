module

public import UnitDistance.ExtraPrimeGenusWitness
public import UnitDistance.SigmaFreeRetained

@[expose] public section
set_option backward.privateInPublic true


/-! The five actual extra-prime Frobenius elements have the required genus
coordinates, exact retained order four, and generate all finite decomposition images. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace UnitDistance.ExtraPrime
open ArithmeticProP ArithmeticGenusFrattini SigmaUnramified

/-- The five Frobenius elements are actual restrictions of elements of the
fixed absolute decomposition groups. -/
def sigmaFrobenius (i : Fin 5) : Gal(maximalSigmaProTwo/ℚ) := frobenius (prime i)

theorem genus_mem_one_or (x y : VectorGroup) (hy : y∈Subgroup.zpowers x) : y=1 ∨ y=x := by
  classical
  obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp ((isOfFinOrder_of_finite x).mem_zpowers_iff_mem_range_orderOf.mp hy)
  have hlt := Finset.mem_range.mp hn
  have hle := orderOf_le_of_pow_eq_one (by decide : 0<2) (vectorGroup_pow_two x)
  have hn' : n=0 ∨ n=1 := by omega
  rcases hn' with rfl | rfl <;> simp

/-- Arithmetic Frobenius has the exact Euler sign vector, rather than an
assumed abelianization label. -/
theorem sigmaFrobenius_genus (i : Fin 5) :
    sigmaGenusRestriction (sigmaFrobenius i)=Multiplicative.ofAdd (vector i) := by
  obtain ⟨d,hd⟩ := exists_labeled_sigma_decomposition i
  have h := decomposition_image_zpowers (prime i) (outside_support i) sigmaGenusRestriction d
  rw [hd] at h
  rcases genus_mem_one_or _ _ h with h | h
  · exact False.elim (vector_ne_zero i (congrArg Multiplicative.toAdd h))
  · exact h.symm

theorem sigmaFrobenius_retained_base (i : Fin 5) :
    (sigmaRetainedModelMap (sigmaFrobenius i)).base=vector i := by
  rw [sigmaRetainedModelMap_base,sigmaFrobenius_genus]
  rfl

theorem sigmaFrobenius_retained_order (i : Fin 5) :
    orderOf (sigmaRetainedModelMap (sigmaFrobenius i))=4 :=
  retained_order i _ (sigmaFrobenius_retained_base i)

theorem sigmaFrobenius_retained_fourth (i : Fin 5) :
    sigmaRetainedModelMap ((sigmaFrobenius i)^4)=1 := by
  rw [map_pow,←sigmaFrobenius_retained_order i,pow_orderOf_eq_one]

/-- The full actual decomposition image is cyclic in every discrete quotient. -/
theorem sigmaFrobenius_generates (i : Fin 5)
    {H : Type*} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    (q : Gal(maximalSigmaProTwo/ℚ) →ₜ* H) (d : PrimeCompletion.AbsoluteDecomposition (prime i)) :
    q (decompositionMap (prime i) d)∈Subgroup.zpowers (q (sigmaFrobenius i)) :=
  decomposition_image_zpowers (prime i) (outside_support i) q d

/-- The actual decomposition image in the retained quadratic model has four elements. -/
theorem retained_decomposition_card (i : Fin 5) :
    Nat.card ((sigmaRetainedModelMap.comp (decompositionMap (prime i))).toMonoidHom.range)=4 := by
  rw [decomposition_range_eq_zpowers (prime i) (outside_support i),Nat.card_zpowers]
  exact sigmaFrobenius_retained_order i

/-- The corresponding cut words are genuine free-source preimages whose
fourth powers preserve the independently constructed retained field. -/
def freeFrobenius (i : Fin 5) : FiniteFreeProTwo.Carrier 7 :=
  Function.surjInv sigmaFreeMap_surjective (sigmaFrobenius i)

theorem freeFrobenius_image (i : Fin 5) : sigmaFreeMap (freeFrobenius i)=sigmaFrobenius i :=
  Function.surjInv_eq sigmaFreeMap_surjective _

theorem freeFrobenius_base (i : Fin 5) :
    (sigmaFreeRetainedMap (freeFrobenius i)).base=vector i := by
  change (sigmaRetainedModelMap (sigmaFreeMap (freeFrobenius i))).base=_
  rw [freeFrobenius_image,sigmaFrobenius_retained_base]

theorem freeFrobenius_fourth_retained (i : Fin 5) :
    sigmaFreeRetainedMap ((freeFrobenius i)^4)=1 := by
  change sigmaRetainedModelMap (sigmaFreeMap ((freeFrobenius i)^4))=1
  rw [map_pow,freeFrobenius_image,sigmaFrobenius_retained_fourth]

/-- In any quotient retaining M and imposing the fourth-power cut, the
Frobenius still has exact order four. -/
theorem freeFrobenius_order_in_quotient (i : Fin 5)
    {H : Type*} [Group H] (q : FiniteFreeProTwo.Carrier 7 →* H)
    (r : H →* RetainedQuadratic.Q)
    (hr : r.comp q=sigmaFreeRetainedMap.toMonoidHom)
    (h4 : q ((freeFrobenius i)^4)=1) : orderOf (q (freeFrobenius i))=4 := by
  have hret : r (q (freeFrobenius i))=sigmaRetainedModelMap (sigmaFrobenius i) := by
    have h := congrArg (fun f : FiniteFreeProTwo.Carrier 7 →* RetainedQuadratic.Q =>
      f (freeFrobenius i)) hr
    change r (q (freeFrobenius i))=sigmaRetainedModelMap (sigmaFreeMap (freeFrobenius i)) at h
    simpa only [freeFrobenius_image] using h
  have h2 : q (freeFrobenius i)^2≠1 := by
    intro h
    have h' := congrArg r h
    rw [map_pow,map_one,hret] at h'
    have hd := orderOf_dvd_of_pow_eq_one h'
    rw [sigmaFrobenius_retained_order] at hd
    norm_num at hd
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime_pow (p:=2) (n:=1) h2 (by simpa only [map_pow, Nat.reducePow, Nat.reduceAdd] using h4)

end UnitDistance.ExtraPrime
