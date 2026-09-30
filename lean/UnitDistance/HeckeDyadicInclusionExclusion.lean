module

public import UnitDistance.OddNormDyadicIdeals
public import UnitDistance.HeckeSignedOddSupport
public import UnitDistance.HeckeParityTheta

@[expose] public section
set_option backward.privateInPublic true


/-! Finite inclusion–exclusion for the actual odd-norm signed theta series. -/
noncomputable section
open NumberField DedekindResidue MeasureTheory
open NumberField.mixedEmbedding NumberField.Units.dirichletUnitTheorem
open scoped BigOperators Classical nonZeroDivisors
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.NumberFieldAnalysis
open UnitDistance.OddNormDyadic
variable (K : Type*) [Field K] [NumberField K]

 theorem mem_idealZLattice_mk0_iff (J : (Ideal (𝓞 K))⁰)
    (x : EuclideanSpace ℝ (index K)) :
    x ∈ idealZLattice K (FractionalIdeal.mk0 K J) ↔
      ∃ a : 𝓞 K, a ∈ (J : Ideal (𝓞 K)) ∧ embeddingCoords K (a:K) = x := by
  rw [mem_idealZLattice]
  constructor
  · rintro ⟨y,hy,he⟩
    rw [FractionalIdeal.coe_mk0, FractionalIdeal.mem_coeIdeal] at hy
    obtain ⟨a,ha,rfl⟩ := hy
    exact ⟨a,ha,he⟩
  · rintro ⟨a,ha,he⟩
    refine ⟨(a:K), ?_, he⟩
    rw [FractionalIdeal.coe_mk0, FractionalIdeal.mem_coeIdeal]
    exact ⟨a,ha,rfl⟩

 theorem embedding_mem_idealZLattice_mk0 (J : (Ideal (𝓞 K))⁰) (a : 𝓞 K) :
    embeddingCoords K (a:K) ∈ idealZLattice K (FractionalIdeal.mk0 K J) ↔
      a ∈ (J : Ideal (𝓞 K)) := by
  rw [mem_idealZLattice_mk0_iff]
  constructor
  · rintro ⟨b,hb,he⟩
    have h : b = a := RingOfIntegers.ext (embeddingCoords_injective K he)
    simpa only [h] using hb
  · exact fun ha => ⟨a,ha,rfl⟩

 theorem indicator_odd_idealZLattice (J : (Ideal (𝓞 K))⁰)
    (hJ : Odd (Ideal.absNorm (J : Ideal (𝓞 K))))
    (f : EuclideanSpace ℝ (index K) → ℂ) (x : EuclideanSpace ℝ (index K)) :
    (if x ∈ idealZLattice K (FractionalIdeal.mk0 K J) then
        (if oddNormPoint K x then f x else 0) else 0) =
      ∑ S ∈ (Finset.univ : Finset (DyadicPrime K)).powerset,
        (-1:ℂ)^S.card * (if x ∈ idealZLattice K
          (FractionalIdeal.mk0 K (dyadicSubideal K J S)) then f x else 0) := by
  by_cases hx : ∃ a : 𝓞 K, embeddingCoords K (a:K)=x
  · obtain ⟨a,rfl⟩ := hx
    simp only [embedding_mem_idealZLattice_mk0, oddNormPoint_embedding]
    have h := indicator_dyadicSubideal K ℂ J hJ a (f (embeddingCoords K (a:K)))
    simpa only [ite_and] using h
  · have hn (I : (Ideal (𝓞 K))⁰) : x ∉ idealZLattice K (FractionalIdeal.mk0 K I) := by
      intro hm
      obtain ⟨a,ha,he⟩ := (mem_idealZLattice_mk0_iff K I x).mp hm
      exact hx ⟨a,he⟩
    simp only [hn, ↓reduceIte, mul_zero, Finset.sum_const_zero]

 theorem tsum_odd_idealZLattice (J : (Ideal (𝓞 K))⁰)
    (hJ : Odd (Ideal.absNorm (J : Ideal (𝓞 K))))
    (f : EuclideanSpace ℝ (index K) → ℂ)
    (hf : ∀ S : Finset (DyadicPrime K), Summable fun v :
      idealZLattice K (FractionalIdeal.mk0 K (dyadicSubideal K J S)) => f v) :
    (∑' v : idealZLattice K (FractionalIdeal.mk0 K J),
      if oddNormPoint K v then f v else 0) =
      ∑ S ∈ (Finset.univ : Finset (DyadicPrime K)).powerset,
        (-1:ℂ)^S.card * ∑' v : idealZLattice K
          (FractionalIdeal.mk0 K (dyadicSubideal K J S)), f v := by
  have hind (S : Finset (DyadicPrime K)) : Summable fun x : EuclideanSpace ℝ (index K) =>
      if x ∈ idealZLattice K (FractionalIdeal.mk0 K (dyadicSubideal K J S)) then f x else 0 := by
    exact summable_subtype_iff_indicator.mp (hf S)
  calc
    _ = ∑' x : EuclideanSpace ℝ (index K),
        (idealZLattice K (FractionalIdeal.mk0 K J) : Set _).indicator
          (fun x => if oddNormPoint K x then f x else 0) x :=
      tsum_subtype (idealZLattice K (FractionalIdeal.mk0 K J) : Set _)
        (fun x => if oddNormPoint K x then f x else 0)
    _ = ∑' x : EuclideanSpace ℝ (index K),
        ∑ S ∈ (Finset.univ : Finset (DyadicPrime K)).powerset,
          (-1:ℂ)^S.card * (if x ∈ idealZLattice K
            (FractionalIdeal.mk0 K (dyadicSubideal K J S)) then f x else 0) := by
      apply tsum_congr
      intro x
      exact indicator_odd_idealZLattice K J hJ f x
    _ = _ := by
      rw [Summable.tsum_finsetSum (fun S _ => (hind S).mul_left _)]
      apply Finset.sum_congr rfl
      intro S _
      rw [tsum_mul_left]
      congr 1
      exact (tsum_subtype (idealZLattice K
        (FractionalIdeal.mk0 K (dyadicSubideal K J S)) : Set _) f).symm

 theorem heckeOddSignedTerm_tsum_inclusionExclusion (J : (Ideal (𝓞 K))⁰)
    (hJ : Odd (Ideal.absNorm (J : Ideal (𝓞 K)))) {t : ℝ} (ht : 0<t) (u : logSpace K) :
    (∑' v : idealZLattice K (FractionalIdeal.mk0 K J),
      (heckeOddSignedTerm K t u v : ℂ)) =
      ∑ S ∈ (Finset.univ : Finset (DyadicPrime K)).powerset,
        (-1:ℂ)^S.card * heckeParityTheta (heckeRealParity K)
          (idealZLattice K (FractionalIdeal.mk0 K (dyadicSubideal K J S)))
          (placeWeights K (heckeWeights K t u)) := by
  have ha : ∀ i, 0 < placeWeights K (heckeWeights K t u) i := by
    rintro (w | ⟨w,j⟩) <;> exact heckeWeights_pos K ht u w
  have hf (S : Finset (DyadicPrime K)) := summable_heckeParityKernel (heckeRealParity K)
    (idealZLattice K (FractionalIdeal.mk0 K (dyadicSubideal K J S))) ha
  have h := tsum_odd_idealZLattice K J hJ
    (heckeParityKernel (heckeRealParity K) (placeWeights K (heckeWeights K t u))) hf
  simpa only [heckeParityTheta, heckeParityKernel_eq_signedTerm, heckeOddSignedTerm,
    apply_ite, Complex.ofReal_zero] using h

end UnitDistance.NumberFieldAnalysis
