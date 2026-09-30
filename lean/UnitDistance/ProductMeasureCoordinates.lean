module

public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section
set_option backward.privateInPublic true


/-! # Measure-preserving regrouping of dependent product coordinates

The dependent Pi/product argument generalizes Mathlib's
`measurePreserving_arrowProdEquivProdArrow`; its proof follows the same
finite-spanning-rectangle measure uniqueness argument.
-/

noncomputable section
open MeasureTheory MeasureTheory.Measure Set
open scoped Classical

namespace UnitDistance

section Pi
variable {ι : Type*} [Fintype ι] (A B : ι → Type*)
  [∀ i, MeasurableSpace (A i)] [∀ i, MeasurableSpace (B i)]

/-- Split the two coordinates in each member of a dependent finite product. -/
def piProdCoordinates : ((i : ι) → A i × B i) ≃ᵐ ((i : ι) → A i) × ((i : ι) → B i) where
  toFun x := (fun i => (x i).1, fun i => (x i).2)
  invFun x i := (x.1 i, x.2 i)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := by
    exact (Measurable.of_eval fun i =>
      measurable_fst.comp (measurable_pi_apply i)).prodMk
      (Measurable.of_eval fun i => measurable_snd.comp (measurable_pi_apply i))
  measurable_invFun := by
    exact Measurable.of_eval fun i =>
      ((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd)

/-- Exact product-measure normalization for dependent coordinate regrouping. -/
theorem piProdCoordinates_measurePreserving
    (μ : (i : ι) → Measure (A i)) (ν : (i : ι) → Measure (B i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)] :
    MeasurePreserving (piProdCoordinates A B) (Measure.pi (fun i => (μ i).prod (ν i)))
      ((Measure.pi μ).prod (Measure.pi ν)) where
  measurable := (piProdCoordinates A B).measurable
  map_eq := by
    refine (FiniteSpanningSetsIn.ext ?_ (isPiSystem_pi.prod isPiSystem_pi)
      ((FiniteSpanningSetsIn.pi fun i => (μ i).toFiniteSpanningSetsIn).prod
      (FiniteSpanningSetsIn.pi (fun i => (ν i).toFiniteSpanningSetsIn))) ?_).symm
    · refine (generateFrom_eq_prod generateFrom_pi generateFrom_pi ?_ ?_).symm
      · exact (FiniteSpanningSetsIn.pi (fun i => (μ i).toFiniteSpanningSetsIn)).isCountablySpanning
      · exact (FiniteSpanningSetsIn.pi (fun i => (ν i).toFiniteSpanningSetsIn)).isCountablySpanning
    · rintro _ ⟨s, ⟨s, _, rfl⟩, ⟨_, ⟨t, _, rfl⟩, rfl⟩⟩
      rw [MeasurableEquiv.map_apply]
      have he : piProdCoordinates A B ⁻¹' (univ.pi s ×ˢ univ.pi t) =
          univ.pi (fun i => s i ×ˢ t i) := by
        ext x
        simp [piProdCoordinates, Set.mem_pi, forall_and]
      rw [he]
      simp_rw [Measure.pi_pi, Measure.prod_prod, Measure.pi_pi, Finset.prod_mul_distrib]

end Pi

section Cross
variable {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace C] [MeasurableSpace D]

/-- Regroup four coordinates, putting the first and third together. -/
def prodCrossCoordinates : ((A × B) × (C × D)) ≃ᵐ ((A × C) × (B × D)) :=
  MeasurableEquiv.prodAssoc.trans
    (((MeasurableEquiv.refl A).prodCongr MeasurableEquiv.prodAssoc.symm).trans
      (((MeasurableEquiv.refl A).prodCongr
        (MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl D))).trans
        (((MeasurableEquiv.refl A).prodCongr MeasurableEquiv.prodAssoc).trans
          MeasurableEquiv.prodAssoc.symm)))

@[simp] theorem prodCrossCoordinates_apply (x : (A × B) × (C × D)) :
    prodCrossCoordinates x = ((x.1.1, x.2.1), (x.1.2, x.2.2)) := rfl

theorem prodCrossCoordinates_measurePreserving
    (μa : Measure A) (μb : Measure B) (μc : Measure C) (μd : Measure D)
    [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd] :
    MeasurePreserving prodCrossCoordinates ((μa.prod μb).prod (μc.prod μd))
      ((μa.prod μc).prod (μb.prod μd)) := by
  have h₁ := measurePreserving_prodAssoc μa μb (μc.prod μd)
  have h₂ := (MeasurePreserving.id μa).prod
    ((measurePreserving_prodAssoc μb μc μd).symm MeasurableEquiv.prodAssoc)
  have h₃ := (MeasurePreserving.id μa).prod
    ((Measure.measurePreserving_swap (μ := μb) (ν := μc)).prod (MeasurePreserving.id μd))
  have h₄ := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μc μb μd)
  have h₅ := (measurePreserving_prodAssoc μa μc (μb.prod μd)).symm MeasurableEquiv.prodAssoc
  exact h₅.comp (h₄.comp (h₃.comp (h₂.comp h₁)))

end Cross

end UnitDistance
