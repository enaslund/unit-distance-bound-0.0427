module

public import UnitDistance.Sqrt241.Cut.Basic

@[expose] public section
set_option backward.privateInPublic true


/-!
# The dyadic local groups in the cut quotient

At `𝔭₂` all seven literal relations of the order-32 group `D` (including
`y₂²`) are cut words, so the lifted genuine relation `r₂` is in the cut
kernel. At `𝔭₁` the six cuts other than `y₁²` are words and the lifted genuine
relation `r₁` is in the cut kernel by the presentation hypothesis. Hence both
local maps factor through `D` (`Dyadic.ArithmeticPresentation.factors_through_model`),
and when the labels hold, the composite with the retained map is the explicit
embedding `Retained.dyadicMapOfLifts` (so all layers inject).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.Sqrt241.Cut
open ProCGroups ProCGroups.ProC ProCGroups.Presentations GroupData GroupAugmentation
open Dyadic.Presentation (comm literalRelations)

namespace SourceLifts
variable (A : SourceLifts)

/-- The images of the local literal relations are the literal dyadic words. -/
theorem dyadic_literal (P : Fin 2) (i : Fin 7) :
    A.dyadic P (Dyadic.ArithmeticPresentation.relations i) =
      literalRelations (A.lifts.dyadicX P) (A.lifts.dyadicY P) (A.lifts.dyadicZ P) i := by
  change A.dyadic P (literalRelations Dyadic.ArithmeticPresentation.x
    Dyadic.ArithmeticPresentation.y Dyadic.ArithmeticPresentation.z i) = _
  have h := Dyadic.Presentation.map_literalRelations (A.dyadic P).toMonoidHom
    Dyadic.ArithmeticPresentation.x Dyadic.ArithmeticPresentation.y
    Dyadic.ArithmeticPresentation.z i
  exact h

/-- Every literal dyadic relation except `y₁²` is a cut word. -/
theorem literal_mem_words (P : Fin 2) (i : Fin 7) (hi : P = 1 ∨ i ≠ 1) :
    literalRelations (A.lifts.dyadicX P) (A.lifts.dyadicY P) (A.lifts.dyadicZ P) i ∈
      A.lifts.words := by
  fin_cases P <;> fin_cases i
  · exact Or.inl (Or.inl ⟨7,rfl⟩)
  · exact absurd rfl (hi.resolve_left (by decide))
  · exact Or.inl (Or.inl ⟨8,rfl⟩)
  · exact Or.inl (Or.inl ⟨9,rfl⟩)
  · exact Or.inl (Or.inr ⟨0,rfl⟩)
  · exact Or.inr ⟨0,rfl⟩
  · exact Or.inr ⟨1,rfl⟩
  · exact Or.inl (Or.inl ⟨10,rfl⟩)
  · exact Or.inl (Or.inl ⟨6,rfl⟩)
  · exact Or.inl (Or.inl ⟨11,rfl⟩)
  · exact Or.inl (Or.inl ⟨12,rfl⟩)
  · exact Or.inl (Or.inr ⟨1,rfl⟩)
  · exact Or.inr ⟨2,rfl⟩
  · exact Or.inr ⟨3,rfl⟩

theorem dyadic_cut_mem_kernel (P : Fin 2) (g : LocalSource)
    (hg : g ∈ Dyadic.ArithmeticPresentation.cuts) : A.dyadic P g ∈ A.kernel := by
  obtain ⟨i,hi,rfl⟩ := hg
  rw [dyadic_literal]
  exact A.word_mem_kernel (A.literal_mem_words P i (Or.inr hi))

/-- The closed kernel of the local model is mapped into the cut kernel at `𝔭₂`. -/
theorem dyadic_two_modelKernel_le (g : LocalSource)
    (hg : g ∈ (Dyadic.ArithmeticPresentation.relationKernel : Subgroup LocalSource)) :
    A.dyadic 1 g ∈ A.kernel := by
  let N : Subgroup LocalSource := A.kernel.comap (A.dyadic 1).toMonoidHom
  have hN : IsClosed (N : Set LocalSource) := A.kernel_isClosed.preimage (A.dyadic 1).continuous
  have hle : (Dyadic.ArithmeticPresentation.relationKernel : Subgroup LocalSource) ≤ N := by
    rw [← Dyadic.ArithmeticPresentation.literal_presentation]
    apply closedNormalClosure_le_closed_normal hN
    rintro _ ⟨i,rfl⟩
    change A.dyadic 1 _ ∈ A.kernel
    rw [dyadic_literal]
    exact A.word_mem_kernel (A.literal_mem_words 1 i (Or.inl rfl))
  exact hle hg

/-- The genuine relation `r` is killed in the local model. -/
theorem genuine_mem_modelKernel (r : LocalSource)
    (hr : Dyadic.ArithmeticPresentation.detector r = FreeThreeQuadratic.relation) :
    r ∈ (Dyadic.ArithmeticPresentation.relationKernel : Subgroup LocalSource) := by
  change FreeThreeDyadicQuotient.quotient (Dyadic.ArithmeticPresentation.detector r) = 1
  rw [hr,FreeThreeDyadicQuotient.quotient_relation]

theorem genuine_two_mem_kernel (r : LocalSource)
    (hr : Dyadic.ArithmeticPresentation.detector r = FreeThreeQuadratic.relation) :
    A.dyadic 1 r ∈ A.kernel :=
  A.dyadic_two_modelKernel_le r (genuine_mem_modelKernel r hr)

theorem relators_mem_kernel (r : LocalSource)
    (hr : Dyadic.ArithmeticPresentation.detector r = FreeThreeQuadratic.relation) (i : Fin 7) :
    A.relators r i ∈ A.kernel := by
  fin_cases i
  · exact A.quadratic_mem_kernel 0
  · exact A.quadratic_mem_kernel 1
  · exact A.quadratic_mem_kernel 2
  · exact A.quadratic_mem_kernel 3
  · exact A.quadratic_mem_kernel 4
  · exact A.quadratic_mem_kernel 5
  · exact A.genuine_two_mem_kernel r hr

/-- The closed normal closure of the seven relators lies in the cut kernel. -/
theorem relators_closure_le_kernel (r : LocalSource)
    (hr : Dyadic.ArithmeticPresentation.detector r = FreeThreeQuadratic.relation) :
    closedNormalClosure (Set.range (A.relators r)) ≤ A.kernel := by
  apply closedNormalClosure_le_closed_normal A.kernel_isClosed
  rintro _ ⟨i,rfl⟩
  exact A.relators_mem_kernel r hr i

theorem genuine_one_mem_kernel (r : LocalSource)
    (hr : Dyadic.ArithmeticPresentation.detector r = FreeThreeQuadratic.relation)
    (hgen : A.Presentation r) : A.dyadic 0 r ∈ A.kernel :=
  A.relators_closure_le_kernel r hr hgen

theorem genuine_mem_kernel (r : LocalSource)
    (hr : Dyadic.ArithmeticPresentation.detector r = FreeThreeQuadratic.relation)
    (hgen : A.Presentation r) (P : Fin 2) : A.dyadic P r ∈ A.kernel := by
  fin_cases P
  · exact A.genuine_one_mem_kernel r hr hgen
  · exact A.genuine_two_mem_kernel r hr

theorem exists_dyadicQuotientMap (r : LocalSource)
    (hr : Dyadic.ArithmeticPresentation.detector r = FreeThreeQuadratic.relation)
    (hgen : A.Presentation r) (P : Fin 2) :
    ∃ f : Dyadic.D →ₜ* A.ActualQuotient,
      f.comp Dyadic.ArithmeticPresentation.model = A.projection.comp (A.dyadic P) :=
  Dyadic.ArithmeticPresentation.factors_through_model (A.projection.comp (A.dyadic P)) r hr
    (A.projection_eq_one_of_mem (A.genuine_mem_kernel r hr hgen P))
    (fun g hg => A.projection_eq_one_of_mem (A.dyadic_cut_mem_kernel P g hg))

/-- The local group `D` at `𝔭_P` in the cut quotient. -/
def dyadicQuotientMap (r : LocalSource)
    (hr : Dyadic.ArithmeticPresentation.detector r = FreeThreeQuadratic.relation)
    (hgen : A.Presentation r) (P : Fin 2) : Dyadic.D →ₜ* A.ActualQuotient :=
  Classical.choose (A.exists_dyadicQuotientMap r hr hgen P)

theorem dyadicQuotientMap_model (r : LocalSource)
    (hr : Dyadic.ArithmeticPresentation.detector r = FreeThreeQuadratic.relation)
    (hgen : A.Presentation r) (P : Fin 2) (g : LocalSource) :
    A.dyadicQuotientMap r hr hgen P (Dyadic.ArithmeticPresentation.model g) =
      A.projection (A.dyadic P g) :=
  congrArg (fun f : LocalSource →ₜ* A.ActualQuotient => f g)
    (Classical.choose_spec (A.exists_dyadicQuotientMap r hr hgen P))

/-- The global lifts of the dyadic generators `x, y, z` at `𝔭_P`. -/
def dyadicXYZ (P : Fin 2) : Fin 3 → Source :=
  ![A.lifts.dyadicX P,A.lifts.dyadicY P,A.lifts.dyadicZ P]

def localXYZ : Fin 3 → LocalSource :=
  ![Dyadic.ArithmeticPresentation.x,Dyadic.ArithmeticPresentation.y,Dyadic.ArithmeticPresentation.z]

theorem model_localXYZ (j : Fin 3) :
    Dyadic.ArithmeticPresentation.model (localXYZ j) = Dyadic.Filtration.gen j := by
  fin_cases j
  · exact Dyadic.ArithmeticPresentation.model_x
  · exact Dyadic.ArithmeticPresentation.model_y
  · exact Dyadic.ArithmeticPresentation.model_z

theorem dyadicXYZ_eq (P : Fin 2) (j : Fin 3) : A.dyadicXYZ P j = A.dyadic P (localXYZ j) := by
  fin_cases j <;> rfl

theorem dyadicQuotientMap_gen (r : LocalSource)
    (hr : Dyadic.ArithmeticPresentation.detector r = FreeThreeQuadratic.relation)
    (hgen : A.Presentation r) (P : Fin 2) (j : Fin 3) :
    A.dyadicQuotientMap r hr hgen P (Dyadic.Filtration.gen j) = A.projection (A.dyadicXYZ P j) := by
  rw [← model_localXYZ,dyadicQuotientMap_model,dyadicXYZ_eq]

/-- With the labels, the retained composite is the explicit adapted embedding. -/
theorem retained_dyadicQuotientMap (r : LocalSource)
    (hr : Dyadic.ArithmeticPresentation.detector r = FreeThreeQuadratic.relation)
    (hgen : A.Presentation r) (hL : A.Labels) (P : Fin 2) :
    (A.retained hL).toMonoidHom.comp (A.dyadicQuotientMap r hr hgen P).toMonoidHom =
      Retained.dyadicMapOfLifts P (retainedFree (A.lifts.dyadicX P))
        (retainedFree (A.lifts.dyadicY P)) (retainedFree (A.lifts.dyadicZ P)) := by
  apply MonoidHom.eq_of_eqOn_dense dyadic_generators
  rintro _ ⟨j,rfl⟩
  change A.retained hL (A.dyadicQuotientMap r hr hgen P (Dyadic.Filtration.gen j)) = _
  rw [dyadicQuotientMap_gen,retained_projection]
  rw [Retained.dyadicMapOfLifts_gen]
  · fin_cases j <;> rfl
  · fin_cases j
    · exact hL.dyadicX P
    · exact hL.dyadicY P
    · exact hL.dyadicZ P

theorem dyadicQuotientMap_layers (r : LocalSource)
    (hr : Dyadic.ArithmeticPresentation.detector r = FreeThreeQuadratic.relation)
    (hgen : A.Presentation r) (hL : A.Labels) (P : Fin 2) (n : ℕ) :
    Function.Injective (layerMap F Dyadic.D (A.dyadicQuotientMap r hr hgen P).toMonoidHom n) :=
  LocalModels.layers_of_comp _ (A.retained hL).toMonoidHom _
    (A.retained_dyadicQuotientMap r hr hgen hL P) (Retained.dyadicMapOfLifts_layers P _ _ _) n

end SourceLifts
end UnitDistance.Sqrt241.Cut
