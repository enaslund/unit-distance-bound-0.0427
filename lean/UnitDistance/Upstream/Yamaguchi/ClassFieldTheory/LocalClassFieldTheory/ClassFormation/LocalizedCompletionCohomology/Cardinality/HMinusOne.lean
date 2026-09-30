/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.H0

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Degree-minus-one localized Herbrand cardinality
-/

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand
open scoped TensorProduct

noncomputable section

namespace LocalClassFieldTheory

section LocalTateComparison

variable {k ell : Type}
    [Field k] [Field ell] [Algebra k ell]
    [FiniteDimensional k ell] [IsGalois k ell]

theorem localHerbrandHMinusOne_card_eq_one
    (vK : AbsoluteValue k ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK ell)
    (σ : ell ≃ₐ[k] ell)
    (hgen : ∀ τ : ell ≃ₐ[k] ell,
      τ ∈ Subgroup.zpowers σ)
    [ValuativeRel vK.Completion]
    [IsNonarchimedeanLocalField vK.Completion] :
    letI hK :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := k) w.1
    letI : SMul k w.1.Completion := hK.toSMul
    letI : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    letI := localizedCompletionGlobalAlgebra vK w
    letI := localizedCompletionIsScalarTower vK w
    letI : FiniteDimensional vK.Completion
        (LocalizedCompletion vK w) :=
      localizedCompletionModuleFinite vK hvK w
    letI : IsGalois vK.Completion
        (LocalizedCompletion vK w) :=
      HilbertRamification.algebraicLocalization_isGalois vK w
    letI : Fintype (absoluteValueDecompositionGroup k w.1) :=
      Fintype.ofFinite _
    letI :=
      decompositionGroupLocalUnitsAction vK hvK w
    letI : Finite
        (HerbrandHMinusOne
          (absoluteValueDecompositionGroup k w.1)
          (LocalizedCompletion vK w)ˣ
          (subgroupGeneratorOfGenerator
            (absoluteValueDecompositionGroup k w.1)
            σ hgen)) :=
      localHerbrandHMinusOneFinite
        vK hvK w σ hgen
    Nat.card
        (HerbrandHMinusOne
          (absoluteValueDecompositionGroup k w.1)
          (LocalizedCompletion vK w)ˣ
          (subgroupGeneratorOfGenerator
            (absoluteValueDecompositionGroup k w.1)
            σ hgen)) = 1 := by
  let := localizedCompletionBaseAlgebra vK w
  let := localizedCompletionGlobalAlgebra vK w
  let := localizedCompletionIsScalarTower vK w
  let : FiniteDimensional vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionFiniteDimensional vK hvK w
  let : IsGalois vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionIsGalois vK w
  let := localizedCompletionDecompositionGroupFintype vK w
  let :=
    decompositionGroupLocalUnitsAction vK hvK w
  let : Finite
      (HerbrandHMinusOne
        (absoluteValueDecompositionGroup k w.1)
        (LocalizedCompletion vK w)ˣ
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup k w.1)
          σ hgen)) :=
    localHerbrandHMinusOneFinite
      vK hvK w σ hgen
  let g :=
    localizedCompletionGaloisGenerator
      vK hvK w σ hgen
  let hg :=
    localizedCompletionGaloisGenerator_generates
      vK hvK w σ hgen
  let hcard :=
    finiteExtensionUnits_tate_card_of_generator
      vK.Completion (LocalizedCompletion vK w)
      g hg
  calc
    Nat.card
        (HerbrandHMinusOne
          (absoluteValueDecompositionGroup k w.1)
          (LocalizedCompletion vK w)ˣ
          (subgroupGeneratorOfGenerator
            (absoluteValueDecompositionGroup k w.1)
            σ hgen)) =
      Nat.card
        (tateCohomology
          (Rep.ofAlgebraAutOnUnits vK.Completion
            (LocalizedCompletion vK w)) (-1)) :=
      Nat.card_congr
        (localHerbrandHMinusOneEquivUnitsTateHminusOne
          vK hvK w σ hgen)
    _ = 1 := hcard.cardHminusOne


end LocalTateComparison

end LocalClassFieldTheory
