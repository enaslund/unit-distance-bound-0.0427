/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.Trivial

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Localized-units Herbrand quotient
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

theorem localUnits_herbrandQuotient_eq_localDegree
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
        (HerbrandH0
          (absoluteValueDecompositionGroup k w.1)
          (LocalizedCompletion vK w)ˣ) :=
      localHerbrandH0Finite vK hvK w σ hgen
    letI : Finite
        (HerbrandHMinusOne
          (absoluteValueDecompositionGroup k w.1)
          (LocalizedCompletion vK w)ˣ
          (subgroupGeneratorOfGenerator
            (absoluteValueDecompositionGroup k w.1)
            σ hgen)) :=
      localHerbrandHMinusOneFinite
        vK hvK w σ hgen
    herbrandQuotient
        (G := absoluteValueDecompositionGroup k w.1)
        (A := (LocalizedCompletion vK w)ˣ)
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup k w.1)
          σ hgen) =
      (Module.finrank vK.Completion
        (LocalizedCompletion vK w) : ℚ) := by
  let _ := localizedCompletionBaseAlgebra vK w
  let _ := localizedCompletionGlobalAlgebra vK w
  let _ := localizedCompletionIsScalarTower vK w
  let _ : FiniteDimensional vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionFiniteDimensional vK hvK w
  let _ : IsGalois vK.Completion
      (LocalizedCompletion vK w) :=
    localizedCompletionIsGalois vK w
  let _ := localizedCompletionDecompositionGroupFintype vK w
  let _ :=
    decompositionGroupLocalUnitsAction vK hvK w
  let _ : Finite
      (HerbrandH0
        (absoluteValueDecompositionGroup k w.1)
        (LocalizedCompletion vK w)ˣ) :=
    localHerbrandH0Finite vK hvK w σ hgen
  let _ : Finite
      (HerbrandHMinusOne
        (absoluteValueDecompositionGroup k w.1)
        (LocalizedCompletion vK w)ˣ
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup k w.1)
          σ hgen)) :=
    localHerbrandHMinusOneFinite
      vK hvK w σ hgen
  rw [herbrandQuotient_eq_card_ratio,
    localHerbrandH0_card_eq_localDegree
      vK hvK w σ hgen,
    localHerbrandHMinusOne_card_eq_one
      vK hvK w σ hgen]
  simp


end LocalTateComparison

end LocalClassFieldTheory
