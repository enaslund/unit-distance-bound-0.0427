/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.ClassFieldTheory.AlgebraicNumberTheory.Idele.LocallyCompact
public import UnitDistance.Upstream.Yamaguchi.ValuedFieldTheory.Valuation.ValuedAdicComplete
public import Mathlib.NumberTheory.NumberField.ProductFormula

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Canonical structures on finite completions

This module installs the complete discrete valuation, characteristic-zero,
and finite residue-field structures used by finite-place class-field
arithmetic.
-/

open scoped NumberField ValuativeRel
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

variable {K : Type} [Field K] [NumberField K]

/-- The distinguished valuation on a finite completion of a number field is
complete discrete. -/
noncomputable instance finitePlaceAdicCompletion_isCompleteDiscrete
    (v₀ : HeightOneSpectrum (𝓞 K)) :
    ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete
      (Valued.v :
        Valuation (v₀.adicCompletion K)
          (WithZero (Multiplicative ℤ))) where
  isRankOneDiscrete := inferInstance
  isAdicComplete :=
    ValuationTheory.Valuations.rankOneDiscreteValuationSubring_isAdicComplete

/-- A finite completion of a number field has characteristic zero. -/
noncomputable instance finitePlaceAdicCompletion_charZero
    (v₀ : HeightOneSpectrum (𝓞 K)) :
    CharZero (v₀.adicCompletion K) :=
  charZero_of_injective_algebraMap
    (algebraMap K (v₀.adicCompletion K)).injective

/-- The residue field of a finite completion of a number field is finite. -/
noncomputable instance finitePlaceAdicCompletion_residueFinite
    (v₀ : HeightOneSpectrum (𝓞 K)) :
    Finite
      (IsLocalRing.ResidueField
        (Valued.v :
          Valuation (v₀.adicCompletion K)
            (WithZero (Multiplicative ℤ))).valuationSubring) := by
  change Finite (Valued.ResidueField (v₀.adicCompletion K))
  exact _root_.finite_adicCompletion_residueField K v₀

end GlobalClassFieldTheory.ClassFieldAxiom

end
