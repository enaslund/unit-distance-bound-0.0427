/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Gather

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Compiled final swap stage of the profinite-unit decomposition
-/

open scoped Topology

noncomputable section

namespace KummerTheory.ProfiniteUnitDecomposition.Internal

open ClassFormation

/-- Swap the collected free and finite coordinates. -/
noncomputable def freeFiniteSwap :
    CyclotomicFinitePart × Multiplicative ZHat ≃ₜ*
      Multiplicative ZHat × CyclotomicFinitePart :=
  LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.continuousMulEquivProdComm
    CyclotomicFinitePart (Multiplicative ZHat)

end KummerTheory.ProfiniteUnitDecomposition.Internal
