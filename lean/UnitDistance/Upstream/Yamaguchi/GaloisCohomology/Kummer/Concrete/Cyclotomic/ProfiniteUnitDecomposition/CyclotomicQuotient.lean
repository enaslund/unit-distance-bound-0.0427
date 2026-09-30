/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.TorsionQuotientMk

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# The cyclotomic profinite-unit torsion quotient
-/

open scoped Topology

noncomputable section

namespace KummerTheory

open ClassFormation

/-- Cyclotomic-character form of the torsion decomposition: quotienting `ℤ̂ˣ` by
the closure of its torsion subgroup leaves one copy of `ℤ̂`. -/
noncomputable def zHatUnitsTorsionQuotientEquiv :
    ZHatˣ ⧸ (CommGroup.torsion ZHatˣ).topologicalClosure ≃ₜ*
      Multiplicative ZHat :=
  torsionQuotientEquivOfZHatMulDecomposition
    ZHatˣ CyclotomicFinitePart
      zHatUnitsDecomposition
        dense_torsion_cyclotomicFinitePart

end KummerTheory
