/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.CyclotomicQuotient

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Local coordinates of the profinite-unit decomposition
-/

open scoped Topology

noncomputable section

namespace KummerTheory

open ClassFormation
open LocalFieldTheory.Padic

/-- The `p`-adic coordinate of the global free factor in
`zHatUnitsDecomposition` is exactly the free factor in the genuine
local decomposition of the `p`-adic unit coordinate. -/
@[simp]
theorem zHatUnitsDecomposition_freeCoordinate
    (u : ZHatˣ) (p : Nat.Primes) :
    zHatToPadicInt p
        (Multiplicative.toAdd
          (zHatUnitsDecomposition u).1) =
      Multiplicative.toAdd
        (((padicUnitDecomposition p.1).symm
          (zHatUnitsContinuousMulEquivPrimeProduct u p)).2) := by
  let y : ProfiniteIntegerPrimeProduct :=
    fun q =>
      Multiplicative.toAdd
        (((padicUnitDecomposition q.1).symm
          (zHatUnitsContinuousMulEquivPrimeProduct u q)).2)
  change
    zHatToPadicInt p
        (zHatContinuousAddEquivPrimeProduct.symm y) =
      y p
  exact
    congrFun
      (zHatContinuousAddEquivPrimeProduct.apply_symm_apply y) p

end KummerTheory
