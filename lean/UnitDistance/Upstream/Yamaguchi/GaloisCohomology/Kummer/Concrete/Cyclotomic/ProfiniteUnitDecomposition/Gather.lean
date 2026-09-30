/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.FiniteFree

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Compiled free-coordinate gathering stage of the profinite-unit decomposition
-/

open scoped Topology

noncomputable section

namespace KummerTheory.ProfiniteUnitDecomposition.Internal

open ClassFormation
open LocalFieldTheory.Padic

/-- Reassemble the family of local additive coordinates into `ℤ̂`. -/
noncomputable def gatherFree :
    ((p : Nat.Primes) → Multiplicative ℤ_[p.1]) ≃ₜ*
      Multiplicative ZHat :=
  (continuousPiMultiplicative
      (fun p : Nat.Primes => ℤ_[p.1])).symm.trans
    (continuousMultiplicativeEquivOfAddEquiv
      zHatContinuousAddEquivPrimeProduct).symm

end KummerTheory.ProfiniteUnitDecomposition.Internal
