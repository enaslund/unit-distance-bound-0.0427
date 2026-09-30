/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.Kummer.Concrete.Cyclotomic.ProfiniteUnitDecomposition.Local

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Compiled finite/free collection stage of the profinite-unit decomposition
-/

open scoped Topology

noncomputable section

namespace KummerTheory.ProfiniteUnitDecomposition.Internal

open LocalFieldTheory.Padic

/-- Collect the finite and torsion-free coordinates of the local product. -/
noncomputable def finiteFreeSplit :
    ((p : Nat.Primes) →
      padicUnitFiniteFactor p.1 × Multiplicative ℤ_[p.1]) ≃ₜ*
    ((p : Nat.Primes) → Multiplicative ℤ_[p.1]) ×
      CyclotomicFinitePart where
  toFun x := (fun p => (x p).2, fun p => (x p).1)
  invFun x p := (x.2 p, x.1 p)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun :=
    (continuous_pi fun p =>
      continuous_snd.comp (continuous_apply p)).prodMk
        (continuous_pi fun p =>
          continuous_fst.comp (continuous_apply p))
  continuous_invFun :=
    continuous_pi fun p =>
      ((continuous_apply p).comp continuous_snd).prodMk
        ((continuous_apply p).comp continuous_fst)

end KummerTheory.ProfiniteUnitDecomposition.Internal
