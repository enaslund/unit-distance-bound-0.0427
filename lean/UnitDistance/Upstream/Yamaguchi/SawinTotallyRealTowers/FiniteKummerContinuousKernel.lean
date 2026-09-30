/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.FiniteKummerAbsoluteKernel
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.FiniteKummerAbsoluteLift
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.Kummer.FiniteKummerCoefficientH2
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.DiscreteH2Representatives
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.DiscreteH2Comparison
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.DiscreteH2ShortComplexComparison
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.DiscreteH2CochainComparison
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.FreeProPH2Cocycle
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.H2CentralExtensionClass
public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.ProP.TrivialZModP
public import Mathlib.FieldTheory.AbsoluteGaloisGroup
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.GaloisClosure
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.Tactic.Abel

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# The finite Kummer coefficient kernel lies in the absolute inflation kernel

The finite coefficient map is composed with the established discrete
continuous-to-ordinary H² comparison. Normalization changes a representative
by the boundary of a constant one-cochain. The representative-level
Hilbert-90 result therefore proves kernel containment for every finite
continuous H² class, with no assumption about a chosen representative.
-/

namespace ClassFieldTower.Sawin

open CategoryTheory ClassFieldTower.Cohomology ClassFieldTower.ProP
open ClassFieldTower.Martinet.Shafarevich

noncomputable section

/-- Normalizing a dehomogenized cocycle changes it by an explicit constant
one-cochain boundary and leaves its ordinary cohomology class unchanged. -/
theorem normalizedFiniteKummerTwoCocycle_H2π
    (K : Type) [Field K] (p : ℕ+) [Fact (p : ℕ).Prime]
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K))
    (z : trivialZModPCocyclesLifted (p : ℕ) Gal(E/K) 2) :
    groupCohomology.H2π
      (Rep.trivial ℤ Gal(E/K) (ULift.{0} (ZMod (p : ℕ))))
      (normalizedFiniteKummerTwoCocycle K p E z) =
    discreteContinuousH2AddEquiv
      (ContinuousCohomology.π (trivialZModPLifted (p : ℕ) Gal(E/K)) 2 z) := by
  rw [discreteContinuousH2AddEquiv_π]
  apply (groupCohomology.H2π_eq_iff _ _).mpr
  let a : ULift.{0} (ZMod (p : ℕ)) :=
    (((trivialZModPCochainsLifted (p : ℕ) Gal(E/K)).iCycles 2).hom z).1 1 1 1
  let c : Gal(E/K) → Gal(E/K) → ULift.{0} (ZMod (p : ℕ)) := fun g h ↦
    (((trivialZModPCochainsLifted (p : ℕ) Gal(E/K)).iCycles 2).hom z).1 1 g (g * h)
  refine ⟨fun _ : Gal(E/K) ↦ -a, ?_⟩
  funext gh
  change -a - -a + -a = (c gh.1 gh.2 - a) - c gh.1 gh.2
  abel

/-- The actual finite Kummer coefficient map on lifted continuous H²,
using the existing discrete comparison. Its target retains its natural
additive group structure; no mod-p module is imposed on field-unit H². -/
def finiteKummerContinuousH2Map
    (K : Type) [Field K] (p : ℕ+)
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K))
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty) :
    continuousCohomologyZModPLifted (p : ℕ) Gal(E/K) 2 →+
      groupCohomology (Rep.ofAlgebraAutOnUnits K E) 2 :=
  (finiteKummerCoefficientH2Map K E p hmu).hom.toAddMonoidHom.comp
    (discreteContinuousH2AddEquiv (p := (p : ℕ)) (Q := Gal(E/K))).toAddMonoidHom

/-- The kernel of finite Kummer coefficient change is contained in the
kernel of actual absolute inflation, for every finite continuous H² class. -/
theorem finiteKummerContinuousH2Map_ker_le_absoluteInflation_ker
    (K : Type) [Field K] [CharZero K] (p : ℕ+) [Fact (p : ℕ).Prime]
    (E : FiniteGaloisIntermediateField K (AlgebraicClosure K))
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty) :
    (finiteKummerContinuousH2Map K p E hmu).ker ≤
      (continuousCohomologyZModPMapLifted (p : ℕ)
        (absoluteFiniteGaloisRestriction K E) 2).hom.toLinearMap.toAddMonoidHom.ker := by
  intro x hx
  let z : trivialZModPCocyclesLifted (p : ℕ) Gal(E/K) 2 :=
    degreeTwoCocycleRepresentative x
  have hRepresentative :
      ContinuousCohomology.π (trivialZModPLifted (p : ℕ) Gal(E/K)) 2 z = x :=
    degreeTwoCocycleRepresentative_π x
  have hZero : (finiteKummerCoefficientH2Map K E p hmu).hom
      (groupCohomology.H2π
        (Rep.trivial ℤ Gal(E/K) (ULift.{0} (ZMod (p : ℕ))))
        (normalizedFiniteKummerTwoCocycle K p E z)) = 0 := by
    rw [normalizedFiniteKummerTwoCocycle_H2π, hRepresentative]
    exact hx
  change (continuousCohomologyZModPMapLifted (p : ℕ)
    (absoluteFiniteGaloisRestriction K E) 2).hom x = 0
  rw [← hRepresentative]
  exact absoluteInflation_eq_zero_of_finiteKummerH2_eq_zero K p E hmu z hZero

end

end ClassFieldTower.Sawin
