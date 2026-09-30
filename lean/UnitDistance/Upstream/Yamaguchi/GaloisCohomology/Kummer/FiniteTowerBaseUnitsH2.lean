/-
Ported from Naganori Yamaguchi, SawinTotallyRealTowers, commit
3a455e1aa9140dbbe7b7d68f508392a69c86d0f4, under Apache-2.0.
Modified: project-local imports relocated; Lean 4.32 compatibility changes
are recorded in third-party/yamaguchi/compatibility.patch.
Original declaration namespaces and mathematical statements are retained.
-/

module

public import UnitDistance.Upstream.Yamaguchi.GaloisCohomology.Kummer.FiniteCyclicBaseUnitsH2
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

@[expose] public section
set_option backward.privateInPublic true


set_option autoImplicit false

/-!
# Base-unit coefficients along a field tower

The inclusions Kˣ → Lˣ → Nˣ give an actual equivariant coefficient map
for Gal(N/L), starting with the trivial action on Kˣ.
-/

open CategoryTheory

namespace ClassFieldTower.Cohomology

noncomputable section

variable (K L N : Type) [Field K] [Field L] [Field N]
  [Algebra K L] [Algebra L N]

/-- Inclusion of base units along the two given algebra maps. -/
def finiteTowerBaseUnitsRepHom :
    Rep.trivial ℤ Gal(N/L) (Additive Kˣ) ⟶ Rep.ofAlgebraAutOnUnits L N :=
  (Rep.trivialFunctor ℤ Gal(N/L)).map
    (ModuleCat.ofHom
      (Units.map (algebraMap K L).toMonoidHom).toAdditive.toIntLinearMap) ≫
    finiteGaloisBaseUnitsRepHom L N

/-- The induced degree-two coefficient map for the actual field tower. -/
def finiteTowerBaseUnitsH2Map :
    groupCohomology (Rep.trivial ℤ Gal(N/L) (Additive Kˣ)) 2 ⟶
      groupCohomology (Rep.ofAlgebraAutOnUnits L N) 2 :=
  groupCohomology.map (MonoidHom.id Gal(N/L)) (finiteTowerBaseUnitsRepHom K L N) 2

end
end ClassFieldTower.Cohomology
