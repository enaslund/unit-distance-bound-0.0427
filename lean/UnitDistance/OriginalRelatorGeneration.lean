module

public import UnitDistance.SpecifiedRelators
public import UnitDistance.ClassTwoCentralCharacters
public import UnitDistance.UniversalQuadraticTame
public import Mathlib.Algebra.Module.Pi

@[expose] public section
set_option backward.privateInPublic true


/-!
# Six original quadratic coordinates detect a full relator family

This criterion combines the actual finite universal class-two detector with
continuous pro-two cohomology and relative Nakayama. Arithmetic still must
provide the map, its values on the six relators, and the sharp H² bound.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

namespace UnitDistance.OriginalRelatorGeneration

open ClassFieldTower.ProP ClassFieldTower.Cohomology
open ProCGroups ProCGroups.ProC ProCGroups.Presentations

local instance : AddCommGroup UniversalQuadratic.F :=
  Ring.toAddCommGroup
local instance : Module UniversalQuadratic.F UniversalQuadratic.F :=
  Semiring.toModule
local instance : AddCommGroup UniversalQuadratic.V := Pi.addCommGroup
local instance : AddCommGroup UniversalQuadratic.W := Pi.addCommGroup
local instance : Module UniversalQuadratic.F UniversalQuadratic.V :=
  Pi.Function.module (Fin 7) UniversalQuadratic.F UniversalQuadratic.F
local instance : Module UniversalQuadratic.F UniversalQuadratic.W :=
  Pi.Function.module (Fin 28) UniversalQuadratic.F UniversalQuadratic.F
local instance : TopologicalSpace
    (ClassTwo.GroupModel UniversalQuadratic.cocycle) := ⊥
local instance : DiscreteTopology
    (ClassTwo.GroupModel UniversalQuadratic.cocycle) := ⟨rfl⟩
local instance : IsTopologicalGroup
    (ClassTwo.GroupModel UniversalQuadratic.cocycle) := by infer_instance

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- An actual continuous genus coordinate of the universal finite quotient. -/
def baseCharacter (q : G →ₜ* UniversalQuadratic.Q) (i : Fin 7) :
    G →ₜ* Multiplicative (ZMod 2) where
  toFun g := Multiplicative.ofAdd ((q g).base i)
  map_one' := by simp
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    change (q (g * h)).base i = (q g).base i + (q h).base i
    rw [map_mul, ClassTwo.GroupModel.mul_base]
    rfl
  continuous_toFun :=
    (continuous_of_discreteTopology : Continuous (fun x : UniversalQuadratic.Q ↦
      Multiplicative.ofAdd (x.base i))).comp q.continuous_toFun

/-- The actual Frattini subgroup maps into the central coordinates of the
universal detector, since every continuous genus character kills it. -/
theorem base_eq_zero_of_mem_frattini (q : G →ₜ* UniversalQuadratic.Q)
    (g : G) (hg : g ∈ closedPowerCommutator 2 G) : (q g).base = 0 := by
  funext i
  exact congrArg Multiplicative.toAdd
    (closedPowerCommutator_le_character_ker (baseCharacter q i) hg)

/-- The six original relators normally generate the full actual closed
kernel once their universal quadratic images and the sharp actual H² bound
are proved. No character family or normal-generation assumption is supplied. -/
theorem closedNormalClosure_eq_of_original_images
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : HasPGroupOpenNormalBasis 2 G)
    (R : ClosedSubgroup G) [R.Normal]
    (hR : (R : Subgroup G) ≤ closedPowerCommutator 2 G)
    (ρ : Fin 6 → R) (q : G →ₜ* UniversalQuadratic.Q)
    (himage : ∀ i, (q (ρ i)).central = UniversalQuadratic.originalInitial i)
    [FiniteDimensional (ZMod 2)
      (continuousCohomologyZModPLifted 2 (G ⧸ (R : Subgroup G)) 2)]
    (hbound : Module.finrank (ZMod 2)
      (continuousCohomologyZModPLifted 2 (G ⧸ (R : Subgroup G)) 2) ≤ 6) :
    closedNormalClosure (Set.range (fun i ↦ (ρ i : G))) = (R : Subgroup G) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbase (r : R) : (q r).base = 0 :=
    base_eq_zero_of_mem_frattini q r (hR r.2)
  let χ (i : Fin 6) : R →ₜ* Multiplicative (ZMod 2) :=
    ClassTwo.centralCharacter UniversalQuadratic.cocycle q (R : Subgroup G)
      hbase (OriginalQuadratic.coordinate i)
  apply SpecifiedRelators.closedNormalClosure_eq_of_dual_characters
    hG R hR ρ χ
  · intro i g r
    exact ClassTwo.centralCharacter_conjNormal UniversalQuadratic.cocycle q
      (R : Subgroup G) hbase (OriginalQuadratic.coordinate i) g r
  · intro i j
    change OriginalQuadratic.coordinate i (q (ρ j)).central = _
    rw [himage, UniversalQuadratic.original_coordinate]
  · exact hbound

/-- Actual infinity-square and odd tame words give the required six images
using only the specified elementary inertia and Frobenius coordinates. -/
theorem closedNormalClosure_eq_of_tame_words
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : HasPGroupOpenNormalBasis 2 G)
    (R : ClosedSubgroup G) [R.Normal]
    (hR : (R : Subgroup G) ≤ closedPowerCommutator 2 G)
    (ρ : Fin 6 → R) (q : G →ₜ* UniversalQuadratic.Q)
    (c : G) (inertia frobenius : Fin 5 → G)
    (hinfinity : (ρ 0 : G) = c ^ 2)
    (htame : ∀ i, (ρ (UniversalQuadratic.oddIndex i) : G) =
      frobenius i * inertia i * (frobenius i)⁻¹ *
        ((inertia i) ^ UniversalQuadratic.oddPrimes i)⁻¹)
    (hc : (q c).base = UniversalQuadratic.inertiaVectors 0)
    (hinertia : ∀ i, (q (inertia i)).base =
      UniversalQuadratic.inertiaVectors (UniversalQuadratic.oddIndex i))
    (hfrobenius : ∀ i, (q (frobenius i)).base =
      UniversalQuadratic.frobeniusVectors (UniversalQuadratic.oddIndex i))
    [FiniteDimensional (ZMod 2)
      (continuousCohomologyZModPLifted 2 (G ⧸ (R : Subgroup G)) 2)]
    (hbound : Module.finrank (ZMod 2)
      (continuousCohomologyZModPLifted 2 (G ⧸ (R : Subgroup G)) 2) ≤ 6) :
    closedNormalClosure (Set.range (fun i ↦ (ρ i : G))) = (R : Subgroup G) := by
  apply closedNormalClosure_eq_of_original_images hG R hR ρ q ?_ hbound
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rw [hinfinity, map_pow]
    exact congrArg (fun x : UniversalQuadratic.Q ↦ x.central)
      (UniversalQuadratic.infinitySquare_originalInitial (q c) hc)
  · change (q (ρ (UniversalQuadratic.oddIndex j))).central =
      UniversalQuadratic.originalInitial (UniversalQuadratic.oddIndex j)
    rw [htame, map_mul, map_mul, map_mul, map_inv, map_inv, map_pow]
    simpa only [UniversalQuadratic.tameWord] using
      congrArg (fun x : UniversalQuadratic.Q ↦ x.central)
      (UniversalQuadratic.tameWord_originalInitial j (q (inertia j)) (q (frobenius j))
        (hinertia j) (hfrobenius j))

end UnitDistance.OriginalRelatorGeneration
