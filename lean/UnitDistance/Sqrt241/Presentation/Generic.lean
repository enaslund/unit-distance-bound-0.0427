module

public import UnitDistance.SpecifiedRelators
public import UnitDistance.ClassTwoCentralCharacters
public import UnitDistance.Upstream.Yamaguchi.SawinTotallyRealTowers.ProTwoFrattini

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Relators detected by initials in a bilinear class-two quotient (generic)

Generic form of `OriginalRelatorGeneration.closedNormalClosure_eq_of_original_images`
(ℚ package): the number `m` of generators, the number `n` of relators, the
bilinear law `β` and the dual functionals are parameters. If a continuous map
`q : G → GroupModel β` sends `n` relators to central elements whose central
coordinates (the *initials*) have a dual family of linear functionals, and
`dim H²(G/R) ≤ n`, then the relators normally generate `R`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Presentation

open ClassFieldTower.ProP ClassFieldTower.Cohomology
open ProCGroups ProCGroups.ProC ProCGroups.Presentations

variable {m : ℕ} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  (β : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) →ₗ[ZMod 2] W)
  [TopologicalSpace (ClassTwo.GroupModel β)] [DiscreteTopology (ClassTwo.GroupModel β)]

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A continuous elementary coordinate of a map into the class-two model. -/
def baseCharacter (q : G →ₜ* ClassTwo.GroupModel β) (i : Fin m) :
    G →ₜ* Multiplicative (ZMod 2) where
  toFun g := Multiplicative.ofAdd ((q g).base i)
  map_one' := by simp
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    change (q (g * h)).base i = (q g).base i + (q h).base i
    rw [map_mul, ClassTwo.GroupModel.mul_base]
    rfl
  continuous_toFun :=
    (continuous_of_discreteTopology : Continuous (fun x : ClassTwo.GroupModel β ↦
      Multiplicative.ofAdd (x.base i))).comp q.continuous_toFun

/-- The Frattini subgroup maps to central elements (zero base). -/
theorem base_eq_zero_of_mem_frattini (q : G →ₜ* ClassTwo.GroupModel β)
    (g : G) (hg : g ∈ closedPowerCommutator 2 G) : (q g).base = 0 := by
  funext i
  exact congrArg Multiplicative.toAdd
    (closedPowerCommutator_le_character_ker (baseCharacter β q i) hg)

/-- **Relators detected by initials.** Let `R ≤ Φ(G)` be a closed normal
subgroup of a pro-2 group `G`, `ρ : Fin n → R`, and `q : G →ₜ* GroupModel β`
such that the central coordinates `init i` of the `q (ρ i)` admit dual
functionals `ℓ i`. If `dim H²(G/R, ℤ/2) ≤ n`, the `ρ i` normally generate `R`. -/
theorem closedNormalClosure_eq_of_initials
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : HasPGroupOpenNormalBasis 2 G) (R : ClosedSubgroup G) [R.Normal]
    (hR : (R : Subgroup G) ≤ closedPowerCommutator 2 G)
    {n : ℕ} (ρ : Fin n → R) (q : G →ₜ* ClassTwo.GroupModel β)
    (ℓ : Fin n → W →ₗ[ZMod 2] ZMod 2) (init : Fin n → W)
    (himage : ∀ i, (q (ρ i)).central = init i)
    (hdual : ∀ i j, ℓ i (init j) = if i = j then 1 else 0)
    [FiniteDimensional (ZMod 2)
      (continuousCohomologyZModPLifted 2 (G ⧸ (R : Subgroup G)) 2)]
    (hbound : Module.finrank (ZMod 2)
      (continuousCohomologyZModPLifted 2 (G ⧸ (R : Subgroup G)) 2) ≤ n) :
    closedNormalClosure (Set.range (fun i ↦ (ρ i : G))) = (R : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbase (r : R) : (q r).base = 0 :=
    base_eq_zero_of_mem_frattini β q r (hR r.2)
  let χ (i : Fin n) : R →ₜ* Multiplicative (ZMod 2) :=
    ClassTwo.centralCharacter β q (R : Subgroup G) hbase (ℓ i)
  apply SpecifiedRelators.closedNormalClosure_eq_of_dual_characters hG R hR ρ χ
  · intro i g r
    exact ClassTwo.centralCharacter_conjNormal β q (R : Subgroup G) hbase (ℓ i) g r
  · intro i j
    change ℓ i (q (ρ j)).central = _
    rw [himage, hdual]
  · exact hbound

end UnitDistance.Sqrt241.Presentation
