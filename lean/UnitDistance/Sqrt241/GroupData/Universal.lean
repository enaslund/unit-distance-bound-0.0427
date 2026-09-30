module

public import UnitDistance.Sqrt241.GroupData.Basic
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.FreeProC.Basic
public import Mathlib.Topology.Algebra.Group.Basic

@[expose] public section
set_option backward.privateInPublic true


/-!
# The universal class-two detector on eight generators

The finite 2-group `F₂⁸ × F₂³⁶` with the lower-triangular basis law records
the eight generator squares and the 28 commutators (lexicographic order).
It is the `B`-analogue of `UniversalQuadratic.Q` (seven generators over `ℚ`).
Its central coordinates of the seven presentation relator initials
(`c₁², c₂²`, the four tame relations, the genuine dyadic relation at
`𝔭₂`) are computed from the elementary vectors of construction.md §3.4 and
have an explicit dual matrix. No arithmetic presentation is assumed here.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.Sqrt241.Universal
open ClassTwo GroupData

abbrev W := Fin 36 → F

/-- Lower-triangular universal law: eight squares and 28 brackets. -/
def cocycle : V →ₗ[F] V →ₗ[F] W := bilinearOfMasks 8 36 universalCocycleMasks

abbrev Q := GroupModel cocycle

instance : Group Q := inferInstanceAs (Group (GroupModel cocycle))

instance : TopologicalSpace Q := ⊥
instance : DiscreteTopology Q := ⟨rfl⟩
instance : IsTopologicalGroup Q := by infer_instance

theorem isTwoGroup : IsPGroup 2 Q := GroupModel.isTwoGroup cocycle

theorem card_Q : Nat.card Q = 2^44 := by
  rw [Nat.card_congr (GroupModel.equivProd cocycle),Nat.card_prod]
  simp only [V,W,Nat.card_fun,Nat.card_fin,Nat.card_zmod]
  norm_num

def lift (v : V) : Q := ⟨v,0⟩
def generator (i : Fin 8) : Q := lift (Pi.single i 1)
def squareVector (v : V) : W := cocycle v v
def bracketVector (v w : V) : W := cocycle v w-cocycle w v

theorem lift_square (v : V) : (lift v)^2 = (⟨0,squareVector v⟩ : Q) :=
  GroupModel.square_coordinates cocycle (lift v)

theorem lift_commutator (v w : V) :
    (lift v)⁻¹*(lift w)⁻¹*lift v*lift w = (⟨0,bracketVector v w⟩ : Q) :=
  GroupModel.commutator_coordinates cocycle (lift v) (lift w)

/-- Initial of the tame relation `φτφ⁻¹τ^{-N}` of norm `N`. -/
def tameInitial (q : Fin 4) : W :=
  bracketVector (tameInertiaVector q) (tameFrobeniusVector q) +
    (if tameNorm q % 4 = 3 then 1 else 0 : F) • squareVector (tameInertiaVector q)

/-- Initial `S(y) + B(x,y) + B(x,z)` of the genuine dyadic relation at `𝔭_P`. -/
def dyadicInitial (P : Fin 2) : W :=
  squareVector (dyadicYVector P) + bracketVector (dyadicXVector P) (dyadicYVector P) +
    bracketVector (dyadicXVector P) (dyadicZVector P)

/-- The seven presentation relator initials: `c₁², c₂²`, the tame relations at
`𝔮₁, 𝔮₂, 𝔯₁, 𝔯₂` and the genuine relation at `𝔭₂`. -/
def initial : Fin 7 → W :=
  ![squareVector (conjVector 0),squareVector (conjVector 1),tameInitial 0,tameInitial 1,
    tameInitial 2,tameInitial 3,dyadicInitial 1]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem initial_certificate : ∀ (i : Fin 7) (k : Fin 36),
    initial i k = bits 36 (relatorInitialMasks i) k := by
  -- one initial at a time, so that every kernel reduction stays small
  intro i
  fin_cases i <;> decide +kernel

theorem initial_eq (i : Fin 7) : initial i = bits 36 (relatorInitialMasks i) :=
  funext (initial_certificate i)

/-- Explicit dual functionals of the seven initials. -/
def coordinate (i : Fin 7) : W →ₗ[F] F := maskFunctional 36 (relatorCoordinateMasks i)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
theorem coordinate_masks_certificate : ∀ i j : Fin 7,
    coordinate i (bits 36 (relatorInitialMasks j)) = if i = j then 1 else 0 := by
  decide +kernel

theorem coordinate_initial (i j : Fin 7) :
    coordinate i (initial j) = if i = j then 1 else 0 := by
  rw [initial_eq]
  exact coordinate_masks_certificate i j

/-- The genuine relation at `𝔭₁` has initial the sum of the seven initials. -/
theorem dyadicInitial_zero_certificate : ∀ k : Fin 36,
    dyadicInitial 0 k = (∑ i, initial i) k := by
  decide +kernel

open ProCGroups ProCGroups.ProC ProCGroups.FreeProC

theorem hasPGroupOpenNormalBasis : HasPGroupOpenNormalBasis 2 Q := by
  apply HasOpenNormalBasisInClass.of_allOpenNormalQuotients
  intro U
  exact ⟨inferInstance,isTwoGroup.of_surjective (QuotientGroup.mk' (U : Subgroup Q))
    (QuotientGroup.mk'_surjective (U : Subgroup Q))⟩

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] {x : Fin 8 → G}

/-- The continuous detector given by the free universal property. -/
def freeDetector (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x) : G →ₜ* Q :=
  hfree.liftHom hasPGroupOpenNormalBasis generator continuous_of_discreteTopology

@[simp] theorem freeDetector_generator
    (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x) (i : Fin 8) :
    freeDetector hfree (x i) = generator i :=
  hfree.liftHom_apply hasPGroupOpenNormalBasis generator continuous_of_discreteTopology i

@[simp] theorem freeDetector_generator_base
    (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x) (i : Fin 8) :
    (freeDetector hfree (x i)).base = Pi.single i 1 := by
  rw [freeDetector_generator]
  rfl

end UnitDistance.Sqrt241.Universal
