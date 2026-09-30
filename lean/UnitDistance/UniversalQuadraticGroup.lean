module

public import UnitDistance.OriginalQuadraticRelations
public import Mathlib.Topology.Algebra.Group.Basic

@[expose] public section
set_option backward.privateInPublic true


/-!
# The universal seven-generator quadratic detector

An actual finite2-group on F₂⁷ × F₂²⁸ records the seven generator squares and
21 commutators in lexicographic order. It retains the six original relation
initials as independent central vectors; no arithmetic presentation is
assumed or assigned to this group.
-/
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace UnitDistance.UniversalQuadratic
open ClassTwo
abbrev F := ZMod 2
abbrev V := Fin 7 → F
abbrev W := Fin 28 → F

/-- Lower-triangular basis tensor: seven diagonal squares and21 brackets. -/
def cocycleMasks : Fin 7 → Fin 7 → ℕ :=
  ![![1,0,0,0,0,0,0],![128,2,0,0,0,0,0],![256,8192,4,0,0,0,0],
    ![512,16384,262144,8,0,0,0],![1024,32768,524288,4194304,16,0,0],
    ![2048,65536,1048576,8388608,33554432,32,0],
    ![4096,131072,2097152,16777216,67108864,134217728,64]]

def cocycle : V →ₗ[F] V →ₗ[F] W where
  toFun v :=
    { toFun := fun w => ∑ i, ∑ j, (v i*w j) • RetainedQuadratic.binaryVector 28 (cocycleMasks i j)
      map_add' w w' := by
        simp only [Pi.add_apply,mul_add,add_smul,Finset.sum_add_distrib]
      map_smul' r w := by
        simp only [Pi.smul_apply,smul_eq_mul,Finset.smul_sum,smul_smul]
        simp only [RingHom.id_apply,mul_left_comm] }
  map_add' v v' := by
    apply LinearMap.ext
    intro w
    change (∑ i, ∑ j, ((v i+v' i)*w j) • RetainedQuadratic.binaryVector 28 (cocycleMasks i j)) = _
    simp only [add_mul,add_smul,Finset.sum_add_distrib]
    rfl
  map_smul' r v := by
    apply LinearMap.ext
    intro w
    change (∑ i, ∑ j, ((r*v i)*w j) • RetainedQuadratic.binaryVector 28 (cocycleMasks i j)) =
      r • (∑ i, ∑ j, (v i*w j) • RetainedQuadratic.binaryVector 28 (cocycleMasks i j))
    simp only [Finset.smul_sum,smul_smul,mul_assoc]

abbrev Q := GroupModel cocycle

instance : TopologicalSpace Q := ⊥
instance : DiscreteTopology Q := ⟨rfl⟩
instance : IsTopologicalGroup Q := by infer_instance

theorem isTwoGroup : IsPGroup 2 Q := GroupModel.isTwoGroup cocycle

theorem card_Q : Nat.card Q=2^35 := by
  rw [Nat.card_congr (GroupModel.equivProd cocycle),Nat.card_prod]
  simp only [V,W,Nat.card_fun,Nat.card_fin,Nat.card_zmod]
  norm_num

def lift (v : V) : Q := ⟨v,0⟩
def generator (i : Fin 7) : Q := lift (Pi.single i 1)
def squareVector (v : V) : W := cocycle v v
def bracketVector (v w : V) : W := cocycle v w-cocycle w v

theorem lift_square (v : V) : (lift v)^2=(⟨0,squareVector v⟩ : Q) :=
  GroupModel.square_coordinates cocycle (lift v)

theorem lift_commutator (v w : V) :
    (lift v)⁻¹*(lift w)⁻¹*lift v*lift w=(⟨0,bracketVector v w⟩ : Q) :=
  GroupModel.commutator_coordinates cocycle (lift v) (lift w)

/-- Infinity first, then inertia at3,5,7,11,13. -/
def inertiaVectors : Fin 6 → V :=
  fun i => RetainedQuadratic.binaryVector 7 (![1,4,8,16,32,64] i)

/-- The five displayed odd Frobenius vectors; infinity uses the zero vector. -/
def frobeniusVectors : Fin 6 → V :=
  fun i => RetainedQuadratic.binaryVector 7 (![0,43,86,77,83,58] i)

def squareCoefficients : Fin 6 → F := ![1,1,0,1,1,0]

/-- The actual square/bracket expressions from the six proposed relator initials. -/
def originalInitial (i : Fin 6) : W :=
  bracketVector (inertiaVectors i) (frobeniusVectors i) +
    squareCoefficients i • squareVector (inertiaVectors i)

/-- Exact compatibility with the six independently checked manuscript rows. -/
theorem originalInitial_certificate : ∀ i : Fin 6, ∀ k : Fin 28,
    originalInitial i k=OriginalQuadratic.relationVector i k := by
  decide +kernel

theorem originalInitial_eq (i : Fin 6) : originalInitial i=OriginalQuadratic.relationVector i :=
  funext (originalInitial_certificate i)

/-- The six displayed initial forms have an actual identity matrix of linear detectors. -/
theorem original_coordinate (i j : Fin 6) :
    OriginalQuadratic.coordinate i (originalInitial j)=if i=j then 1 else 0 := by
  rw [originalInitial_eq,OriginalQuadratic.coordinate_relation]

end UnitDistance.UniversalQuadratic
