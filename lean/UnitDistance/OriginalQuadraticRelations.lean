module

public import UnitDistance.GroupAugmentationRetainedQuadraticRelations

@[expose] public section
set_option backward.privateInPublic true


/-! Independent quadratic coordinates of the actual six proposed original
relation initials. Their arithmetic identification with tame relators and
complex conjugation remains separate from these exact finite identities. -/
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace UnitDistance.OriginalQuadratic
abbrev F := ZMod 2
abbrev V := Fin 28 → F

def originalIndex (i : Fin 6) : Fin 16 := ⟨i.val,by omega⟩

/-- Infinity square, then tame relations at3,5,7,11,13. -/
def relationVector (i : Fin 6) : V := RetainedQuadratic.relationVector (originalIndex i)

/-- The first six actual dual coordinates of the checked elimination map. -/
def coordinate (i : Fin 6) : V →ₗ[F] F where
  toFun v := RetainedQuadratic.relationCoefficients v (originalIndex i)
  map_add' v w := by simp
  map_smul' r v := by simp

/-- A complete exact identity evaluation matrix for these six finite rows. -/
theorem coordinate_relation : ∀ i j : Fin 6,
    coordinate i (relationVector j) = if i=j then 1 else 0 := by
  decide +kernel

/-- Linear expansion in the six original relation vectors. -/
def expansion : (Fin 6 → F) →ₗ[F] V where
  toFun v := ∑ i, v i • relationVector i
  map_add' v w := by simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' r v := by
    simp only [Pi.smul_apply,Finset.smul_sum,smul_smul,smul_eq_mul,RingHom.id_apply]

def coordinates : V →ₗ[F] (Fin 6 → F) where
  toFun v i := coordinate i v
  map_add' v w := by ext i; simp
  map_smul' r v := by ext i; simp

/-- The explicit finite dual coordinates are a left inverse. -/
theorem coordinates_expansion (v : Fin 6 → F) : coordinates (expansion v)=v := by
  funext i
  change coordinate i (∑ j, v j • relationVector j)=v i
  simp [coordinate_relation]

/-- The six displayed original quadratic rows are genuinely independent. -/
theorem expansion_injective : Function.Injective expansion :=
  Function.LeftInverse.injective coordinates_expansion

end UnitDistance.OriginalQuadratic
