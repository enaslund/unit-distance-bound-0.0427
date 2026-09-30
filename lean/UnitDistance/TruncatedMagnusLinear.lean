module

public import UnitDistance.TruncatedMagnusCertificates

@[expose] public section
set_option backward.privateInPublic true


/-! Linear consequences of the finite tensor certificates. The subgroup
used below remembers all actual cubic tails of the quadratic relators. -/
noncomputable section
open scoped BigOperators
namespace UnitDistance.TruncatedMagnus
variable {R : Type*} [CommRing R]

def bracketLinear : V₁ R →ₗ[R] V₂ R →ₗ[R] V₃ R where
  toFun x :=
    { toFun := bracket x
      map_add' y z := by ext i j k; simp [bracket]; ring
      map_smul' r y := by ext i j k; simp [bracket,smul_eq_mul]; ring }
  map_add' x y := by ext z i j k; simp [bracket]; ring
  map_smul' r x := by ext z i j k; simp [bracket,smul_eq_mul]; ring

@[simp] theorem bracketLinear_apply (x : V₁ R) (y : V₂ R) :
    bracketLinear x y=bracket x y := rfl

def coordinateCombination {n : ℕ} {W : Type*} [AddCommGroup W] [Module R W]
    (w : Fin n → W) : (Fin n → R) →ₗ[R] W where
  toFun v := ∑ i, v i • w i
  map_add' v u := by simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' r v := by
    simp only [Pi.smul_apply,smul_smul,Finset.smul_sum,RingHom.id_apply,smul_eq_mul]

@[simp] theorem coordinateCombination_single {n : ℕ} {W : Type*}
    [AddCommGroup W] [Module R W] (w : Fin n → W) (i : Fin n) :
    coordinateCombination w (Pi.single i (1 : R))=w i := by
  classical
  simp [coordinateCombination,Pi.single_apply]

namespace Certificate

def rowMap : A →ₗ[F] V₂ F := coordinateCombination quadraticRow

def selectedMap : U →ₗ[F] V₂ F := coordinateCombination selectedQuadratic

def baseMap : U →ₗ[F] V₁ F := coordinateCombination (fun i : Fin 6 => e i.succ)

@[simp] theorem rowMap_single (i : Fin 16) : rowMap (Pi.single i 1)=quadraticRow i :=
  coordinateCombination_single _ i
@[simp] theorem selectedMap_single (i : Fin 6) :
    selectedMap (Pi.single i 1)=selectedQuadratic i := coordinateCombination_single _ i
@[simp] theorem baseMap_single (i : Fin 6) :
    baseMap (Pi.single i 1)=e i.succ := coordinateCombination_single _ i

attribute [local irreducible] leftInverse secondDetector thirdDetector rowMap selectedMap baseMap

theorem leftInverse_rowMap (v : A) : leftInverse (rowMap v)=v := by
  have h : leftInverse.comp rowMap=LinearMap.id := by
    apply (Pi.basisFun F (Fin 16)).ext
    intro i
    simp only [Pi.basisFun_apply,LinearMap.comp_apply,LinearMap.id_apply,rowMap_single]
    exact funext (leftInverse_row_certificate i)
  exact congrArg (fun f : A →ₗ[F] A => f v) h

theorem secondDetector_rowMap (v : A) : secondDetector (rowMap v)=0 := by
  have h : secondDetector.comp rowMap=0 := by
    apply (Pi.basisFun F (Fin 16)).ext
    intro i
    simp only [Pi.basisFun_apply,LinearMap.comp_apply,LinearMap.zero_apply,rowMap_single]
    exact funext (second_row_certificate i)
  exact congrArg (fun f : A →ₗ[F] U => f v) h

theorem thirdDetector_bracket_rowMap (x : V₁ F) (v : A) :
    thirdDetector (bracket x (rowMap v))=0 := by
  have h (i : Fin 7) : thirdDetector.comp ((bracketLinear (e i)).comp rowMap)=0 := by
    apply (Pi.basisFun F (Fin 16)).ext
    intro j
    simp only [Pi.basisFun_apply,LinearMap.comp_apply,LinearMap.zero_apply,rowMap_single,
      bracketLinear_apply]
    exact funext (third_row_certificate j i)
  have h' : thirdDetector.comp (bracketLinear.flip (rowMap v))=0 := by
    apply (Pi.basisFun F (Fin 7)).ext
    intro i
    simpa only [Pi.basisFun_apply,LinearMap.comp_apply,LinearMap.flip_apply,
      LinearMap.zero_apply,bracketLinear_apply,e] using
      congrArg (fun f : A →ₗ[F] U => f v) (h i)
  exact congrArg (fun f : V₁ F →ₗ[F] U => f x) h'

theorem thirdDetector_bracket_selectedMap (v : U) :
    thirdDetector (bracket (e 0) (selectedMap v))=v := by
  have h : thirdDetector.comp ((bracketLinear (e 0)).comp selectedMap)=LinearMap.id := by
    apply (Pi.basisFun F (Fin 6)).ext
    intro i
    simp only [Pi.basisFun_apply,LinearMap.comp_apply,LinearMap.id_apply,selectedMap_single,
      bracketLinear_apply]
    exact funext (third_detect_certificate i)
  exact congrArg (fun f : U →ₗ[F] U => f v) h

def quadraticAdjoint : V₁ F →ₗ[F] V₂ F where
  toFun x := quadraticBracket (e 0) x
  map_add' x y := by ext i j; simp [quadraticBracket]; ring
  map_smul' r x := by ext i j; simp [quadraticBracket,smul_eq_mul]; ring

theorem secondDetector_bracket_baseMap (v : U) :
    secondDetector (quadraticBracket (e 0) (baseMap v))=v := by
  have h : secondDetector.comp (quadraticAdjoint.comp baseMap)=LinearMap.id := by
    apply (Pi.basisFun F (Fin 6)).ext
    intro i
    simp only [Pi.basisFun_apply,LinearMap.comp_apply,LinearMap.id_apply,baseMap_single]
    change secondDetector (quadraticBracket (e 0) (e i.succ))=Pi.single i 1
    exact funext (second_detect_certificate i)
  exact congrArg (fun f : U →ₗ[F] U => f v) h

/-- Each arbitrary actual cubic tail is retained in the defining condition. -/
def tailCorrection (tails : Fin 16 → V₃ F) : V₂ F →ₗ[F] U :=
  thirdDetector.comp ((coordinateCombination tails).comp leftInverse)

def cutSubgroup (tails : Fin 16 → V₃ F) : Subgroup (Group F) :=
  relationSubgroup (LinearMap.range rowMap) thirdDetector (tailCorrection tails)

instance cutSubgroup_normal (tails : Fin 16 → V₃ F) : (cutSubgroup tails).Normal :=
  relationSubgroup_normal _ _ _ (by
    intro x y hy
    obtain ⟨v,rfl⟩ := hy
    exact thirdDetector_bracket_rowMap x v)

/-- Every literal quadratic relator, including its unknown cubic tail, lies in the cut kernel. -/
theorem relator_mem_cutSubgroup (tails : Fin 16 → V₃ F) (i : Fin 16) :
    (⟨0,quadraticRow i,tails i⟩ : Group F)∈cutSubgroup tails := by
  apply relation_mem
  · exact ⟨Pi.single i 1,rowMap_single i⟩
  · change thirdDetector (tails i)=
      thirdDetector (coordinateCombination tails (leftInverse (quadraticRow i)))
    rw [show leftInverse (quadraticRow i)=Pi.single i 1 from
      funext (leftInverse_row_certificate i),coordinateCombination_single]

theorem dyadic_mem_cutSubgroup (tails : Fin 16 → V₃ F) :
    (⟨0,0,dyadicCubic⟩ : Group F)∈cutSubgroup tails := by
  apply (central_mem_relationSubgroup _ _ _ _).mpr
  exact funext third_dyadic_certificate

end Certificate
end UnitDistance.TruncatedMagnus
