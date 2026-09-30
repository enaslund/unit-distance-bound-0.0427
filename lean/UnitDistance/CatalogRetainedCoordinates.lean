module

public import UnitDistance.CatalogSquareclassData
public import UnitDistance.GroupAugmentationRetainedQuadraticRelations

@[expose] public section
set_option backward.privateInPublic true


/-! The independent catalog forms give an invertible coordinate system on
the retained model's twelve actual central coordinates. All matrix entries
are checked against the catalog form evaluations. -/
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
namespace UnitDistance.CatalogRetainedCoordinates
open RetainedQuadratic
abbrev F := ZMod 2
abbrev W := Fin 12 → F

def columns : Fin 12 → ℕ :=
  ![528,716,1594,313,998,2965,648,24,872,262,260,136]

def inverseColumns : Fin 12 → ℕ :=
  ![3675,1536,3856,2241,2113,1475,3922,193,2832,2112,2823,2747]

/-- From the model's central coordinates to the twelve actual root signs. -/
def toSigns : W →ₗ[F] W := binaryMatrixMap 12 12 columns

def fromSigns : W →ₗ[F] W := binaryMatrixMap 12 12 inverseColumns

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem inverse_certificate : ∀ (i j : Fin 12),
    fromSigns (toSigns (Pi.single i 1)) j=(Pi.single i (1 : F) : W) j := by decide +kernel

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem reverse_certificate : ∀ (i j : Fin 12),
    toSigns (fromSigns (Pi.single i 1)) j=(Pi.single i (1 : F) : W) j := by decide +kernel

attribute [local irreducible] toSigns fromSigns

theorem fromSigns_leftInverse : Function.LeftInverse fromSigns toSigns := by
  have h : fromSigns.comp toSigns=LinearMap.id := by
    apply (Pi.basisFun F (Fin 12)).ext
    intro i
    simpa only [Pi.basisFun_apply,LinearMap.comp_apply,LinearMap.id_apply]
      using funext (inverse_certificate i)
  intro v
  exact congrArg (fun f : W →ₗ[F] W => f v) h

theorem toSigns_leftInverse : Function.LeftInverse toSigns fromSigns := by
  have h : toSigns.comp fromSigns=LinearMap.id := by
    apply (Pi.basisFun F (Fin 12)).ext
    intro i
    simpa only [Pi.basisFun_apply,LinearMap.comp_apply,LinearMap.id_apply]
      using funext (reverse_certificate i)
  intro v
  exact congrArg (fun f : W →ₗ[F] W => f v) h

def signEquiv : W ≃ₗ[F] W := LinearEquiv.ofLinear toSigns fromSigns
  (by apply LinearMap.ext; intro v; exact toSigns_leftInverse v)
  (by apply LinearMap.ext; intro v; exact fromSigns_leftInverse v)

/-- The root character on a genus basis vector is its independently specified bit. -/
theorem character_single (m : ℕ) (i : Fin 7) :
    CatalogSquareclassData.character m (Pi.single i 1)=if m.testBit i.val then 1 else 0 := by
  unfold CatalogSquareclassData.character
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [hji]
  · simp

theorem character_add (m : ℕ) (v w : Fin 7 → F) :
    CatalogSquareclassData.character m (v+w)=
      CatalogSquareclassData.character m v+CatalogSquareclassData.character m w := by
  simp only [CatalogSquareclassData.character,Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  split <;> simp

/-- Pair evaluation reduces to four independently specified catalog bits. -/
theorem character_two_singles (m : ℕ) (i j : Fin 7) :
    CatalogSquareclassData.character m (Pi.single i 1+Pi.single j 1)=
      (if m.testBit i.val then 1 else 0)+(if m.testBit j.val then 1 else 0) := by
  rw [character_add,character_single,character_single]

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 100000 in
/-- Every actual catalog polar coefficient is the image of the model's
central commutator coefficient. -/
theorem cocycle_polar_certificate (i j : Fin 7) (k : Fin 12) :
    toSigns (RetainedQuadratic.cocycle (Pi.single i 1) (Pi.single j 1)+
      RetainedQuadratic.cocycle (Pi.single j 1) (Pi.single i 1)) k =
      CatalogSquareclassData.wordForm (CatalogSquareclassData.retainedWords k)
        (Pi.single i 1+Pi.single j 1) := by
  simp only [CatalogSquareclassData.wordForm,CatalogSquareclassData.catalogForm,
    character_two_singles]
  have h : ∀ (i j : Fin 7) (k : Fin 12),
      toSigns (RetainedQuadratic.cocycle (Pi.single i 1) (Pi.single j 1)+
        RetainedQuadratic.cocycle (Pi.single j 1) (Pi.single i 1)) k =
      ∑ t : Fin 17, if (CatalogSquareclassData.retainedWords k).testBit t.val then
        (((if (CatalogSquareclassData.masksA t).testBit i.val then 1 else 0)+
          (if (CatalogSquareclassData.masksA t).testBit j.val then 1 else 0))*
         ((if (CatalogSquareclassData.masksB t).testBit i.val then 1 else 0)+
          (if (CatalogSquareclassData.masksB t).testBit j.val then 1 else 0))) else 0 := by
    decide +kernel
  exact h i j k

end UnitDistance.CatalogRetainedCoordinates
