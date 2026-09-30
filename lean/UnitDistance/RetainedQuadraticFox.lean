module

public import UnitDistance.GroupAugmentationRetainedQuadratic
public import UnitDistance.GroupAugmentationFoxCharacters
public import UnitDistance.GroupAugmentationGlobalBlocks

@[expose] public section
set_option backward.privateInPublic true


/-!
# The concrete retained quotient certifies global dyadic Fox coordinates

The explicit finite quadratic model has three literal genus-coordinate
characters dual to the dyadic generators. Any genuine ambient homomorphism
to this model compatible with the local dyadic map inherits both actual
layer injections and the explicit elementary left inverse. These are proved
consequences of an actual group diagram, not hypotheses about Hilbert costs.
-/

noncomputable section
namespace UnitDistance.RetainedQuadratic
open GroupAugmentation

/-- The three genus coordinates dual to the actual local dyadic generators. -/
def dyadicCharacterIndex : Fin 3 → Fin 7 := ![1,2,3]

def dyadicCharacter (k : Fin 3) : Q →* Multiplicative F where
  toFun q := Multiplicative.ofAdd (q.base (dyadicCharacterIndex k))
  map_one' := rfl
  map_mul' _ _ := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- Nine exact coordinate checks for the independently defined local map. -/
theorem dyadicCharacter_certificate : ∀ j k : Fin 3,
    (dyadicCharacter k (dyadicMap (Dyadic.Filtration.gen j))).toAdd =
      (Pi.single j (1 : F) : Fin 3 → F) k := by decide +kernel

variable (P : Type*) [Group P] (f : Dyadic.D →* P) (π : P →* Q)
variable (hdiagram : π.comp f = dyadicMap)

include hdiagram in
/-- Compatibility with the actual retained local map proves every ambient
augmentation-layer injection, by functoriality through the retained model. -/
theorem retained_dyadic_layer_injections (n : ℕ) :
    Function.Injective (layerMap F Dyadic.D f n) := by
  apply (layerMap_injective_iff F Dyadic.D f n).mpr
  intro g hg hfg
  have hπfg := map_dimensionSubgroup_le F P π (n+1) ⟨f g,hfg,rfl⟩
  have hq : dyadicMap g ∈ dimensionSubgroup F Q (n+1) := by
    simpa only [← hdiagram,MonoidHom.comp_apply] using hπfg
  exact (layerMap_injective_iff F Dyadic.D dyadicMap n).mp
    (dyadic_layer_injections Q dyadicMap dyadicMap_first_layer dyadicMap_second_layer n) g hg hq

variable {ι : Type*} [Fintype ι]
variable (generators : ι → P) (words : Fin 3 → FreeGroup ι)
variable (hwords : ∀ j, FreeGroup.lift generators (words j) = f (Dyadic.Filtration.gen j))

include hdiagram hwords in
/-- The retained genus characters explicitly certify the global Fox matrix
left inverse after augmentation. -/
theorem retained_characterFoxRetraction_left (j k : Fin 3) :
    augmentation F P
      (characterFoxRetraction P generators (fun k => (dyadicCharacter k).comp π)
        (foxSubstitutionAlgebra F P generators words (Pi.single j 1)) k) =
      augmentation F P ((Pi.single j (1 : A F P) : Fin 3 → A F P) k) := by
  apply characterFoxRetraction_left P generators words (fun k => (dyadicCharacter k).comp π)
  intro a b
  rw [hwords]
  change (dyadicCharacter b (π (f (Dyadic.Filtration.gen a)))).toAdd = _
  have he := DFunLike.congr_fun hdiagram (Dyadic.Filtration.gen a)
  rw [show π (f (Dyadic.Filtration.gen a)) = dyadicMap (Dyadic.Filtration.gen a) from he]
  exact dyadicCharacter_certificate a b

variable [Finite P] (hP : IsPGroup 2 P)

include hdiagram hwords hP in
/-- Retaining the actual finite quadratic model proves the exact global
common-row cost, including global coordinate strictness. -/
theorem retained_global_dyadic_row_cost
    (c : Fin 3 → Dyadic.AlgebraD)
    (hc : ∀ i, c i-Dyadic.AlgebraD.linearFoxCoefficients i ∈ Dyadic.AlgebraD.augmentationPower 2)
    (t : ℝ) (ht : 0 ≤ t) :
    FilteredHilbert.value F (ι → A F P)
      (fun n => globalDyadicRow P generators words f c ⊓ shiftedFoxCoefficientPower P n)
      (Nat.card P+1) t =
    t^2*(1-t^7/((1+t)^3*(1+t^2)^2))*
      Polynomial.eval₂ (Nat.castRingHom ℝ) t (hilbertPolynomial P) := by
  exact global_dyadic_row_cost P generators hP words f
    (retained_dyadic_layer_injections P f π hdiagram 1)
    (retained_dyadic_layer_injections P f π hdiagram 2)
    (characterFoxRetraction P generators (fun k => (dyadicCharacter k).comp π))
    (retained_characterFoxRetraction_left P f π hdiagram generators words hwords) c hc t ht

include hdiagram hwords hP in
/-- The full dyadic block also has its optimized upper cost as a proved
consequence of the actual retained diagram. -/
theorem retained_global_dyadic_block_cost (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    FilteredHilbert.value F (ι → A F P)
      (fun n => globalFoxBlock P generators words ⊓ shiftedFoxCoefficientPower P n)
      (Nat.card P+1) t ≤
    (3*t-1+1/((1+t)^3*(1+t^2)^2))*
      Polynomial.eval₂ (Nat.castRingHom ℝ) t (hilbertPolynomial P) := by
  exact global_dyadic_block_cost P generators hP words f hwords
    (retained_dyadic_layer_injections P f π hdiagram 1)
    (retained_dyadic_layer_injections P f π hdiagram 2) t ht0 ht1

end UnitDistance.RetainedQuadratic
