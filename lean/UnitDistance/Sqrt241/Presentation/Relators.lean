module

public import UnitDistance.Sqrt241.Generators.Source
public import UnitDistance.Sqrt241.Presentation.Generic
public import UnitDistance.Sqrt241.Presentation.GenuineRelation
public import UnitDistance.Sqrt241.Cut.Basic

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# The seven relators of the presentation of `G_B`

For lifts `A : Cut.SourceLifts` to the free source `F(8)` of the local
generators (complex conjugations, tame pairs, dyadic local maps, caps) with the
elementary labels `A.Labels`, the seven relators
`A.relators r` (`c₁², c₂²`, the tame words at `𝔮₁, 𝔮₂, 𝔯₁, 𝔯₂`, the lifted
genuine relation at `𝔭₂`) have universal quadratic initials
`Universal.initial` (`relators_central`), and they lie in the relation kernel
of `freeMap : F(8) → G_B` as soon as their images in `G_B` are trivial
(`relators_mem`).

The elementary coordinate of every continuous map from `F(8)` to a class-two
model sending generators to `(eᵢ, _)` is the genus label of the image in
`G_B` (`detector_base`, `retainedFree_base`).
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Presentation

open Tower GroupData ClassTwo ProCGroups ProCGroups.ProC ClassFieldTower.ProP

/-- The free pro-2 group on the eight generators. -/
abbrev Free : Type := FiniteFreeProTwo.Carrier 8

/-- The universal quadratic detector of the free source. -/
def detector : Free →ₜ* Universal.Q := Universal.freeDetector (FiniteFreeProTwo.isFree 8)

theorem labelGroup_hasPGroupOpenNormalBasis :
    HasPGroupOpenNormalBasis 2 (Multiplicative (Fin 8 → ZMod 2)) := by
  have htwo : IsPGroup 2 (Multiplicative (Fin 8 → ZMod 2)) := IsPGroup.of_card card_labelGroup
  exact HasOpenNormalBasisInClass.of_finite_discrete
    (FiniteGroupClass.pGroup_formation 2).quotientClosed ⟨inferInstance, htwo⟩

/-- A continuous map `F(8) → F₂⁸` sending generator `i` to `eᵢ` is the genus
label of `freeMap`. -/
theorem eq_label_of_generator (f : Free →* Multiplicative (Fin 8 → ZMod 2)) (hf : Continuous f)
    (hgen : ∀ i, f (FiniteFreeProTwo.generator 8 i) = Multiplicative.ofAdd (Pi.single i 1))
    (g : Free) : f g = genusLabel (freeMap g) := by
  have h := (FiniteFreeProTwo.isFree 8).hom_ext labelGroup_hasPGroupOpenNormalBasis
    (f := f) (g := (genusLabel.comp freeMap).toMonoidHom) hf (genusLabel.comp freeMap).continuous
    (by
      intro i
      change f (FiniteFreeProTwo.generator 8 i) = genusLabel (freeMap (FiniteFreeProTwo.generator 8 i))
      rw [hgen, freeMap_generator_label])
  exact congrArg (fun φ : Free →* Multiplicative (Fin 8 → ZMod 2) ↦ φ g) h

theorem detector_base (g : Free) : (detector g).base = (genusLabel (freeMap g)).toAdd := by
  have h := eq_label_of_generator
    ((GroupModel.baseHom Universal.cocycle).comp detector.toMonoidHom)
    ((continuous_of_discreteTopology : Continuous
      (GroupModel.baseHom Universal.cocycle)).comp detector.continuous_toFun)
    (fun i ↦ by
      change Multiplicative.ofAdd (detector (FiniteFreeProTwo.generator 8 i)).base = _
      rw [detector, Universal.freeDetector_generator_base]) g
  exact congrArg Multiplicative.toAdd h

theorem retainedFree_base (g : Free) :
    (Cut.retainedFree g).base = (genusLabel (freeMap g)).toAdd := by
  have h := eq_label_of_generator
    ((GroupModel.baseHom Retained.cocycle).comp Cut.retainedFree.toMonoidHom)
    ((continuous_of_discreteTopology : Continuous
      (GroupModel.baseHom Retained.cocycle)).comp Cut.retainedFree.continuous_toFun)
    (fun i ↦ by
      change Multiplicative.ofAdd (Cut.retainedFree (FiniteFreeProTwo.generator 8 i)).base = _
      rw [Cut.retainedFree_generator]) g
  exact congrArg Multiplicative.toAdd h

theorem detector_base_eq_retainedFree_base (g : Free) :
    (detector g).base = (Cut.retainedFree g).base := by
  rw [detector_base, retainedFree_base]

/-! ### Initials of the seven relators -/

section Initials

variable (A : Cut.SourceLifts) (hL : A.Labels)

include hL in
theorem detector_conj_base (k : Fin 2) : (detector (A.conj k)).base = conjVector k := by
  rw [detector_base_eq_retainedFree_base]
  exact hL.conj k

include hL in
theorem detector_tameInertia_base (q : Fin 4) :
    (detector (A.tameInertia q)).base = tameInertiaVector q := by
  rw [detector_base_eq_retainedFree_base]
  exact hL.tameInertia q

include hL in
theorem detector_tameFrobenius_base (q : Fin 4) :
    (detector (A.tameFrobenius q)).base = tameFrobeniusVector q := by
  rw [detector_base_eq_retainedFree_base]
  exact hL.tameFrobenius q

theorem sub_eq_add_W (v w : Universal.W) : v - w = v + w := GroupData.sub_eq_add v w

include hL in
/-- The dyadic generators `a, b, c` of `𝔭_P` have labels `y, x, z - y`. -/
theorem detector_dyadic_bases (P : Fin 2) :
    (detector (A.dyadic P (FiniteFreeProTwo.generator 3 0))).base = dyadicYVector P ∧
    (detector (A.dyadic P (FiniteFreeProTwo.generator 3 1))).base = dyadicXVector P ∧
    (detector (A.dyadic P (FiniteFreeProTwo.generator 3 2))).base =
      dyadicZVector P - dyadicYVector P := by
  have hy : (detector (A.dyadic P (FiniteFreeProTwo.generator 3 0))).base = dyadicYVector P := by
    rw [detector_base_eq_retainedFree_base]
    exact hL.dyadicY P
  refine ⟨hy, ?_, ?_⟩
  · rw [detector_base_eq_retainedFree_base]
    exact hL.dyadicX P
  · have hz : (detector (A.dyadic P (FiniteFreeProTwo.generator 3 0 *
        FiniteFreeProTwo.generator 3 2))).base = dyadicZVector P := by
      rw [detector_base_eq_retainedFree_base]
      exact hL.dyadicZ P
    rw [map_mul, map_mul, GroupModel.mul_base, hy] at hz
    rw [← hz]
    abel

include hL in
theorem detector_conj_sq (k : Fin 2) :
    (detector (A.conj k ^ 2)).central = Universal.squareVector (conjVector k) := by
  rw [map_pow, GroupModel.square_coordinates, detector_conj_base A hL]
  rfl

include hL in
theorem detector_tameWord (q : Fin 4) :
    (detector (Lifts.tameWord (tameNorm q) (A.tameInertia q) (A.tameFrobenius q))).central =
      Universal.tameInitial q := by
  have hmap := Lifts.map_tameWord detector.toMonoidHom (tameNorm q) (A.tameInertia q)
    (A.tameFrobenius q)
  have hword := ClassTwo.Tame.word_odd Universal.cocycle (tameNorm q) (Retained.tameNorm_odd q)
    (detector (A.tameInertia q)) (detector (A.tameFrobenius q))
  change (detector.toMonoidHom (Lifts.tameWord (tameNorm q) (A.tameInertia q)
    (A.tameFrobenius q))).central = _
  rw [hmap]
  change (ClassTwo.Tame.word Universal.cocycle (tameNorm q) (detector (A.tameInertia q))
    (detector (A.tameFrobenius q))).central = _
  rw [hword]
  change Universal.cocycle (detector (A.tameInertia q)).base (detector (A.tameFrobenius q)).base -
      Universal.cocycle (detector (A.tameFrobenius q)).base (detector (A.tameInertia q)).base +
      (if tameNorm q % 4 = 3 then 1 else 0 : ZMod 2) •
        Universal.cocycle (detector (A.tameInertia q)).base (detector (A.tameInertia q)).base = _
  rw [detector_tameInertia_base A hL, detector_tameFrobenius_base A hL]
  rfl

include hL in
theorem detector_dyadic_relation (r : Cut.LocalSource)
    (hr : Dyadic.ArithmeticPresentation.detector r = FreeThreeQuadratic.relation) (P : Fin 2) :
    (detector (A.dyadic P r)).central = Universal.dyadicInitial P := by
  have h := genuineRelation_image Universal.cocycle Universal.hasPGroupOpenNormalBasis
    (detector.comp (A.dyadic P)) r hr
  obtain ⟨ha, hb, hc⟩ := detector_dyadic_bases A hL P
  change ((detector.comp (A.dyadic P)) r).central = _
  rw [h]
  change Universal.cocycle (detector (A.dyadic P (FiniteFreeProTwo.generator 3 0))).base
      (detector (A.dyadic P (FiniteFreeProTwo.generator 3 0))).base +
      (Universal.cocycle (detector (A.dyadic P (FiniteFreeProTwo.generator 3 1))).base
        (detector (A.dyadic P (FiniteFreeProTwo.generator 3 2))).base -
      Universal.cocycle (detector (A.dyadic P (FiniteFreeProTwo.generator 3 2))).base
        (detector (A.dyadic P (FiniteFreeProTwo.generator 3 1))).base) = _
  rw [ha, hb, hc]
  simp only [Universal.dyadicInitial, Universal.squareVector, Universal.bracketVector, map_sub,
    LinearMap.sub_apply, sub_eq_add_W]
  abel

include hL in
/-- The universal initials of the seven relators. -/
theorem relators_central (r : Cut.LocalSource)
    (hr : Dyadic.ArithmeticPresentation.detector r = FreeThreeQuadratic.relation) (i : Fin 7) :
    (detector (A.relators r i)).central = Universal.initial i := by
  fin_cases i
  · exact detector_conj_sq A hL 0
  · exact detector_conj_sq A hL 1
  · exact detector_tameWord A hL 0
  · exact detector_tameWord A hL 1
  · exact detector_tameWord A hL 2
  · exact detector_tameWord A hL 3
  · exact detector_dyadic_relation A hL r hr 1

end Initials

end UnitDistance.Sqrt241.Presentation
