module

public import UnitDistance.Sqrt241.Presentation.Generation

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# From the local elements of `G_B` to lifts on the free source

`LocalElements` collects the local elements of `G_B` constructed in `Local/`:
the complex conjugations `c₁, c₂`, the tame pairs at `𝔮₁, 𝔮₂, 𝔯₁, 𝔯₂`, the two
dyadic local maps `Gal(ℚ₂(2)/ℚ₂) → G_B` and the three cap elements
(`Frob 29₁`, `Frob 29₂`, `F₇²`). `LocalElements.Relations` (involutions, tame
relations) and `LocalElements.Labels` (genus labels of construction.md §3.4)
are the facts proved about them in `Local/Elements.lean`.

`LocalElements.sourceLifts` lifts them to `F(8)` (as a `Cut.SourceLifts`),
with the dyadic maps extended from the three local generators by the free
universal property. The genuine local relation `genuineRelation`
(`PadicTwoQuadraticRelation.exists_actual_quadratic_relation`) then gives:

* `LocalElements.sourceLifts_labels : (E.sourceLifts).Labels`,
* `LocalElements.relatorsTrivial : RelatorsTrivial E.sourceLifts genuineRelation`,
* `LocalElements.presentation : (E.sourceLifts).Presentation genuineRelation`,
* `LocalElements.relators_generate`: the seven relators normally generate the
  relation kernel.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Presentation

open Tower GroupData ClassTwo ProCGroups ProCGroups.ProC ProCGroups.Presentations
open ClassFieldTower.ProP

/-! ### The genuine local relation -/

/-- The minimal presentation `F(3) → Gal(ℚ₂(2)/ℚ₂)`, generators `↦`
`PadicTwoQuadraticRelation.generator`. -/
def localPresentation : Cut.LocalSource →ₜ* PadicTwoMaximalProTwo.Group :=
  Classical.choose PadicTwoQuadraticRelation.exists_actual_quadratic_relation

theorem localPresentation_generator (i : Fin 3) :
    localPresentation (FiniteFreeProTwo.generator 3 i) = PadicTwoQuadraticRelation.generator i :=
  (Classical.choose_spec PadicTwoQuadraticRelation.exists_actual_quadratic_relation).2.2.1 i

/-- The genuine relation of `Gal(ℚ₂(2)/ℚ₂)` with universal quadratic image `a²[b,c]`. -/
def genuineRelation : Cut.LocalSource :=
  Classical.choose (Classical.choose_spec
    PadicTwoQuadraticRelation.exists_actual_quadratic_relation).2.2.2

theorem localPresentation_genuineRelation : localPresentation genuineRelation = 1 :=
  (Classical.choose_spec (Classical.choose_spec
    PadicTwoQuadraticRelation.exists_actual_quadratic_relation).2.2.2).1

theorem detector_genuineRelation :
    Dyadic.ArithmeticPresentation.detector genuineRelation = FreeThreeQuadratic.relation :=
  (Classical.choose_spec (Classical.choose_spec
    PadicTwoQuadraticRelation.exists_actual_quadratic_relation).2.2.2).2

/-! ### Local elements -/

/-- The local elements of `G_B` used by the presentation and the cut (constructed in `Local/`). -/
structure LocalElements where
  conj : Fin 2 → GB
  tameInertia : Fin 4 → GB
  tameFrobenius : Fin 4 → GB
  dyadic : Fin 2 → (PadicTwoMaximalProTwo.Group →ₜ* GB)
  cap : Fin 3 → GB

namespace LocalElements

variable (E : LocalElements)

/-- The group relations of the local elements. -/
structure Relations : Prop where
  conj_sq : ∀ k, E.conj k ^ 2 = 1
  tame : ∀ q, E.tameFrobenius q * E.tameInertia q * (E.tameFrobenius q)⁻¹ =
    E.tameInertia q ^ tameNorm q

/-- The genus labels of the local elements (construction.md §3.4); the dyadic
generators `a, b, c` are the classes of `-1, 5, 2`. -/
structure Labels : Prop where
  conj : ∀ k, genusLabel (E.conj k) = Multiplicative.ofAdd (conjVector k)
  tameInertia : ∀ q, genusLabel (E.tameInertia q) = Multiplicative.ofAdd (tameInertiaVector q)
  tameFrobenius : ∀ q,
    genusLabel (E.tameFrobenius q) = Multiplicative.ofAdd (tameFrobeniusVector q)
  dyadicA : ∀ P, genusLabel (E.dyadic P (PadicTwoQuadraticRelation.generator 0)) =
    Multiplicative.ofAdd (dyadicAVector P)
  dyadicB : ∀ P, genusLabel (E.dyadic P (PadicTwoQuadraticRelation.generator 1)) =
    Multiplicative.ofAdd (dyadicBVector P)
  dyadicC : ∀ P, genusLabel (E.dyadic P (PadicTwoQuadraticRelation.generator 2)) =
    Multiplicative.ofAdd (dyadicCVector P)
  cap : ∀ k, CapGood (genusLabel (E.cap k)).toAdd

/-- A fixed preimage in `F(8)` of an element of `G_B`. -/
def lift (g : GB) : Free := Function.surjInv freeMap_surjective g

theorem freeMap_lift (g : GB) : freeMap (lift g) = g :=
  Function.surjInv_eq freeMap_surjective g

/-- The dyadic map at `𝔭_P` on the free source: local generator `i ↦` a lift of
its image in `G_B`. -/
def dyadicLift (P : Fin 2) : Cut.LocalSource →ₜ* Free :=
  (FiniteFreeProTwo.isFree 3).liftHom (FiniteFreeProTwo.isFree 8).hasOpenNormalBasisInClass
    (fun i ↦ lift (E.dyadic P (PadicTwoQuadraticRelation.generator i)))
    continuous_of_discreteTopology

theorem dyadicLift_generator (P : Fin 2) (i : Fin 3) :
    E.dyadicLift P (FiniteFreeProTwo.generator 3 i) =
      lift (E.dyadic P (PadicTwoQuadraticRelation.generator i)) :=
  (FiniteFreeProTwo.isFree 3).liftHom_apply (FiniteFreeProTwo.isFree 8).hasOpenNormalBasisInClass
    _ continuous_of_discreteTopology i

/-- The dyadic lift covers the dyadic local map. -/
theorem freeMap_dyadicLift (P : Fin 2) (s : Cut.LocalSource) :
    freeMap (E.dyadicLift P s) = E.dyadic P (localPresentation s) := by
  have h := (FiniteFreeProTwo.isFree 3).hom_ext GB_hasPGroupOpenNormalBasis
    (f := (freeMap.comp (E.dyadicLift P)).toMonoidHom)
    (g := ((E.dyadic P).comp localPresentation).toMonoidHom)
    (freeMap.comp (E.dyadicLift P)).continuous_toFun
    ((E.dyadic P).comp localPresentation).continuous_toFun (by
      intro i
      change freeMap (E.dyadicLift P (FiniteFreeProTwo.generator 3 i)) =
        E.dyadic P (localPresentation (FiniteFreeProTwo.generator 3 i))
      rw [dyadicLift_generator, freeMap_lift, localPresentation_generator])
  exact congrArg (fun f : Cut.LocalSource →* GB ↦ f s) h

/-- The lifts of the local elements to the free source, as a `Cut.SourceLifts`. -/
def sourceLifts : Cut.SourceLifts where
  conj k := lift (E.conj k)
  tameInertia q := lift (E.tameInertia q)
  tameFrobenius q := lift (E.tameFrobenius q)
  dyadic P := E.dyadicLift P
  cap k := lift (E.cap k)

theorem retainedFree_base_lift (g : GB) :
    (Cut.retainedFree (lift g)).base = (genusLabel g).toAdd := by
  rw [retainedFree_base, freeMap_lift]

variable {E}

theorem sourceLifts_labels (hL : E.Labels) : E.sourceLifts.Labels := by
  refine ⟨fun k ↦ ?_, fun q ↦ ?_, fun q ↦ ?_, fun P ↦ ?_, fun P ↦ ?_, fun P ↦ ?_, fun k ↦ ?_⟩
  · change (Cut.retainedFree (lift (E.conj k))).base = _
    rw [retainedFree_base_lift, hL.conj]
    rfl
  · change (Cut.retainedFree (lift (E.tameInertia q))).base = _
    rw [retainedFree_base_lift, hL.tameInertia]
    rfl
  · change (Cut.retainedFree (lift (E.tameFrobenius q))).base = _
    rw [retainedFree_base_lift, hL.tameFrobenius]
    rfl
  · change (Cut.retainedFree (E.dyadicLift P (FiniteFreeProTwo.generator 3 1))).base = _
    rw [retainedFree_base, freeMap_dyadicLift, localPresentation_generator, hL.dyadicB,
      dyadicXVector_eq]
    rfl
  · change (Cut.retainedFree (E.dyadicLift P (FiniteFreeProTwo.generator 3 0))).base = _
    rw [retainedFree_base, freeMap_dyadicLift, localPresentation_generator, hL.dyadicA,
      dyadicYVector_eq]
    rfl
  · change (Cut.retainedFree (E.dyadicLift P (FiniteFreeProTwo.generator 3 0 *
      FiniteFreeProTwo.generator 3 2))).base = _
    rw [retainedFree_base, freeMap_dyadicLift, map_mul, map_mul, localPresentation_generator,
      localPresentation_generator, map_mul, hL.dyadicA, hL.dyadicC, dyadicZVector_eq]
    rfl
  · change CapGood (Cut.retainedFree (lift (E.cap k))).base
    rw [retainedFree_base_lift]
    exact hL.cap k

theorem relatorsTrivial (hR : E.Relations) : RelatorsTrivial E.sourceLifts genuineRelation := by
  refine ⟨fun k ↦ ?_, fun q ↦ ?_, fun P ↦ ?_⟩
  · change freeMap (lift (E.conj k)) ^ 2 = 1
    rw [freeMap_lift, hR.conj_sq]
  · change Lifts.tameWord (tameNorm q) (freeMap (lift (E.tameInertia q)))
      (freeMap (lift (E.tameFrobenius q))) = 1
    rw [freeMap_lift, freeMap_lift, Lifts.tameWord, hR.tame, mul_inv_cancel]
  · change freeMap (E.dyadicLift P genuineRelation) = 1
    rw [freeMap_dyadicLift, localPresentation_genuineRelation, map_one]

/-- **Presentation of `G_B` from the local elements.** -/
theorem relators_generate (hR : E.Relations) (hL : E.Labels) :
    closedNormalClosure (Set.range (E.sourceLifts.relators genuineRelation)) =
      (relationKernel : Subgroup Free) :=
  Presentation.relators_generate E.sourceLifts (sourceLifts_labels hL) genuineRelation
    detector_genuineRelation (relatorsTrivial hR)

/-- The presentation hypothesis of the cut (`Cut.SourceLifts.Presentation`). -/
theorem presentation (hR : E.Relations) (hL : E.Labels) :
    E.sourceLifts.Presentation genuineRelation :=
  Presentation.presentation E.sourceLifts (sourceLifts_labels hL) genuineRelation
    detector_genuineRelation (relatorsTrivial hR)

end LocalElements

end UnitDistance.Sqrt241.Presentation
