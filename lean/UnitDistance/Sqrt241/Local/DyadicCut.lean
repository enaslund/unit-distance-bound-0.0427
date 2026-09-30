module

public import UnitDistance.Sqrt241.Local.Maps
public import UnitDistance.SigmaDyadicRetainedDiagram
public import UnitDistance.SigmaDyadicInertiaCard
public import UnitDistance.PadicTwoGlobalMapSurjective
public import UnitDistance.SigmaRetainedInertia

@[expose] public section
set_option backward.privateInPublic true

/-!
# The ℚ₂-local cut `G_{ℚ₂}(2) → D` and its indices `e = 8`, `f = 4`

The local dyadic cut is the quotient of the maximal pro-2 quotient of `Gal(ℚ̄₂/ℚ₂)` by the
genuine relation and the six dyadic cuts in the local generators `x, y, z`
(`Dyadic.ArithmeticPresentation`). It is realized here as a continuous surjection
`localCut : PadicTwoMaximalProTwo.Group →ₜ* Dyadic.D` with
`localCut ∘ localPresentation = model` (`localCut_presentation`): the ℚ retained field's
dyadic local map factors as the injective `SigmaDyadic.retainedDyadic` after `localCut`
(`retainedDyadic_localCut`), which also shows that `model` factors through the local
Galois group.

Consequences:
* any local map killing the relation and the cuts factors through `localCut`
  (`factor_through_localCut`), with the same kernel if the factor is injective
  (`ker_eq_localCut_ker`);
* on the chosen decomposition group at `2`, `dyadicCutD : AbsoluteDecomposition 2 →* D`
  (`dyadicCutD_decomposition`) is surjective and sends absolute inertia onto a subgroup of
  order `8` (`dyadicCutD_inertia_card`), so every map factoring injectively through it has
  inertia image `8` and decomposition image `32`, i.e. `(e, f) = (8, 4)`
  (`image_cards_of_factor`);
* the ℚ package's retained field is cut out by the same kernel at `2`
  (`retained_decompositionMap`), the comparison used by the root-discriminant bound
  `Discriminant.log_rootDiscriminant_le_of_retained_comparison`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Local

open NumberField UnitDistance.PrimeCompletion ProCGroups ProCGroups.ProC ArithmeticProP Tower

attribute [local instance] PrimeCompletion.primeFact PrimeCompletion.baseRationalAlgebra

/-! ## The local cut -/

/-- The ℚ retained field's local map at the chosen place above `2`. -/
def retainedLocalQ : PadicTwoMaximalProTwo.Group →ₜ* RetainedQuadratic.Q :=
  sigmaRetainedModelMap.comp PadicTwoGlobalMap.toGlobal

theorem retainedLocalQ_presentation (s : PadicTwoQuadraticRelation.Source) :
    retainedLocalQ (SigmaDyadic.localPresentation s) =
      SigmaDyadic.retainedDyadic (Dyadic.ArithmeticPresentation.model s) := by
  have h := DFunLike.congr_fun SigmaDyadic.retainedDyadic_comp_model s
  change SigmaDyadic.retainedDyadic (Dyadic.ArithmeticPresentation.model s) =
    sigmaRetainedModelMap (sigmaFreeMap (SigmaDyadic.toSigmaFree s)) at h
  rw [SigmaDyadic.commuting_square_apply] at h
  exact h.symm

theorem retainedLocalQ_mem_range (g : PadicTwoMaximalProTwo.Group) :
    retainedLocalQ g ∈ SigmaDyadic.retainedDyadic.range := by
  obtain ⟨s, rfl⟩ := SigmaDyadic.localPresentation_surjective g
  rw [retainedLocalQ_presentation]
  exact ⟨_, rfl⟩

/-- The range of `retainedDyadic` identified with `D`. -/
def retainedDyadicEquiv : Dyadic.D ≃* SigmaDyadic.retainedDyadic.range :=
  MonoidHom.ofInjective SigmaDyadic.retainedDyadic_injective

/-- **The ℚ₂-local cut.** -/
def localCut : PadicTwoMaximalProTwo.Group →ₜ* Dyadic.D where
  toMonoidHom := retainedDyadicEquiv.symm.toMonoidHom.comp
    (retainedLocalQ.toMonoidHom.codRestrict _ retainedLocalQ_mem_range)
  continuous_toFun := by
    have h1 : Continuous (fun g : PadicTwoMaximalProTwo.Group =>
        (⟨retainedLocalQ g, retainedLocalQ_mem_range g⟩ : SigmaDyadic.retainedDyadic.range)) :=
      retainedLocalQ.continuous.subtype_mk _
    exact (continuous_of_discreteTopology (f := retainedDyadicEquiv.symm)).comp h1

theorem retainedDyadic_localCut (g : PadicTwoMaximalProTwo.Group) :
    SigmaDyadic.retainedDyadic (localCut g) = retainedLocalQ g := by
  have h := retainedDyadicEquiv.apply_symm_apply
    (⟨retainedLocalQ g, retainedLocalQ_mem_range g⟩ : SigmaDyadic.retainedDyadic.range)
  exact congrArg Subtype.val h

theorem localCut_presentation_apply (s : PadicTwoQuadraticRelation.Source) :
    localCut (SigmaDyadic.localPresentation s) = Dyadic.ArithmeticPresentation.model s := by
  apply SigmaDyadic.retainedDyadic_injective
  rw [retainedDyadic_localCut, retainedLocalQ_presentation]

theorem localCut_presentation :
    localCut.comp SigmaDyadic.localPresentation = Dyadic.ArithmeticPresentation.model :=
  ContinuousMonoidHom.ext localCut_presentation_apply

theorem localCut_surjective : Function.Surjective localCut := by
  intro d
  obtain ⟨s, rfl⟩ := Dyadic.ArithmeticPresentation.model_surjective d
  exact ⟨SigmaDyadic.localPresentation s, localCut_presentation_apply s⟩

/-- The three local generators: `a ↦ y`, `b ↦ x`, `c ↦ y z`. -/
theorem localCut_generator (i : Fin 3) :
    localCut (PadicTwoQuadraticRelation.generator i) = ![Dyadic.D.y, Dyadic.D.x, Dyadic.D.y * Dyadic.D.z] i := by
  rw [← SigmaDyadic.localPresentation_generator, localCut_presentation_apply,
    Dyadic.ArithmeticPresentation.model_generator]

/-- The ℚ retained field's local map is `retainedDyadic ∘ localCut`. -/
theorem retainedLocalQ_eq :
    retainedLocalQ.toMonoidHom = SigmaDyadic.retainedDyadic.comp localCut.toMonoidHom :=
  MonoidHom.ext fun g => (retainedDyadic_localCut g).symm

/-- Any homomorphism agreeing with the model on the local presentation factors through the
local cut. -/
theorem factor_through_localCut {H : Type*} [Group H] (ψ : PadicTwoMaximalProTwo.Group →* H)
    (f : Dyadic.D →* H)
    (h : ψ.comp SigmaDyadic.localPresentation.toMonoidHom =
      f.comp Dyadic.ArithmeticPresentation.model.toMonoidHom) :
    ψ = f.comp localCut.toMonoidHom := by
  apply MonoidHom.ext
  intro g
  obtain ⟨s, rfl⟩ := SigmaDyadic.localPresentation_surjective g
  have hs := DFunLike.congr_fun h s
  change ψ (SigmaDyadic.localPresentation s) = f (localCut (SigmaDyadic.localPresentation s))
  rw [localCut_presentation_apply]
  exact hs

theorem ker_eq_localCut_ker {H : Type*} [Group H] (ψ : PadicTwoMaximalProTwo.Group →* H)
    (f : Dyadic.D →* H) (hf : Function.Injective f) (hψ : ψ = f.comp localCut.toMonoidHom) :
    ψ.ker = localCut.toMonoidHom.ker := by
  rw [hψ]
  ext g
  change f (localCut g) = 1 ↔ localCut g = 1
  rw [← map_one f]
  exact hf.eq_iff

/-! ## The chosen decomposition group at 2 -/

theorem absoluteHom_injective : Function.Injective PadicTwoGlobalMap.absoluteHom := by
  intro σ τ h
  apply AlgEquiv.ext
  intro x
  have hx := congrArg (fun g : Gal(PadicTwoGlobalMap.LocalClosure/PadicTwoGlobalMap.Base) =>
    g (PadicTwoGlobalMap.closureEquiv x)) h
  change PadicTwoGlobalMap.closureEquiv (σ (PadicTwoGlobalMap.closureEquiv.symm
      (PadicTwoGlobalMap.closureEquiv x))) =
    PadicTwoGlobalMap.closureEquiv (τ (PadicTwoGlobalMap.closureEquiv.symm
      (PadicTwoGlobalMap.closureEquiv x))) at hx
  simpa using hx

theorem dyadicDecomposition_bijective : Function.Bijective dyadicDecomposition :=
  ⟨fun _ _ h => absoluteHom_injective ((decompositionEquiv prime2).symm.injective h),
    PadicTwoGlobalMap.decomposition_surjective⟩

/-- `Gal(ℚ̄₂/ℚ₂)` is the chosen decomposition group at `2`. -/
def dyadicDecompositionEquiv : PadicTwoMaximalProTwo.AbsoluteGroup ≃* AbsoluteDecomposition prime2 :=
  MulEquiv.ofBijective dyadicDecomposition.toMonoidHom dyadicDecomposition_bijective

/-- The local cut read on the chosen decomposition group at `2`. -/
def dyadicCutD : AbsoluteDecomposition prime2 →* Dyadic.D :=
  (localCut.toMonoidHom.comp PadicTwoMaximalProTwo.projection.toMonoidHom).comp
    dyadicDecompositionEquiv.symm.toMonoidHom

theorem dyadicCutD_decomposition (σ : PadicTwoMaximalProTwo.AbsoluteGroup) :
    dyadicCutD (PadicTwoGlobalMap.decomposition σ) = localCut (PadicTwoMaximalProTwo.projection σ) := by
  change localCut (PadicTwoMaximalProTwo.projection
    (dyadicDecompositionEquiv.symm (dyadicDecompositionEquiv σ))) = _
  rw [MulEquiv.symm_apply_apply]

theorem dyadicCutD_surjective : Function.Surjective dyadicCutD := by
  intro d
  obtain ⟨g, rfl⟩ := localCut_surjective d
  obtain ⟨σ, rfl⟩ := PadicTwoMaximalProTwo.projection_surjective g
  exact ⟨_, dyadicCutD_decomposition σ⟩

/-- **Comparison with the ℚ retained field at 2**: its decomposition map is
`retainedDyadic ∘ dyadicCutD` (`retainedDyadic` injective). -/
theorem retained_decompositionMap (d : AbsoluteDecomposition prime2) :
    sigmaRetainedModelMap (SigmaUnramified.decompositionMap prime2 d) =
      SigmaDyadic.retainedDyadic (dyadicCutD d) := by
  obtain ⟨σ, rfl⟩ := PadicTwoGlobalMap.decomposition_surjective d
  rw [dyadicCutD_decomposition, retainedDyadic_localCut]
  rfl

/-- The ℚ retained field's decomposition restriction at `2` is `dyadicCutD` up to an
isomorphism, so both have the same kernel on the chosen decomposition group. -/
theorem retained_restriction_eq_one_iff (d : AbsoluteDecomposition prime2) :
    decompositionRestriction prime2 ArithmeticRetained.RetainedField
      sigmaRetainedAbsoluteEmbedding d = 1 ↔ dyadicCutD d = 1 := by
  rw [← sigmaRetainedRestriction_decomposition]
  have h := retained_decompositionMap d
  change sigmaRetainedModelEquiv.symm (sigmaRetainedRestriction
    (SigmaUnramified.decompositionMap prime2 d)) = _ at h
  constructor
  · intro h1
    rw [h1, map_one] at h
    exact SigmaDyadic.retainedDyadic_injective (h.symm.trans (map_one _).symm)
  · intro h1
    rw [h1, map_one] at h
    exact sigmaRetainedModelEquiv.symm.injective (h.trans (map_one _).symm)

/-- **Dyadic inertia has order 8** in the local cut. -/
theorem dyadicCutD_inertia_card :
    Nat.card (dyadicCutD.comp (AbsoluteInertia prime2).subtype).range = 8 := by
  have he : SigmaCut.retainedDyadicInertiaMap =
      SigmaDyadic.retainedDyadic.comp (dyadicCutD.comp (AbsoluteInertia prime2).subtype) := by
    apply MonoidHom.ext
    intro i
    exact retained_decompositionMap i.val
  have h := retained_dyadic_inertia_card
  rw [he, MonoidHom.range_comp] at h
  rwa [Subgroup.card_map_of_injective SigmaDyadic.retainedDyadic_injective] at h

/-- **Indices `(e, f) = (8, 4)`**: a map of the chosen decomposition group at `2` factoring
injectively through the local cut has inertia image of order `8` and decomposition image of
order `32`. -/
theorem image_cards_of_factor {H : Type*} [Group H] (ψ : AbsoluteDecomposition prime2 →* H)
    (f : Dyadic.D →* H) (hf : Function.Injective f) (hψ : ψ = f.comp dyadicCutD) :
    Nat.card (ψ.comp (AbsoluteInertia prime2).subtype).range = 8 ∧ Nat.card ψ.range = 32 := by
  subst hψ
  constructor
  · rw [MonoidHom.comp_assoc, MonoidHom.range_comp,
      Subgroup.card_map_of_injective hf, dyadicCutD_inertia_card]
  · rw [MonoidHom.range_comp, Subgroup.card_map_of_injective hf,
      MonoidHom.range_eq_top_of_surjective _ dyadicCutD_surjective, Subgroup.card_top,
      Nat.card_eq_fintype_card, Dyadic.D.card]

/-! ## The dyadic local maps into `G_B` at the chosen place -/

/-- The unnormalized absolute map at the chosen place is the dyadic local map at `dyadicPlace`
on the pro-2 quotient. -/
theorem decompositionMapB_dyadic (σ : PadicTwoMaximalProTwo.AbsoluteGroup) :
    decompositionMapB prime2 isSquare_241_two (PadicTwoGlobalMap.decomposition σ) =
      dyadicLocal dyadicPlace (PadicTwoMaximalProTwo.projection σ) := by
  rw [dyadicLocal_projection, frame_self, conjGB_one]
  rfl

/-- If the dyadic local map at the chosen place becomes, after `q`, a map factoring through the
local cut, then so does the chosen decomposition map at `2`. -/
theorem decompositionMapB_factor {H : Type*} [Group H] (q : GB →* H) (f : Dyadic.D →* H)
    (hq : q.comp (dyadicLocal dyadicPlace).toMonoidHom = f.comp localCut.toMonoidHom) :
    q.comp (decompositionMapB prime2 isSquare_241_two).toMonoidHom = f.comp dyadicCutD := by
  apply MonoidHom.ext
  intro d
  obtain ⟨σ, rfl⟩ := PadicTwoGlobalMap.decomposition_surjective d
  change q (decompositionMapB prime2 isSquare_241_two (PadicTwoGlobalMap.decomposition σ)) =
    f (dyadicCutD (PadicTwoGlobalMap.decomposition σ))
  rw [decompositionMapB_dyadic, dyadicCutD_decomposition]
  exact DFunLike.congr_fun hq _

end UnitDistance.Sqrt241.Local
