/-
Retyped from `UnitDistance/CentralLiftCorrection.lean` (adapted from Naganori
Yamaguchi, SawinTotallyRealTowers, commit 3a455e1aa9140dbbe7b7d68f508392a69c86d0f4,
Apache-2.0; source RealCentralLiftCorrection.lean): the base ℚ is replaced by an
arbitrary number field `F`, and the ℚ-only input (prime three in `T`, used to
build a character with prescribed inertia from ℚ(√−3)) is replaced by the
hypothesis `PrescribedQuadraticInertia F T`.
-/
module

public import UnitDistance.CentralLiftCorrection

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Removing unwanted inertia from cocycle lifts over a number field

`PrescribedQuadraticInertia F T` asks that every finite family of local
quadratic characters be realized on inertia, outside `T`, by one global
quadratic character that is unramified outside the family and `T`. Under this
hypothesis an absolute cocycle lift can be twisted so as to kill all inertia
outside `T` (the generic local input `exists_inertia_trivial_local_cocycle_lift`
is reused from the ℚ development, where it is already stated for any `F`).
-/

open scoped NumberField Topology
open NumberField IsDedekindDomain

noncomputable section

namespace UnitDistance.Sqrt241.Relation

open ClassFieldTower.Sawin ClassFieldTower.Cohomology ClassFieldTower.ProP
open ClassFieldTower.Martinet.Shafarevich ProCGroups
open UnitDistance.ArithmeticProP (exists_inertia_trivial_local_cocycle_lift)

/-- Every finite family of local quadratic characters is realized, on inertia
at the places of the family outside `T`, by a global quadratic character
unramified at every place outside the family and `T`. -/
def PrescribedQuadraticInertia (F : Type) [Field F] [NumberField F]
    (T : Set (HeightOneSpectrum (𝓞 F))) : Prop :=
  ∀ (S' : Finset (HeightOneSpectrum (𝓞 F)))
    (χ : ∀ v : ↥S', finitePlaceAbsoluteDecompositionGroup F v.1 →ₜ*
      Multiplicative (ZMod 2)),
    ∃ γ : Field.absoluteGaloisGroup F →ₜ* Multiplicative (ZMod 2),
      (∀ v : ↥S', v.1 ∉ T → ∀ σ : finitePlaceAbsoluteInertiaSubgroup F v.1,
          χ v σ.1 = γ (finitePlaceAbsoluteDecompositionInclusion F v.1 σ.1)) ∧
      (∀ v : HeightOneSpectrum (𝓞 F), v ∉ S' → v ∉ T →
        ∀ σ : finitePlaceAbsoluteInertiaSubgroup F v,
          γ (finitePlaceAbsoluteDecompositionInclusion F v σ.1) = 1)

theorem twist_eq_one_at
    {F : Type} [Field F]
    {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (z : trivialZModPCocyclesLifted 2 Q 2)
    (s : Field.absoluteGaloisGroup F →ₜ* H2CocycleExtension z)
    (γ : Field.absoluteGaloisGroup F →ₜ* Multiplicative (ZMod 2))
    (σ : Field.absoluteGaloisGroup F)
    (hs : H2CocycleExtension.projection z (s σ) = 1)
    (hγ : γ σ = Multiplicative.ofAdd (s σ).left.down) :
    H2CocycleExtension.twistByCharacter z s γ σ = 1 := by
  apply H2CocycleExtension.ext
  · apply ULift.ext
    change (s σ).left.down - (γ σ).toAdd = 0
    rw [hγ]
    exact sub_self _
  · exact hs

/-- Finite ramification of an absolute lift permits a global character
correction killing all prescribed outside inertia. -/
theorem exists_inertia_corrected_absolute_cocycle_lift
    (F : Type) [Field F] [NumberField F]
    (T : Set (HeightOneSpectrum (𝓞 F)))
    (hchar : PrescribedQuadraticInertia F T)
    {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (q : Field.absoluteGaloisGroup F →ₜ* Q)
    (z : trivialZModPCocyclesLifted 2 Q 2)
    (s : Field.absoluteGaloisGroup F →ₜ* H2CocycleExtension z)
    (hs : (H2CocycleExtension.projection z).comp s = q)
    (hInertia : ∀ (v : HeightOneSpectrum (𝓞 F)), v ∉ T →
      ∀ σ : finitePlaceAbsoluteInertiaSubgroup F v,
        q (finitePlaceAbsoluteDecompositionInclusion F v σ.1) = 1) :
    ∃ γ : Field.absoluteGaloisGroup F →ₜ* Multiplicative (ZMod 2),
      (∀ (v : HeightOneSpectrum (𝓞 F)), v ∉ T →
        ∀ σ : finitePlaceAbsoluteInertiaSubgroup F v,
          H2CocycleExtension.twistByCharacter z s γ
            (finitePlaceAbsoluteDecompositionInclusion F v σ.1) = 1) := by
  classical
  let : DiscreteTopology (H2CocycleExtension z) :=
    (H2CocycleExtension.toProdHomeomorph z).symm.discreteTopology
  have hFinite := absoluteDiscreteHom_inertia_support_finite F s
  let S := hFinite.toFinset
  have hLocal (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ T) :
      ∃ t : finitePlaceAbsoluteDecompositionGroup F v →ₜ* H2CocycleExtension z,
        (H2CocycleExtension.projection z).comp t =
          q.comp (finitePlaceAbsoluteDecompositionInclusion F v) ∧
        finitePlaceAbsoluteInertiaSubgroup F v ≤ t.toMonoidHom.ker := by
    apply exists_inertia_trivial_local_cocycle_lift F 2 v
      (q.comp (finitePlaceAbsoluteDecompositionInclusion F v)) _ z
    intro σ hσ
    exact hInertia v hv ⟨σ, hσ⟩
  let t (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ T) := (hLocal v hv).choose
  have ht (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ T) :=
    (hLocal v hv).choose_spec
  have hProjection (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ T) :
      (H2CocycleExtension.projection z).comp
        (s.comp (finitePlaceAbsoluteDecompositionInclusion F v)) =
      (H2CocycleExtension.projection z).comp (t v hv) := by
    rw [(ht v hv).1]
    ext σ
    exact DFunLike.congr_fun hs (finitePlaceAbsoluteDecompositionInclusion F v σ)
  let χ (v : ↥S) : finitePlaceAbsoluteDecompositionGroup F v.1 →ₜ*
      Multiplicative (ZMod 2) :=
    if hv : v.1 ∉ T then
      H2CocycleExtension.liftDifference z
        (s.comp (finitePlaceAbsoluteDecompositionInclusion F v.1))
        (t v.1 hv) (hProjection v.1 hv)
    else 1
  obtain ⟨γ, hγInside, hγOutside⟩ := hchar S χ
  refine ⟨γ, ?_⟩
  · intro v hv σ
    apply twist_eq_one_at z s γ _
    · exact (DFunLike.congr_fun hs _).trans (hInertia v hv σ)
    · by_cases hS : v ∈ S
      · have hc := hγInside ⟨v, hS⟩ hv σ
        dsimp only [χ] at hc
        rw [dite_eq_left hv] at hc
        change Multiplicative.ofAdd
          ((s (finitePlaceAbsoluteDecompositionInclusion F v σ.1)).left.down -
            (t v hv σ.1).left.down) = _ at hc
        have htσ : t v hv σ.1 = 1 := (ht v hv).2 σ.property
        rw [htσ] at hc
        change Multiplicative.ofAdd
          ((s (finitePlaceAbsoluteDecompositionInclusion F v σ.1)).left.down - 0) = _ at hc
        have hsub :
            Multiplicative.ofAdd
                ((s (finitePlaceAbsoluteDecompositionInclusion F v σ.1)).left.down -
                  (0 : ZMod 2)) =
              Multiplicative.ofAdd
                ((s (finitePlaceAbsoluteDecompositionInclusion F v σ.1)).left.down) :=
          congrArg Multiplicative.ofAdd (sub_zero _)
        rw [hsub] at hc
        exact hc.symm
      · have hsσ : s (finitePlaceAbsoluteDecompositionInclusion F v σ.1) = 1 := by
          by_contra hh
          exact hS (hFinite.mem_toFinset.mpr ⟨σ, hh⟩)
        rw [hsσ]
        exact hγOutside v hS hv σ

end UnitDistance.Sqrt241.Relation
