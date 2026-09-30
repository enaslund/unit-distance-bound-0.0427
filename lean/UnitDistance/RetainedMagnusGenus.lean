module

public import UnitDistance.RetainedQuadraticCutWords
public import UnitDistance.TruncatedMagnusConjugacyFlexible

@[expose] public section
set_option backward.privateInPublic true


/-! Agreement of the actual Magnus first coordinate with an actual retained
Galois quotient is forced by the free universal property. Thus a single set
of arithmetic genus-coordinate facts serves both quotient constructions. -/
noncomputable section
namespace UnitDistance.RetainedQuadratic.Cut
open ProCGroups ProCGroups.ProC ProCGroups.FreeProC ProCGroups.Presentations
open TruncatedMagnus.Certificate (freeDetector freeCut relatorTails presentationWords dyadicWord)
local instance : AddCommGroup F := Ring.toAddCommGroup
local instance : Module F F := Semiring.toModule
local instance : AddCommGroup V := Pi.addCommGroup
local instance : AddCommGroup W := Pi.addCommGroup
local instance : Module F V := Pi.Function.module (Fin 7) F F
local instance : Module F W := Pi.Function.module (Fin 12) F F
attribute [local irreducible] cocycle

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] {x : Fin 7 → G}
  [TopologicalSpace Q] [DiscreteTopology Q]

/-- The Magnus first coordinate equals the true retained genus coordinate everywhere. -/
theorem freeDetector_first_eq_base
    (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x)
    (ρ : G →ₜ* Q) (hρ : ∀ i,(ρ (x i)).base=Pi.single i 1) (g : G) :
    (freeDetector hfree g).first=(ρ g).base := by
  letI : TopologicalSpace (Multiplicative V) := ⊥
  letI : DiscreteTopology (Multiplicative V) := ⟨rfl⟩
  have hE : HasPGroupOpenNormalBasis 2 (Multiplicative V) := by
    have htwo : IsPGroup 2 (Multiplicative V) := by
      apply IsPGroup.of_card (n := 7)
      rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative V ≃ V)]
      simp [V]
    apply HasOpenNormalBasisInClass.of_allOpenNormalQuotients
    intro U
    exact ⟨inferInstance,htwo.of_surjective (QuotientGroup.mk' (U : Subgroup (Multiplicative V)))
      (QuotientGroup.mk'_surjective (U : Subgroup (Multiplicative V)))⟩
  let f : G →* Multiplicative V :=
    TruncatedMagnus.Group.firstHom.comp (freeDetector hfree).toMonoidHom
  let q : G →* Multiplicative V := (ClassTwo.GroupModel.baseHom cocycle).comp ρ.toMonoidHom
  have hf : Continuous f :=
    (continuous_of_discreteTopology : Continuous TruncatedMagnus.Group.firstHom).comp
      (freeDetector hfree).continuous_toFun
  have hq : Continuous q :=
    (continuous_of_discreteTopology : Continuous (ClassTwo.GroupModel.baseHom cocycle)).comp
      ρ.continuous_toFun
  have he : f=q := hfree.hom_ext hE hf hq (by
    intro i
    apply Multiplicative.toAdd.injective
    dsimp [f, q]
    change (freeDetector hfree (x i)).first=(ρ (x i)).base
    rw [TruncatedMagnus.Certificate.freeDetector_generator, hρ]
    rfl)
  exact congrArg (Multiplicative.toAdd : Multiplicative V → V)
    (DFunLike.congr_fun he g)

/-- A single genuine arithmetic genus diagram proves both retained-field
retention and the required large conjugacy class in a finite quotient. -/
theorem retained_and_cubic_cut_kernel
    (hfree : IsFreeProCGroup (C := FiniteGroupClass.pGroup 2) x)
    (ρ : G →ₜ* Q) (hρ : ∀ i,(ρ (x i)).base=Pi.single i 1)
    (c : G) (t f : Fin 5 → G) (a b d : G)
    (hc : (ρ c).base=vector 1)
    (ht : ∀ i,(ρ (t i)).base=inertiaVector i)
    (hf : ∀ i,(ρ (f i)).base=frobeniusVector i)
    (ha : (ρ a).base=vector 2) (hb : (ρ b).base=vector 53) (hd : (ρ d).base=vector 89)
    (deep : Set G) (hdeep : ∀ g∈deep,g∈GroupAugmentation.dimensionSubgroup F G 4) :
    let N := closedNormalClosure
      (Set.range (presentationWords c t f a b d) ∪ {dyadicWord b d} ∪ deep)
    let ψ := freeCut hfree (relatorTails hfree (presentationWords c t f a b d))
    N ≤ ρ.toMonoidHom.ker ∧ N ≤ ψ.toMonoidHom.ker ∧
      4096 ≤ (Subgroup.centralizer
        ({(⟨ψ c,⟨c,rfl⟩⟩ : ψ.toMonoidHom.range)} : Set ψ.toMonoidHom.range)).index := by
  dsimp only
  refine ⟨literal_closedNormalClosure_le_ker ρ c t f a b d hc ht hf ha hb hd deep hdeep,?_,?_⟩
  · apply TruncatedMagnus.Certificate.literal_closedNormalClosure_le_freeCut_ker hfree
      c t f a b d
    all_goals try simp only [freeDetector_first_eq_base hfree ρ hρ]
    · exact hc
    · exact ht
    · exact hf
    · exact ha
    · exact hb
    · exact hd
    · exact hdeep
  · apply TruncatedMagnus.Certificate.freeCut_image_conjugacy_index_of_first
    rw [freeDetector_first_eq_base hfree ρ hρ,hc]
    have h : vector 1=TruncatedMagnus.Certificate.e 0 := by
      funext i
      have hh : ∀ i : Fin 7,vector 1 i=TruncatedMagnus.Certificate.e 0 i := by decide +kernel
      exact hh i
    exact h

end UnitDistance.RetainedQuadratic.Cut
