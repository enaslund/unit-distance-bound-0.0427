module

public import UnitDistance.GroupAugmentationFoxPresentation
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Index

@[expose] public section
set_option backward.privateInPublic true


/-!
# Fox exactness from an actual finite-2 presentation test

To prove the finite Fox relation sequence, it suffices that every finite
2-group quotient of the free group killing the defining relations kills
the actual evaluation kernel. This is the finite-target formulation of
closed normal generation in the pro-2 topology. The proof supplies its own
finite 2-group test, using the actual evaluated Fox affine group.

The presentation criterion is explicit and is not proved for the manuscript's
arithmetic group by this module.
-/

noncomputable section
namespace UnitDistance.GroupAugmentation
variable (G : Type*) [Group G]
variable {ι : Type*} [Fintype ι]
local notation "F" => ZMod 2
variable (generators : ι → G) (relations : Set (FreeGroup ι))

/-- A literal finite-target criterion for a complete pro-2 presentation.
The first field asserts the actual relation identities. The second tests
actual finite 2-group quotients of the free group, not abstract row costs. -/
structure ProTwoPresentation : Prop where
  relators_vanish : ∀ r ∈ relations, FreeGroup.lift generators r = 1
  finite_test : ∀ (N : Subgroup (FreeGroup ι)) [N.Normal] [Finite (FreeGroup ι ⧸ N)],
    IsPGroup 2 (FreeGroup ι ⧸ N) → relations ⊆ N → (FreeGroup.lift generators).ker ≤ N

/-- Ordinary normal generation implies the finite pro-2 presentation test. -/
theorem proTwoPresentation_of_normalClosure
    (h : (FreeGroup.lift generators).ker = Subgroup.normalClosure relations) :
    ProTwoPresentation G generators relations where
  relators_vanish r hr := by
    apply MonoidHom.mem_ker.mp
    rw [h]
    exact Subgroup.subset_normalClosure hr
  finite_test N _ _ _ hN := by
    rw [h]
    exact Subgroup.normalClosure_le_normal hN

variable (hG : IsPGroup 2 G)

include hG in
/-- The actual affine derivative group of a 2-group is a 2-group: a power
kills its evaluation coordinate and one further squaring kills translation. -/
theorem foxAffine_isTwoGroup : IsPGroup 2 (FoxAffine F G (ι := ι)) := by
  intro x
  obtain ⟨n,hn⟩ := hG x.right
  have hr : (x^(2^n)).right = 1 := by
    change SemidirectProduct.rightHom (x^(2^n)) = 1
    rw [map_pow]
    exact hn
  have hadd (a : Multiplicative (ι → A F G)) : a*a = 1 := by
    apply Multiplicative.toAdd.injective
    funext i
    apply MonoidAlgebra.ext
    apply Finsupp.ext
    intro g
    change (a.toAdd i).coeff g + (a.toAdd i).coeff g = 0
    exact CharTwo.add_self_eq_zero _
  refine ⟨n+1, ?_⟩
  rw [pow_succ,pow_mul,pow_two]
  apply SemidirectProduct.ext
  · simp [SemidirectProduct.mul_left,hr,hadd]
  · simp [SemidirectProduct.mul_right,hr]

variable [Finite G]

instance foxAffine_finite : Finite (FoxAffine F G (ι := ι)) := by
  letI : Fintype G := Fintype.ofFinite G
  letI : Finite (G →₀ F) := Finite.of_equiv (G → F) Finsupp.equivFunOnFinite.symm
  letI : Finite (A F G) :=
    Finite.of_equiv (G →₀ F) (MonoidAlgebra.coeffLinearEquiv F).symm.toEquiv
  exact Finite.of_equiv (Multiplicative (ι → A F G) × G) SemidirectProduct.equivProd.symm

include hG in
/-- Every actual row module supplies a finite 2-group presentation test:
its good-word subgroup contains the actual affine evaluation kernel. -/
theorem foxWordsModulo_isFiniteTwoQuotient
    (M : Submodule (A F G) (ι → A F G)) :
    let N := foxWordsModulo F G generators M
    Finite (FreeGroup ι ⧸ N) ∧ IsPGroup 2 (FreeGroup ι ⧸ N) := by
  let N := foxWordsModulo F G generators M
  let L := foxLift F G generators
  have hle : L.ker ≤ N := by
    intro w hw
    have he : L w = 1 := MonoidHom.mem_ker.mp hw
    constructor
    · have hh := congrArg SemidirectProduct.right he
      simpa only [L,foxLift_right,SemidirectProduct.one_right] using hh
    · have hh := congrArg (fun x : FoxAffine F G (ι := ι) => x.left.toAdd) he
      change foxDerivative F G generators w = 0 at hh
      simpa [hh] using M.zero_mem
  have hsrc : IsPGroup 2 (FreeGroup ι ⧸ L.ker) :=
    ((foxAffine_isTwoGroup G hG).to_subgroup L.range).of_equiv
      (QuotientGroup.quotientKerEquivRange L).symm
  letI : Finite (FreeGroup ι ⧸ L.ker) :=
    Finite.of_equiv L.range (QuotientGroup.quotientKerEquivRange L).symm.toEquiv
  have hle' : L.ker ≤ N.comap (MonoidHom.id (FreeGroup ι)) := by simpa using hle
  let q := QuotientGroup.map L.ker N (MonoidHom.id (FreeGroup ι)) hle'
  have hq : Function.Surjective q :=
    QuotientGroup.map_surjective_of_surjective L.ker N (MonoidHom.id (FreeGroup ι))
      QuotientGroup.mk_surjective hle'
  exact ⟨Finite.of_surjective q hq,hsrc.of_surjective q hq⟩

include hG in
/-- Actual defining Fox rows generate the actual Fox kernel under a
complete finite-2 presentation criterion. No continuous Fox theorem is
assumed; the necessary finite 2-group test is constructed above. -/
theorem foxKernel_eq_relationModule_of_proTwoPresentation
    (hgen : Subgroup.closure (Set.range generators) = ⊤)
    (hpresentation : ProTwoPresentation G generators relations) :
    (foxMap F G generators).ker = (foxRelationModule F G generators relations).restrictScalars F := by
  let M := foxRelationModule F G generators relations
  obtain ⟨hfinite,hTwo⟩ := foxWordsModulo_isFiniteTwoQuotient G generators hG M
  letI := hfinite
  have hN : relations ⊆ foxWordsModulo F G generators M := by
    intro r hr
    exact ⟨hpresentation.relators_vanish r hr,Submodule.subset_span ⟨r,hr,rfl⟩⟩
  have hker := hpresentation.finite_test (foxWordsModulo F G generators M) hTwo hN
  apply le_antisymm
  · rw [foxKernel_eq_span_derivatives F G generators hgen]
    apply Submodule.span_le.mpr
    rintro v ⟨w,hw,rfl⟩
    exact (hker (MonoidHom.mem_ker.mpr hw)).2
  · have hm : M ≤ (foxMapAlgebra F G generators).ker := by
      apply Submodule.span_le.mpr
      rintro v ⟨r,hr,rfl⟩
      exact foxDerivative_mem_ker F G generators r (hpresentation.relators_vanish r hr)
    exact hm

end UnitDistance.GroupAugmentation
