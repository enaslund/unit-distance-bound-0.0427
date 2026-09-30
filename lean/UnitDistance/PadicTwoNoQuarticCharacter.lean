module

public import UnitDistance.PadicTwoFiniteRestriction
public import UnitDistance.PadicTwoNoCyclicQuartic

@[expose] public section
set_option backward.privateInPublic true


/-! The actual imaginary quadratic character of the maximal local pro-two
Galois group cannot lift to a cyclic quotient of order four. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.PadicTwoMaximalProTwo
open ProCGroups Multiquadratic
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The fixed actual imaginary root in the algebraic closure. -/
def imaginaryRoot : Closure := genusEmbedding (PadicTwoGenus.roots 0)

theorem imaginaryRoot_sq : imaginaryRoot^2= -1 := by
  have h : (PadicTwoGenus.roots 0)^2=(-1 : PadicTwoGenus.GenusField) := by
    simpa [PadicTwo.independentRadicand] using PadicTwoGenus.roots_sq_int 0
  rw [imaginaryRoot,←map_pow,h,map_neg,map_one]

theorem fixes_imaginaryRoot_of_sign_zero (σ : AbsoluteGroup)
    (hσ : (absoluteSigns σ).toAdd 0=0) : σ imaginaryRoot=imaginaryRoot := by
  let τ := GaloisEmbedding.restriction genusEmbedding σ
  have ht : (PadicTwoGenus.signEquiv τ).toAdd 0=0 := hσ
  have h := PadicTwoGenus.signAutomorphism_roots (PadicTwoGenus.signEquiv τ).toAdd 0
  rw [show PadicTwoGenus.signAutomorphism (PadicTwoGenus.signEquiv τ).toAdd=τ from
    PadicTwoGenus.signEquiv.symm_apply_apply τ,ht,binarySign_zero,one_mul] at h
  change σ (genusEmbedding (PadicTwoGenus.roots 0))=genusEmbedding (PadicTwoGenus.roots 0)
  rw [←GaloisEmbedding.restriction_commutes genusEmbedding σ]
  exact congrArg genusEmbedding h

/-- There is no continuous cyclic quotient of order four whose kernel fixes
the actual imaginary quadratic character. Its fixed field would be a genuine
forbidden cyclic quartic extension of Q₂ containing a square root of minus one. -/
theorem no_cyclic_four_quotient
    {C : Type} [_root_.Group C] [TopologicalSpace C] [DiscreteTopology C]
    [IsCyclic C] (hcard : Nat.card C=4)
    (q : Group →ₜ* C) (hq : Function.Surjective q)
    (hker : ∀g, q g=1 → (signs g).toAdd 0=0) : False := by
  let f := q.comp projection
  have hf : Function.Surjective f := hq.comp projection_surjective
  let V : OpenNormalSubgroup AbsoluteGroup :=
    { toOpenSubgroup :=
        { toSubgroup := f.toMonoidHom.ker
          isOpen' := by
            change IsOpen (f ⁻¹' {1})
            exact (isOpen_discrete _).preimage f.continuous }
      isNormal' := inferInstance }
  let L := IntermediateField.fixedField (V : Subgroup AbsoluteGroup)
  let Vc : ClosedSubgroup AbsoluteGroup := ⟨(V : Subgroup AbsoluteGroup),V.isClosed⟩
  have hfix : L.fixingSubgroup=(V : Subgroup AbsoluteGroup) :=
    InfiniteGalois.fixingSubgroup_fixedField Vc
  letI : Module.Finite ℚ_[2] L := (InfiniteGalois.isOpen_iff_finite L).mp (by
    rw [hfix]
    exact V.isOpen)
  letI : IsGalois ℚ_[2] L := (InfiniteGalois.normal_iff_isGalois L).mp (by
    rw [hfix]
    exact V.isNormal')
  let e₁ : (AbsoluteGroup ⧸ (V : Subgroup AbsoluteGroup)) ≃* Gal(L/ℚ_[2]) :=
    InfiniteGalois.normalAutEquivQuotient Vc
  let e₂ : (AbsoluteGroup ⧸ (V : Subgroup AbsoluteGroup)) ≃* C :=
    QuotientGroup.liftEquiv _ hf rfl
  let e := e₁.symm.trans e₂
  letI : IsCyclic Gal(L/ℚ_[2]) := isCyclic_of_injective e.toMonoidHom e.injective
  have hd : Module.finrank ℚ_[2] L=4 :=
    (IsGalois.card_aut_eq_finrank ℚ_[2] L).symm.trans ((Nat.card_congr e.toEquiv).trans hcard)
  have hi : imaginaryRoot∈L := by
    intro σ
    apply fixes_imaginaryRoot_of_sign_zero σ.val
    exact hker (projection σ.val) σ.property
  exact PadicTwo.no_cyclic_quartic L hd ⟨imaginaryRoot,hi⟩ (by
    apply Subtype.ext
    exact imaginaryRoot_sq)

end UnitDistance.PadicTwoMaximalProTwo
