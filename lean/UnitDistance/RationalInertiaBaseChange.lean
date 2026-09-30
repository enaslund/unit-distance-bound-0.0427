module

public import UnitDistance.RationalGaloisBaseChange
public import UnitDistance.GaloisEmbeddingImageCard

@[expose] public section
set_option backward.privateInPublic true


/-! Cardinality of actual rational absolute inertia after finite restriction,
computed on the genuine local Galois base change through any finite embedding. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
namespace UnitDistance.PrimeCompletion
open ArithmeticProP ClassFieldTower.Martinet.Shafarevich LocalClassFieldTheory
attribute [local instance] primeFact baseRationalAlgebra

variable (p : Nat.Primes) (M : Type) [Field M] [NumberField M] [IsGalois ℚ M]
  (j : M →ₐ[ℚ] AlgebraicClosure ℚ)

def inertiaRestriction : AbsoluteInertia p →* Gal(M/ℚ) :=
  (decompositionRestriction p M j).comp (AbsoluteInertia p).subtype

theorem inertiaRestriction_range : (inertiaRestriction p M j).range=
    (localResidueDegree (Base p)).toMonoidHom.ker.map (localRestriction p M j) := by
  apply le_antisymm
  · rintro _ ⟨σ,rfl⟩
    refine ⟨decompositionEquiv p σ.val,(decomposition_mem_inertia_iff p σ.val).mpr σ.property,?_⟩
    exact localRestriction_decomposition p M j σ.val
  · rintro _ ⟨σ,hσ,rfl⟩
    obtain ⟨τ,rfl⟩ := (decompositionEquiv p).surjective σ
    exact ⟨⟨τ,(decomposition_mem_inertia_iff p τ).mp hσ⟩,
      (localRestriction_decomposition p M j τ).symm⟩

abbrev BaseChange := RationalGaloisBaseChange.Carrier M ℚ_[p.val]

local instance inertiaBaseChangeAlgebra : Algebra (Base p) (BaseChange p M) :=
  targetAlgebra p (BaseChange p M)
local instance inertiaBaseChangeFinite : Module.Finite (Base p) (BaseChange p M) :=
  targetFinite p (BaseChange p M)
local instance inertiaBaseChangeGalois : IsGalois (Base p) (BaseChange p M) :=
  targetGalois p (BaseChange p M)

def baseChangeRestriction : Gal(BaseChange p M/Base p) →* Gal(M/ℚ) :=
  (RationalGaloisBaseChange.restriction M ℚ_[p.val]).comp
    (galoisEquiv p (BaseChange p M)).toMonoidHom

theorem baseChangeRestriction_injective : Function.Injective (baseChangeRestriction p M) :=
  (RationalGaloisBaseChange.restriction_injective M ℚ_[p.val]).comp
    (galoisEquiv p (BaseChange p M)).injective

variable (f : BaseChange p M →ₐ[Base p] SeparableClosure (Base p))

def baseChangeRationalEmbedding : M →ₐ[ℚ] SeparableClosure (Base p) :=
  f.toRingHom.toRatAlgHom.comp (RationalGaloisBaseChange.embedding M ℚ_[p.val])

theorem baseChangeRestriction_commuting :
    (baseChangeRestriction p M).comp (finiteAbsoluteRestriction (Base p) (BaseChange p M) f)=
      (GaloisEmbedding.restriction (baseChangeRationalEmbedding p M f)).toMonoidHom.comp
        (AlgEquiv.restrictScalarsHom ℚ) := by
  apply MonoidHom.ext
  intro σ
  symm
  apply GaloisEmbedding.restriction_unique
  intro x
  change f (RationalGaloisBaseChange.embedding M ℚ_[p.val]
      (RationalGaloisBaseChange.restriction M ℚ_[p.val]
        (galoisEquiv p (BaseChange p M)
          (finiteAbsoluteRestriction (Base p) (BaseChange p M) f σ)) x)) =
    σ (f (RationalGaloisBaseChange.embedding M ℚ_[p.val] x))
  rw [RationalGaloisBaseChange.restriction_commutes]
  exact (finiteAbsoluteRestriction_commutes (Base p) (BaseChange p M) f σ _).symm

/-- The chosen global absolute inertia and any actual local embedding yield
exactly the same finite image cardinality. -/
theorem inertiaRestriction_card_eq_baseChange :
    Nat.card (inertiaRestriction p M j).range=
      Nat.card (finiteAbsoluteInertiaImage (Base p) (BaseChange p M) f) := by
  let I := (localResidueDegree (Base p)).toMonoidHom.ker
  let a : I →* Gal(SeparableClosure (Base p)/ℚ) :=
    (AlgEquiv.restrictScalarsHom ℚ).comp I.subtype
  have hc := GaloisEmbedding.restriction_image_card_eq
    ((absoluteEmbedding p).comp j) (baseChangeRationalEmbedding p M f) a
  have hleft : ((GaloisEmbedding.restriction ((absoluteEmbedding p).comp j)).toMonoidHom.comp a).range=
      (inertiaRestriction p M j).range := by
    rw [inertiaRestriction_range]
    change ((localRestriction p M j).comp I.subtype).range=I.map (localRestriction p M j)
    rw [MonoidHom.range_comp,Subgroup.range_subtype]
  have hright : ((GaloisEmbedding.restriction (baseChangeRationalEmbedding p M f)).toMonoidHom.comp a).range=
      (finiteAbsoluteInertiaImage (Base p) (BaseChange p M) f).map (baseChangeRestriction p M) := by
    change (((GaloisEmbedding.restriction (baseChangeRationalEmbedding p M f)).toMonoidHom.comp
      (AlgEquiv.restrictScalarsHom ℚ)).comp I.subtype).range=_
    rw [←baseChangeRestriction_commuting,MonoidHom.comp_assoc,MonoidHom.range_comp,
      MonoidHom.range_comp,Subgroup.range_subtype]
    rfl
  rw [hleft,hright] at hc
  exact hc.trans (Subgroup.card_map_of_injective (baseChangeRestriction_injective p M))

end UnitDistance.PrimeCompletion
