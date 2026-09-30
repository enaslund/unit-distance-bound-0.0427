module

public import UnitDistance.GaloisEmbeddingRestriction
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.SplittingField.Construction
public import Mathlib.FieldTheory.Normal.Basic

@[expose] public section
set_option backward.privateInPublic true


/-! A finite rational Galois field has a genuine finite Galois base change
inside a splitting field over any characteristic-zero field. Restriction
embeds its Galois group into the original finite Galois group. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.RationalGaloisBaseChange
open Polynomial
variable (M B : Type*) [Field M] [NumberField M] [IsGalois ℚ M]
  [Field B] [CharZero B]

def polynomial : Polynomial ℚ := Classical.choose (Normal.exists_isSplittingField ℚ M)
instance polynomial_splitting : IsSplittingField ℚ M (polynomial M) :=
  Classical.choose_spec (Normal.exists_isSplittingField ℚ M)

abbrev Carrier := ((polynomial M).map (algebraMap ℚ B)).SplittingField

instance baseChange_finite : Module.Finite B (Carrier M B) :=
  Polynomial.IsSplittingField.finiteDimensional _ ((polynomial M).map (algebraMap ℚ B))
instance baseChange_galois : IsGalois B (Carrier M B) :=
  { to_normal := Polynomial.SplittingField.instNormal _ }

theorem polynomial_splits : ((polynomial M).map (algebraMap ℚ (Carrier M B))).Splits := by
  have h := Polynomial.IsSplittingField.splits (Carrier M B)
    ((polynomial M).map (algebraMap ℚ B))
  simpa only [Polynomial.map_map,← IsScalarTower.algebraMap_eq ℚ B (Carrier M B)] using h

/-- An actual rational embedding of the original Galois field. -/
def embedding : M →ₐ[ℚ] Carrier M B :=
  Polynomial.IsSplittingField.lift M (polynomial M) (polynomial_splits M B)

/-- The base-changed field is generated over the new base by the original field image. -/
theorem generated : Algebra.adjoin B (Set.range (embedding M B))=⊤ := by
  apply top_le_iff.mp
  rw [← Polynomial.IsSplittingField.adjoin_rootSet (Carrier M B)
    ((polynomial M).map (algebraMap ℚ B))]
  apply Algebra.adjoin_mono
  intro z hz
  have hs : ((polynomial M).map (algebraMap ℚ B)).rootSet (Carrier M B)=
      (polynomial M).rootSet (Carrier M B) := by
    simp only [Polynomial.rootSet,Polynomial.aroots,Polynomial.map_map,
      ← IsScalarTower.algebraMap_eq ℚ B (Carrier M B)]
  rw [hs,← (Polynomial.IsSplittingField.splits M (polynomial M)).image_rootSet
    (embedding M B)] at hz
  exact Set.image_subset_range _ _ hz

/-- Restriction of the actual local automorphisms to the rational Galois field. -/
def restriction : Gal(Carrier M B/B) →* Gal(M/ℚ) :=
  (GaloisEmbedding.restriction (embedding M B)).toMonoidHom.comp
    (AlgEquiv.restrictScalarsHom ℚ)

theorem restriction_commutes (σ : Gal(Carrier M B/B)) (x : M) :
    embedding M B (restriction M B σ x)=σ (embedding M B x) :=
  GaloisEmbedding.restriction_commutes (embedding M B) (σ.restrictScalars ℚ) x

theorem restriction_injective : Function.Injective (restriction M B) := by
  intro σ τ h
  have he : Set.EqOn σ.toAlgHom τ.toAlgHom (Set.range (embedding M B)) := by
    rintro z ⟨x,rfl⟩
    change σ (embedding M B x)=τ (embedding M B x)
    rw [← restriction_commutes M B σ x,← restriction_commutes M B τ x,h]
  have ha := (AlgHom.eqOn_adjoin_iff (φ := σ.toAlgHom) (ψ := τ.toAlgHom)).mpr he
  rw [generated] at ha
  ext z
  exact ha (show z∈(⊤ : Subalgebra B (Carrier M B)) from trivial)

/-- A genuine p-group base change of a rational p-extension. -/
theorem isPGroup {p : ℕ} (h : IsPGroup p Gal(M/ℚ)) : IsPGroup p Gal(Carrier M B/B) :=
  h.of_injective (restriction M B) (restriction_injective M B)

end UnitDistance.RationalGaloisBaseChange
