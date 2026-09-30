module

public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Tactic

@[expose] public section
set_option backward.privateInPublic true


/-! # Residue fields are preserved by dense valuation-preserving embeddings

This supplies the local-field completion bridge using actual residue maps.
Density provides an approximation modulo the maximal ideal; preservation of
the valuation ensures that the approximation lies in the source integer ring.
-/

noncomputable section
open Set Valued

namespace UnitDistance.Local.ResidueDensity

variable {K L Γ : Type*} [Field K] [Field L] [LinearOrderedCommGroupWithZero Γ]
    [Valued K Γ] [Valued L Γ]
variable (f : K →+* L) (hf : ∀ x, Valued.v (f x) = Valued.v x)

/-- The map of the actual valuation rings induced by a valuation-preserving
field embedding. -/
def integerMap : Valued.integer K →+* Valued.integer L where
  toFun x := ⟨f (x : K), by
    change Valued.v (f (x : K)) ≤ (1 : Γ)
    rw [hf]
    exact x.property⟩
  map_zero' := Subtype.ext (map_zero f)
  map_one' := Subtype.ext (map_one f)
  map_add' x y := Subtype.ext (map_add f (x : K) (y : K))
  map_mul' x y := Subtype.ext (map_mul f (x : K) (y : K))

instance integerMap_isLocalHom : IsLocalHom (integerMap f hf) where
  map_nonunit x hx := by
    apply (Valuation.integer.integers (Valued.v : Valuation K Γ)).isUnit_iff_valuation_eq_one.mpr
    have h := (Valuation.integer.integers (Valued.v : Valuation L Γ)).isUnit_iff_valuation_eq_one.mp hx
    change Valued.v (f (x : K)) = (1 : Γ) at h
    change Valued.v (x : K) = (1 : Γ)
    simpa only [hf] using h

/-- The induced map on the actual valuation-ring residue fields. -/
def residueMap : Valued.ResidueField K →+* Valued.ResidueField L :=
  IsLocalRing.ResidueField.map (integerMap f hf)

theorem residueMap_injective : Function.Injective (residueMap f hf) :=
  (residueMap f hf).injective

/-- Equality modulo the maximal ideal is exactly valuation less than one. -/
theorem residue_eq_iff (x y : Valued.integer L) :
    IsLocalRing.residue (Valued.integer L) x = IsLocalRing.residue (Valued.integer L) y ↔
      Valued.v ((x : L) - y) < (1 : Γ) := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  rfl

/-- Every target residue class has a representative from a dense source. -/
theorem residueMap_surjective (hdense : DenseRange f) :
    Function.Surjective (residueMap f hf) := by
  intro r
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective r
  have hopen : IsOpen {z : L | Valued.v (z - x) < (1 : Γ)} := by
    have h := (Valued.isOpen_ball L (1 : MonoidWithZeroHom.ValueGroup₀ (.ofClass
      (Valued.v : Valuation L Γ)))).preimage (continuous_id.sub continuous_const : Continuous (fun z : L => z - (x : L)))
    change IsOpen {z : L | (Valued.v : Valuation L Γ).restrict (z - x) < 1} at h
    simpa only [Valuation.restrict_lt_one_iff] using h
  have hx : (x : L) ∈ {z : L | Valued.v (z - x) < (1 : Γ)} := by simp
  obtain ⟨y, hy⟩ := hdense.mem_nhds (hopen.mem_nhds hx)
  have hyO : Valued.v y ≤ (1 : Γ) := by
    rw [← hf]
    have h := (Valued.v : Valuation L Γ).map_add_le (le_of_lt hy) x.property
    simpa only [sub_add_cancel] using h
  let yO : Valued.integer K := ⟨y, hyO⟩
  refine ⟨IsLocalRing.residue (Valued.integer K) yO, ?_⟩
  change IsLocalRing.residue (Valued.integer L) (integerMap f hf yO) =
    IsLocalRing.residue (Valued.integer L) x
  exact (residue_eq_iff _ _).mpr hy

/-- A dense valuation-preserving field embedding identifies the residue fields. -/
def residueEquiv (hdense : DenseRange f) : Valued.ResidueField K ≃+* Valued.ResidueField L :=
  RingEquiv.ofBijective (residueMap f hf)
    ⟨residueMap_injective f hf, residueMap_surjective f hf hdense⟩

include hf in
theorem residue_card_eq (hdense : DenseRange f) :
    Nat.card (Valued.ResidueField K) = Nat.card (Valued.ResidueField L) :=
  Nat.card_congr (residueEquiv f hf hdense).toEquiv

section Completion

variable (K) (Γ)

/-- Completion of an ordinary valued field preserves its actual residue field. -/
def completionResidueEquiv :
    Valued.ResidueField K ≃+* Valued.ResidueField (UniformSpace.Completion K) :=
  residueEquiv (UniformSpace.Completion.coeRingHom : K →+* UniformSpace.Completion K)
    (fun x => Valued.valuedCompletion_apply x) UniformSpace.Completion.denseRange_coe

theorem completion_residue_card_eq :
    Nat.card (Valued.ResidueField (UniformSpace.Completion K)) = Nat.card (Valued.ResidueField K) :=
  (Nat.card_congr (completionResidueEquiv K Γ).toEquiv).symm

instance completionResidueFinite [Finite (Valued.ResidueField K)] :
    Finite (Valued.ResidueField (UniformSpace.Completion K)) :=
  Finite.of_equiv _ (completionResidueEquiv K Γ).toEquiv

end Completion

end UnitDistance.Local.ResidueDensity
