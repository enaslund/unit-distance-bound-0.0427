module

public import UnitDistance.Sqrt241.GroupData.DyadicMaps
public import UnitDistance.DyadicArithmeticPresentation
public import UnitDistance.FiniteFreeProTwo
public import UnitDistance.Upstream.Yamaguchi.ProCGroups.Topologies.QuotientMaps

@[expose] public section
set_option backward.privateInPublic true


/-!
# The literal cut on the free pro-2 source of rank eight

The arithmetic enters only through

* `SourceLifts`: lifts to `FiniteFreeProTwo.Carrier 8` of the local generators,
  with the dyadic places given by continuous maps of the local rank-three
  source `Dyadic.ArithmeticPresentation.Source` (from the local elements of `Local/`);
* `SourceLifts.Labels`: their elementary vectors (construction.md §3.4) under
  the free retained map (proved for the local elements in `Local/`);
* a genuine local relation `r` with the proved quadratic initial, and the
  presentation hypothesis `SourceLifts.Presentation A r`: the lifted genuine
  relation at `𝔭₁` lies in the closed normal closure of the seven relators
  `c₁², c₂²`, the four tame words and the lifted genuine relation at `𝔭₂`
  (proved in `Presentation/`).

The cut kernel is the closed normal closure of the thirty literal words
(`Lifts.words`); the free retained map descends to the cut quotient.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace UnitDistance.Sqrt241.Cut
open ProCGroups ProCGroups.ProC ProCGroups.FreeProC ProCGroups.Presentations GroupData
open Dyadic.Presentation (comm literalRelations)

abbrev Source := FiniteFreeProTwo.Carrier 8
abbrev LocalSource := Dyadic.ArithmeticPresentation.Source

/-- Arithmetic lifts of the local generators to the free source. -/
structure SourceLifts where
  conj : Fin 2 → Source
  tameInertia : Fin 4 → Source
  tameFrobenius : Fin 4 → Source
  dyadic : Fin 2 → (LocalSource →ₜ* Source)
  cap : Fin 3 → Source

namespace SourceLifts

/-- The underlying lifts: `x, y, z` at `𝔭_P` are the images of the local
`x = b`, `y = a`, `z = a c`. -/
def lifts (A : SourceLifts) : Lifts Source where
  conj := A.conj
  tameInertia := A.tameInertia
  tameFrobenius := A.tameFrobenius
  dyadicX P := A.dyadic P Dyadic.ArithmeticPresentation.x
  dyadicY P := A.dyadic P Dyadic.ArithmeticPresentation.y
  dyadicZ P := A.dyadic P Dyadic.ArithmeticPresentation.z
  cap := A.cap

end SourceLifts

/-- The free retained map: generator `i ↦ (eᵢ, 0)` (free universal property). -/
def retainedFree : Source →ₜ* Retained.Q :=
  (FiniteFreeProTwo.isFree 8).liftHom Retained.hasPGroupOpenNormalBasis
    (fun i => ⟨Pi.single i 1,0⟩) continuous_of_discreteTopology

@[simp] theorem retainedFree_generator (i : Fin 8) :
    retainedFree (FiniteFreeProTwo.generator 8 i) = ⟨Pi.single i 1,0⟩ :=
  (FiniteFreeProTwo.isFree 8).liftHom_apply Retained.hasPGroupOpenNormalBasis
    (fun i => ⟨Pi.single i 1,0⟩) continuous_of_discreteTopology i

namespace SourceLifts
variable (A : SourceLifts)

/-- The label facts: elementary vectors of the lifts. -/
abbrev Labels : Prop := A.lifts.Labels (fun g => (retainedFree g).base)

/-- The seven presentation relators: `c₁², c₂²`, the tame words at
`𝔮₁, 𝔮₂, 𝔯₁, 𝔯₂` and the lifted genuine relation at `𝔭₂`. -/
def relators (r : LocalSource) : Fin 7 → Source :=
  ![A.conj 0^2,A.conj 1^2,
    Lifts.tameWord (tameNorm 0) (A.tameInertia 0) (A.tameFrobenius 0),
    Lifts.tameWord (tameNorm 1) (A.tameInertia 1) (A.tameFrobenius 1),
    Lifts.tameWord (tameNorm 2) (A.tameInertia 2) (A.tameFrobenius 2),
    Lifts.tameWord (tameNorm 3) (A.tameInertia 3) (A.tameFrobenius 3),
    A.dyadic 1 r]

/-- The arithmetic presentation hypothesis: the genuine relation at the
distinguished place `𝔭₁` is a consequence of the seven relators. -/
def Presentation (r : LocalSource) : Prop :=
  A.dyadic 0 r ∈ closedNormalClosure (Set.range (A.relators r))

/-- The cut kernel: closed normal closure of the thirty literal words. -/
def kernel : Subgroup Source := closedNormalClosure A.lifts.words

instance kernel_normal : (A.kernel).Normal := inferInstanceAs (closedNormalClosure _).Normal

instance kernel_isClosed : IsClosed (A.kernel : Set Source) := closedNormalClosure_isClosed _

/-- The cut quotient of the free source. -/
abbrev ActualQuotient := Source ⧸ A.kernel

def projection : Source →ₜ* A.ActualQuotient :=
  ⟨QuotientGroup.mk' A.kernel,QuotientGroup.continuous_mk⟩

theorem projection_surjective : Function.Surjective A.projection := QuotientGroup.mk'_surjective _

theorem projection_eq_one_of_mem {g : Source} (hg : g ∈ A.kernel) : A.projection g = 1 :=
  (QuotientGroup.eq_one_iff g).mpr hg

theorem word_mem_kernel {g : Source} (hg : g ∈ A.lifts.words) : g ∈ A.kernel :=
  subset_closedNormalClosure _ hg

theorem quadratic_mem_kernel (i : Fin 21) : A.lifts.quadraticWords i ∈ A.kernel :=
  A.word_mem_kernel (Or.inl (Or.inl ⟨i,rfl⟩))

theorem cubic_mem_kernel (P : Fin 2) : A.lifts.cubicWords P ∈ A.kernel :=
  A.word_mem_kernel (Or.inl (Or.inr ⟨P,rfl⟩))

theorem deep_mem_kernel (i : Fin 7) : A.lifts.deepWords i ∈ A.kernel :=
  A.word_mem_kernel (Or.inr ⟨i,rfl⟩)

/-- The retained map descends to the cut quotient. -/
def retained (hL : A.Labels) : A.ActualQuotient →ₜ* Retained.Q :=
  ProCGroups.QuotientGroup.liftₜ A.kernel retainedFree
    (Retained.closedNormalClosure_le_ker retainedFree A.lifts hL)

@[simp] theorem retained_projection (hL : A.Labels) (g : Source) :
    A.retained hL (A.projection g) = retainedFree g := rfl

end SourceLifts
end UnitDistance.Sqrt241.Cut
