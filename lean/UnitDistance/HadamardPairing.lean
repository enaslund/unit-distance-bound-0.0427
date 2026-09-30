/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import UnitDistance.Upstream.Hadamard.HadamardProduct.LogDerivative
public import UnitDistance.Upstream.Hadamard.HadamardProduct.PairedGenusOne

@[expose] public section
set_option backward.privateInPublic true


/-! Selected exact negation-pairing definitions and reindexing proof from
PairedCanonicalProductGrowth.lean. Dyadic growth and counting are omitted. Internal imports relocated.
Source commit: 753938937e624d1c8bbe4c208517660a672d1b8e.
See third-party/entire-hadamard for provenance and license. -/

open Filter Metric Real Set Topology
open scoped Real

namespace OverflowResidueRH

universe u

/-! ## A reusable exact pairing interface -/

/-- One representative from every orbit of a fixed-point-free involution,
using an arbitrary linear order. -/
def involutionHalf {ι : Type u} [LinearOrder ι] (e : ι ≃ ι) : Type u :=
  {i : ι // i < e i}

/-- A fixed-point-free involution decomposes its index type into one
representative and one opposite representative per Boolean fiber. -/
def involutionPairEquiv {ι : Type u} [LinearOrder ι]
    (e : ι ≃ ι) (hinv : Function.Involutive e) (hfree : ∀ i, e i ≠ i) :
    involutionHalf e × Bool ≃ ι where
  toFun p := if p.2 then e p.1.1 else p.1.1
  invFun i := if hi : i < e i then (⟨i, hi⟩, false)
    else (⟨e i, by
      have hle : e i ≤ i := le_of_not_gt hi
      have hne : e i ≠ i := hfree i
      have hlt : e i < i := lt_of_le_of_ne hle hne
      simpa [hinv i] using hlt⟩, true)
  left_inv p := by
    rcases p with ⟨⟨i, hi⟩, b⟩
    cases b with
    | false => simp [hi]
    | true =>
        have hnot : ¬ e i < i := not_lt_of_ge hi.le
        simp [hnot, hinv i]
  right_inv i := by
    by_cases hi : i < e i
    · simp [hi]
    · have hle : e i ≤ i := le_of_not_gt hi
      have hne : e i ≠ i := hfree i
      have hlt : e i < i := lt_of_le_of_ne hle hne
      simp [hi, hinv i]

/-- Exact divisor data for choosing one representative from each
`ρ, -ρ` pair. -/
structure HadamardNegationPairingData
    {ι : Type u} (zeroLoc : ι → ℂ) where
  half : Type u
  pairEquiv : half × Bool ≃ ι
  loc_true : ∀ j, zeroLoc (pairEquiv (j, true)) =
    -zeroLoc (pairEquiv (j, false))

/-- The selected location in one negation orbit. -/
def HadamardNegationPairingData.repLoc
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardNegationPairingData zeroLoc) (j : H.half) : ℂ :=
  zeroLoc (H.pairEquiv (j, false))

/-- Construct exact pairing data from a fixed-point-free location-negating
involution.  The choice of half is noncanonical but the reconstructed full
product is not. -/
noncomputable def HadamardNegationPairingData.ofInvolution
    {ι : Type*} (zeroLoc : ι → ℂ)
    (e : ι ≃ ι) (hinv : Function.Involutive e) (hfree : ∀ i, e i ≠ i)
    (hloc : ∀ i, zeroLoc (e i) = -zeroLoc i) :
    HadamardNegationPairingData zeroLoc := by
  classical
  letI : LinearOrder ι := linearOrderOfSTO WellOrderingRel
  exact
    { half := involutionHalf e
      pairEquiv := involutionPairEquiv e hinv hfree
      loc_true := by
        intro j
        simpa [involutionPairEquiv] using hloc j.1 }

/-- The quadratic canonical product over one representative from each
opposite pair. -/
noncomputable def pairedQuadraticProduct
    {κ : Type*} (repLoc : κ → ℂ) (z : ℂ) : ℂ :=
  ∏' j : κ, (1 - (z / repLoc j) ^ 2)

private theorem tprod_reindex_bool_pairs
    {ι κ : Type*} (f : ι → ℂ) (e : κ × Bool ≃ ι)
    (hf : Multipliable f) :
    (∏' i : ι, f i) =
      ∏' j : κ, (f (e (j, false)) * f (e (j, true))) := by
  let g : κ × Bool → ℂ := fun p ↦ f (e p)
  have hg : Multipliable g := (e.multipliable_iff).2 hf
  have hgb : ∀ j : κ, Multipliable (fun b : Bool ↦ g (j, b)) := by
    intro j
    exact Multipliable.of_finite
  calc
    (∏' i : ι, f i) = ∏' p : κ × Bool, g p :=
      (e.tprod_eq f).symm
    _ = ∏' j : κ, ∏' b : Bool, g (j, b) := hg.tprod_prod' hgb
    _ = ∏' j : κ, (f (e (j, false)) * f (e (j, true))) := by
      simp only [tprod_bool, g]

/-- Exact reindexing of the full genus-one product as a quadratic paired
product.  Multipliability is used explicitly, so no regrouping of a
nonconvergent totalized product is hidden. -/
theorem HadamardNegationPairingData.infiniteHadamardProduct_eq_paired
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardNegationPairingData zeroLoc)
    (Hinv : HadamardZeroInvSqSummability zeroLoc) (z : ℂ) :
    infiniteHadamardProduct zeroLoc z =
      pairedQuadraticProduct H.repLoc z := by
  unfold infiniteHadamardProduct pairedQuadraticProduct
  rw [tprod_reindex_bool_pairs
    (fun i ↦ hadamardGenus1Factor (zeroLoc i) z) H.pairEquiv
    (Hinv.product_multipliable z)]
  apply tprod_congr
  intro j
  dsimp [HadamardNegationPairingData.repLoc]
  rw [H.loc_true]
  exact hadamardGenus1Factor_mul_neg_location
    (Hinv.zero_ne (H.pairEquiv (j, false)))


end OverflowResidueRH
