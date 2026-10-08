module

public import UnitDistance.Sqrt241.Geometry.FixedBaseBridge

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Version 2: the tower data for fields that need not be Galois over `ℚ`

In the 41-cap tower only one prime of `B = ℚ(√241)` above 41 is capped, so the tower
fields `K_j` are Galois over `B` but not, in general, over `ℚ`. Version 1's
`Retained.TowerData` (`Levels/Export.lean`) states local types at rational primes, which
needs `IsGalois ℚ (Ks j)`. `V2.TowerData` replaces them by **windows**: for each witness
index `a`, the primes of `K_j` of absolute norm `Witness.primeNorm a` that contain a chosen
element `window j a` fixed by the complex conjugation. For `a = 0, …, 3`
(`2, 3, 5, 29`) the element can be `0`, and the window is the whole norm fiber; for
`a = 4` (`41`) it is `√241 − r` with `r² ≡ 241 (mod 41)`, which selects the primes above
the capped prime of `B`.

The counting hypothesis `window_count` is the form the planar construction uses: the
window carries the weight `e_a f_a` of `Witness`, so for `41` (effective type `(2,4)`)
the window has `[K_j:ℚ]/8` primes, each of norm `41⁴`.

The signature is controlled through a second field `D ⊆ K_j`, Galois over `ℚ` (in the
concrete data version 1's `Retained.Input.detectorField`): the restriction `cD` of the
complex conjugation has centralizer index at least `2^16` in `Gal(D/ℚ)` (version 1's
`Retained.Input.centralizer_index`), and `hcD` says that `c j` restricts to `cD`.

This module contains definitions only.
-/

noncomputable section

open NumberField IsDedekindDomain Filter

namespace UnitDistance.Sqrt241.V2

open UnitDistance.NumberFieldAnalysis

/-- The primes of `K` of absolute norm `q` that contain `x`. -/
abbrev WindowFiber (K : Type*) [Field K] [NumberField K] (q : ℕ) (x : 𝓞 K) :=
  {P : HeightOneSpectrum (𝓞 K) // Ideal.absNorm P.asIdeal = q ∧ x ∈ P.asIdeal}

/-- **Version 2 tower data**: a fixed base `M`, Galois over `ℚ`, and growing number fields
`K_j ⊇ M`, unramified over `M` at the finite primes, with a complex conjugation, windows at
the five witness indices, and a Galois-over-`ℚ` subfield `D` controlling the signature. -/
structure TowerData where
  M : Type
  [instField : Field M]
  [instNumberField : NumberField M]
  [instIsGalois : IsGalois ℚ M]
  Ks : ℕ → Type
  [instFieldK : ∀ j, Field (Ks j)]
  [instNumberFieldK : ∀ j, NumberField (Ks j)]
  [instAlgebraMK : ∀ j, Algebra M (Ks j)]
  φ : ∀ j, Ks j →+* ℂ
  c : ∀ j, Ks j ≃ₐ[ℚ] Ks j
  hc : ∀ j, NumberField.ComplexEmbedding.IsConj (φ j) (c j)
  hc1 : ∀ j, c j ≠ 1
  D : Type
  [instFieldD : Field D]
  [instNumberFieldD : NumberField D]
  [instIsGaloisD : IsGalois ℚ D]
  [instAlgebraDK : ∀ j, Algebra D (Ks j)]
  cD : D ≃ₐ[ℚ] D
  hcD : ∀ j (x : D), c j (algebraMap D (Ks j) x) = algebraMap D (Ks j) (cD x)
  hindexD : 65536 ≤ (Subgroup.centralizer ({cD} : Set (D ≃ₐ[ℚ] D))).index
  hdegree : Tendsto (fun j => Module.finrank ℚ (Ks j)) atTop atTop
  hunrM : ∀ j, FiniteUnramified M (Ks j)
  window : ∀ j, Fin 5 → 𝓞 (Ks j)
  window_fixed : ∀ j a, RingOfIntegers.mapRingHom (c j).toRingHom (window j a) = window j a
  window_count : ∀ j a,
    Nat.card (WindowFiber (Ks j) (Witness.primeNorm a) (window j a)) *
      (Witness.ramification a * Witness.residueDegree a) = Module.finrank ℚ (Ks j)
  window_free : ∀ j a (P : WindowFiber (Ks j) (Witness.primeNorm a) (window j a)),
    Ideal.map (RingOfIntegers.mapRingHom (c j).toRingHom) P.1.asIdeal ≠ P.1.asIdeal
  r3 : M
  hr3 : r3 ^ 2 = 3
  ii : M
  hii : ii ^ 2 = -1

attribute [instance] TowerData.instField TowerData.instNumberField TowerData.instIsGalois
  TowerData.instFieldK TowerData.instNumberFieldK TowerData.instAlgebraMK
  TowerData.instFieldD TowerData.instNumberFieldD TowerData.instIsGaloisD TowerData.instAlgebraDK

end UnitDistance.Sqrt241.V2
