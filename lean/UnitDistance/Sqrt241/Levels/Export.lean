module

public import UnitDistance.Sqrt241.Levels.Census
public import UnitDistance.Sqrt241.Assembly
public import UnitDistance.RationalGaloisAlgebra

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false

/-!
# Export: the tower data of `target_of_tower_data`

`TowerData` packages exactly the hypotheses of `UnitDistance.Sqrt241.target_of_tower_data`
(`Assembly.lean`) other than the root discriminant `hdiscM` (`Discriminant/`, `DyadicLink/`)
and the analytic hypothesis `H`, in the same forms. `towerData : TowerData` is built from
the concrete input (`Retained.input`, built from `Local.localElements`):

* `M = input.M` (`Ω^core`), with `genusAlgebra : Algebra E M`, `√3`, `√−1`, and the exact
  local types `(8,4)`, `(1,4)`, `(1,8)` at `2, 29, 7` and `f = 4` at the census primes;
* `Ks j = input.level j`, `φ j = phi₁|K_j`, `c j = c₁|K_j`, the algebra `M → K_j` by
  inclusion; all eventual hypotheses hold for every `j`.

The `ℚ`-algebra structures on `↥M` and `↥K_j` used by `TowerData` are the canonical
`DivisionRing.toRatAlgebra`; the constructions use the intermediate-field structures, and
`RationalGalois` transports between them (as in the ℚ package).

`TowerData.target` and `target_of_retained_tower` apply `target_of_tower_data`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UnitDistance.Sqrt241.Retained

open Tower Presentation Cut GroupData ProCGroups UnitDistance.PrimeCompletion
open _root_.UnitDistance.Sqrt241.Local _root_.UnitDistance.NumberFieldAnalysis NumberField Filter

/-- **The tower data**: every hypothesis of `target_of_tower_data` except `hdiscM` and `H`. -/
structure TowerData where
  M : Type
  [instField : Field M]
  [instNumberField : NumberField M]
  [instIsGalois : IsGalois ℚ M]
  [instAlgebraE : Algebra CanonicalGenus.Carrier M]
  Ks : ℕ → Type
  [instFieldK : ∀ j, Field (Ks j)]
  [instNumberFieldK : ∀ j, NumberField (Ks j)]
  [instIsGaloisK : ∀ j, IsGalois ℚ (Ks j)]
  [instAlgebraMK : ∀ j, Algebra M (Ks j)]
  φ : ∀ j, Ks j →+* ℂ
  c : ∀ j, Gal(Ks j/ℚ)
  hc : ∀ j, NumberField.ComplexEmbedding.IsConj (φ j) (c j)
  hc1 : ∀ j, c j ≠ 1
  hdegree : Tendsto (fun j => Module.finrank ℚ (Ks j)) atTop atTop
  hunrM : ∀ᶠ j in atTop, NumberFieldAnalysis.FiniteUnramified M (Ks j)
  he : ∀ᶠ j in atTop, ∀ a : Fin 5,
    (NumberFieldAnalysis.rationalPrimeIdeal (Witness.primes a)).ramificationIdxIn
      (𝓞 (Ks j)) = Witness.ramification a
  hf : ∀ᶠ j in atTop, ∀ a : Fin 5,
    (NumberFieldAnalysis.rationalPrimeIdeal (Witness.primes a)).inertiaDegIn
      (𝓞 (Ks j)) = Witness.residueDegree a
  hfree : ∀ᶠ j in atTop, ∀ (a : Fin 5)
    (P : NumberFieldAnalysis.PrimeNormFiber (Ks j) (Witness.primeNorm a)),
      Ideal.map (RingOfIntegers.mapRingHom (c j).toRingHom) P.1.asIdeal ≠ P.1.asIdeal
  hindex : ∀ᶠ j in atTop, 65536 ≤ (Subgroup.centralizer (Set.singleton (c j))).index
  r3 : M
  hr3 : r3 ^ 2 = 3
  ii : M
  hii : ii ^ 2 = -1
  h2 : (NumberFieldAnalysis.rationalPrimeIdeal 2).ramificationIdxIn (𝓞 M) = 8 ∧
    (NumberFieldAnalysis.rationalPrimeIdeal 2).inertiaDegIn (𝓞 M) = 4
  h29 : (NumberFieldAnalysis.rationalPrimeIdeal 29).ramificationIdxIn (𝓞 M) = 1 ∧
    (NumberFieldAnalysis.rationalPrimeIdeal 29).inertiaDegIn (𝓞 M) = 4
  h7 : (NumberFieldAnalysis.rationalPrimeIdeal 7).ramificationIdxIn (𝓞 M) = 1 ∧
    (NumberFieldAnalysis.rationalPrimeIdeal 7).inertiaDegIn (𝓞 M) = 8
  hcensus : ∀ p ∈ ({41, 47, 53, 59, 61, 67, 79, 83, 97} : Finset ℕ),
    4 ≤ (NumberFieldAnalysis.rationalPrimeIdeal p).inertiaDegIn (𝓞 M)

attribute [instance] TowerData.instField TowerData.instNumberField TowerData.instIsGalois
  TowerData.instAlgebraE TowerData.instFieldK TowerData.instNumberFieldK
  TowerData.instIsGaloisK TowerData.instAlgebraMK

/-- `target_of_tower_data` from the tower data, the root discriminant of `M` and `H`. -/
theorem TowerData.target (T : TowerData)
    (hdiscM : Real.log (NumberFieldAnalysis.rootDiscriminant T.M) ≤ Witness.logRD)
    (H : Real.log (dedekindZeta CanonicalGenus.Carrier
          ((1 + (1 / 300 : ℝ) : ℝ) : ℂ)).re / (512 : ℝ) + (1 / 300 : ℝ) *
        ((Witness.logRD - Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 4 -
          (logDeriv (dedekindZeta CanonicalGenus.Carrier) 2).re / (512 : ℝ)) <
        852 / 10000) :
    Target :=
  target_of_tower_data T.M T.Ks T.φ T.c T.hc T.hc1 T.hdegree T.hunrM T.he T.hf T.hfree T.hindex
    hdiscM T.r3 T.hr3 T.ii T.hii T.h2 T.h29 T.h7 T.hcensus H

/-! ### The concrete tower data -/

section Concrete

/-- The `ℚ`-automorphisms of a level for the canonical `ℚ`-algebra structure. -/
def levelAut (j : ℕ) :
    Gal(input.level j/ℚ) ≃* @AlgEquiv ℚ (input.level j) (input.level j) _ _ _
      DivisionRing.toRatAlgebra DivisionRing.toRatAlgebra :=
  RationalGalois.autEquiv (input.level j) _ DivisionRing.toRatAlgebra

theorem levelAut_apply (j : ℕ) (σ : Gal(input.level j/ℚ)) (x : input.level j) :
    levelAut j σ x = σ x :=
  RationalGalois.autEquiv_apply _ _ _ _ _

theorem M_types (a : Fin 5) :
    (rationalPrimeIdeal (Witness.primes a)).ramificationIdxIn (𝓞 input.M) =
        Witness.ramification a ∧
      (rationalPrimeIdeal (Witness.primes a)).inertiaDegIn (𝓞 input.M) =
        Witness.residueDegree a :=
  input.admissible_M.local_types a

/-- **The concrete tower data.** -/
def towerData : TowerData where
  M := input.M
  instIsGalois := RationalGalois.isGalois _ _ _ input.M_isGalois
  instAlgebraE := input.genusAlgebra
  Ks j := input.level j
  instIsGaloisK j := RationalGalois.isGalois _ _ _ (input.level_isGalois j)
  instAlgebraMK j := algebraOfLe (input.M_le_level j)
  φ := input.levelPhi
  c j := levelAut j (input.levelConj j)
  hc j := by
    change NumberField.ComplexEmbedding.conjugate _ = _
    apply RingHom.ext
    intro x
    change star (input.levelPhi j x) = input.levelPhi j (levelAut j (input.levelConj j) x)
    rw [levelAut_apply]
    exact ((input.levelConj_isConj j).eq x).symm
  hc1 j := by
    intro h
    apply input.levelConj_ne_one j
    exact (levelAut j).injective (h.trans (levelAut j).map_one.symm)
  hdegree := by
    convert input.level_degree_tendsto using 1
  hunrM := Eventually.of_forall fun j => finiteUnramified_of_admissible (input.admissible_level j)
  he := Eventually.of_forall fun j a => ((input.admissible_level j).local_types a).1
  hf := Eventually.of_forall fun j a => ((input.admissible_level j).local_types a).2
  hfree := Eventually.of_forall fun j a P => by
    have heq : (levelAut j (input.levelConj j)).toRingHom = (input.levelConj j).toRingHom := by
      apply RingHom.ext
      intro x
      exact levelAut_apply j _ x
    rw [heq]
    exact prime_moved input (input.EOmega_le_M.trans (input.M_le_level j)) a P
  hindex := Eventually.of_forall fun j => by
    have h0 := input.levelConj_index j
    have h1 := GaloisConjugation.centralizer_index_le_of_surjective
      (levelAut j).symm.toMonoidHom (levelAut j).symm.surjective (levelAut j (input.levelConj j))
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at h1
    exact h0.trans h1
  r3 := input.sqrtThree
  hr3 := input.sqrtThree_sq
  ii := input.sqrtNegOne
  hii := input.sqrtNegOne_sq
  h2 := M_types 0
  h29 := M_types 3
  h7 := M_types 4
  hcensus := M_census

theorem towerData_M : towerData.M = input.M := rfl

/-- **The planar target from the root discriminant of `M` and `H`.** -/
theorem target_of_retained_tower
    (hdiscM : Real.log (NumberFieldAnalysis.rootDiscriminant input.M) ≤ Witness.logRD)
    (H : Real.log (dedekindZeta CanonicalGenus.Carrier
          ((1 + (1 / 300 : ℝ) : ℝ) : ℂ)).re / (512 : ℝ) + (1 / 300 : ℝ) *
        ((Witness.logRD - Real.eulerMascheroniConstant - Real.log (4 * Real.pi)) / 4 -
          (logDeriv (dedekindZeta CanonicalGenus.Carrier) 2).re / (512 : ℝ)) <
        852 / 10000) :
    Target :=
  towerData.target hdiscM H

end Concrete

end UnitDistance.Sqrt241.Retained
