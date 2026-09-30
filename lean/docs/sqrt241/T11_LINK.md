# T11: the dyadic link `√β₁ ∈ M` and `hdiscM`

Owner: T11 agent. Directory: `UnitDistance/Sqrt241/DyadicLink/`. Plan:
[TOWER_PLAN.md](TOWER_PLAN.md) §3 T11; data and route E: [E_RD_DATA.md](E_RD_DATA.md),
[E_ROOTDISC.md](E_ROOTDISC.md). Rules: [CONVENTIONS.md](CONVENTIONS.md).

## Status (2026-09-29): done, unconditional

All six modules compile (`lake build UnitDistance.Sqrt241.DyadicLink.All`, ≈ 25 s after
the dependencies). Every declaration listed below depends only on `propext`,
`Classical.choice`, `Quot.sound` (`#print axioms` from the scratch file
`…/scratchpad/t11/Axioms.lean`, outside the repository). No `sorry`, `admit`, `axiom`,
`native_decide`; the finite checks use `decide +kernel`.

**For T12:** in `UnitDistance.Sqrt241.target_of_tower_data` take
`M := ↥Retained.input.M`, `[Algebra CanonicalGenus.Carrier M] := Retained.input.genusAlgebra`
and

```lean
hdiscM := UnitDistance.Sqrt241.DyadicLink.log_rootDiscriminant_input_M
-- : Real.log (NumberFieldAnalysis.rootDiscriminant ↥Retained.input.M) ≤ Witness.logRD
```

(`hdiscM` does not involve the algebra instance.) No parameter is left open.

## Goal

`hdiscM : Real.log (NumberFieldAnalysis.rootDiscriminant M) ≤ Witness.logRD` of
`target_of_tower_data` (`Assembly.lean`) for the retained field `M = Ω^core`
(T9, `Retained/Field.lean`), via stream E's
`UnitDistance.Sqrt241.log_rootDiscriminant_le_of_sqrt_beta₁`.

## Route decision (route E, not route T)

Both routes need the same ramification data of `M` (`e = 8, 2, 2, 2` at `2, 3, 5, 241`,
unramified elsewhere), now supplied by T10.

* **Route T** (`Discriminant.log_rootDiscriminant_le_of_retained_comparison`) needs in
  addition a Galois field `L ⊇ M, R_ℚ` with `e₂(L) = 8`. The natural `L` is the
  compositum `M · R_ℚ` in `AlgebraicClosure ℚ`; it is *not* inside `Ω` (`R_ℚ` is
  ramified outside `{2,3,5,241}`), so T10's local-index results for fields between `M`
  and `Ω` do not apply to it. `e₂(L) = 8` needs (a) the cut factorization of the
  dyadic decomposition map of `M` through `Local.dyadicCutD` (`dyadicCutD d = 1 ⇒
  d ∈ kernelHat ≤ core`), (b) T5's `retained_restriction_eq_one_iff` for `R_ℚ`, and
  (c) the ℚ package's absolute-image-cardinality API applied to `L` (construction of
  `L`, its algebra structures from `M` and `R_ℚ`, the inertia image of the diagonal).
* **Route E** needs only `√β₁ ∈ M`, a purely global statement: Kummer theory of one
  explicit `D₄`-radical over `B`, a finite `F₂` check against T7's retained cocycle,
  and the free universal property. No local choice, no `R_ℚ`, no chosen places.

Route E was chosen (independent of the dyadic bookkeeping and of the ℚ package's
local API; ≈ 970 lines, self-contained).

## Mathematics (as formalized)

* `β₁ = a + b γ`, `a = -25 + 2√241`, `b = -139 - 9√241`, `γ = √π₂' = genusRoot 3`,
  `β̄₁ = a - b γ`; `β₁ β̄₁ = a² - b² π₂' = π₃' = α₅` (exact identity, `beta_mul_betaBar`).
* **(1) `√β₁ ∈ Ω`.** `F₁ = B(√α₃, √α₅) = quadField 3 ⊔ quadField 5` is admissible. If
  `t = √β₁ ∈ F₁`, done. Otherwise `β₁` is a non-square in `F₁`, `K = F₁(t)` is Galois
  over `B` (every `B`-conjugate of `t` is `±t` or `±√α₅/t`), `[K:B] = 2 [F₁:B]` (a
  2-group), and `K/B` is unramified outside `S`: `F₁/B` is, and `K/F₁` at every prime
  not above `30` by `QuadraticRamification.isUnramifiedAt_of_not_mem` (`2` is a unit,
  and `β₁` is a unit since `β₁ β̄₁ = α₅`); transitivity by
  `Algebra.IsUnramifiedAt.comp`. So `K ≤ Ω` (`Tower.le_OmegaBcl_of_admissible`).
* **(2) Kummer cocycle.** For `g ∈ G_B` with label `v`: `ref 0 = t`, `ref 1 = s/t`
  (`s = √α₅`), `g t = (-1)^{c(g)} ref(v₃)`, and `c(gh) = c(g) + c(h) + v₅ w₃`.
  So `Ψ(g) = (v, c(g))` is a continuous homomorphism `G_B → F₂⁸ ×_{β₃₅} F₂`,
  `β₃₅(v, w) = v₅ w₃`; `g²` acts by `(-1)^{v₃ v₅}`, `[g,h]` by `(-1)^{v₅w₃ + v₃w₅}`.
* **(3) Finite check.** Coordinate 13 of `Retained.cocycle` is exactly `v₅ w₃`
  (from `retainedCocycleMasks`). Equivalently: universal coordinate 27 (pair `(3,5)`,
  the functional `x₃x₅`) vanishes on the 21 cut initials, equals `v₅ w₃` on the
  universal cocycle, and `Retained.reduction` maps it to coordinate 13.
* **(4) Comparison.** `Ψ ∘ freeMap = Φ_c ∘ Cut.retainedFree` with
  `Φ_c(v, w) = (v, w₁₃ + ⟨c, v⟩)`, `c_i = c(gen i)` (both continuous, equal on the
  generators of the free pro-2 group, `IsFreeProCGroup.hom_ext`). Hence
  `retainedFree f = 1 ⇒ freeMap f` fixes `√β₁`.
* **(5)** `core ≤ retainedKer` and `retainedMap ∘ freeMap = retainedFree` give
  `√β₁ ∈ M`; stream E's theorem then gives `hdiscM` from the ramification indices,
  which T10 proves for `Retained.input.M`.

## Delivered (namespace `UnitDistance.Sqrt241.DyadicLink`)

### `DyadicLink/Radical.lean` — step 1
```lean
theorem isUnramifiedAtFinitePlacesOutside_trans {k K F} [..] [IsScalarTower k K F] {T}
    (hkK : IsUnramifiedAtFinitePlacesOutside k K T)
    (hKF : ∀ P : HeightOneSpectrum (𝓞 F), finitePlaceBelow (K := k) P ∉ T →
      Algebra.IsUnramifiedAt (𝓞 K) P.asIdeal) :
    IsUnramifiedAtFinitePlacesOutside k F T                     -- generic tower lemma
def aInt bInt : 𝓞 B                                             -- -25 + 2√241, -139 - 9√241
def beta : Closure := (-25 + 2 * baseRoot) + (-139 - 9 * baseRoot) * genusRoot 3
def betaBar : Closure := (-25 + 2 * baseRoot) - (-139 - 9 * baseRoot) * genusRoot 3
theorem beta_mul_betaBar : beta * betaBar = radicand 5
def sqrtBeta : Closure := squareRoot beta ; theorem sqrtBeta_sq : sqrtBeta ^ 2 = beta
theorem sq_genusRoot_div_sqrtBeta : (genusRoot 5 / sqrtBeta) ^ 2 = betaBar
def F1 : IntermediateField B Closure := quadField 3 ⊔ quadField 5
  -- instances FiniteDimensional, IsGalois, NumberField; F1_isPGroup, F1_unramified, F1_le_OmegaBcl
def gammaO betaO betaBarO : 𝓞 F1 ; theorem betaO_mul_betaBarO : betaO * betaBarO = algebraMap (𝓞 B) (𝓞 F1) (alpha 5)
def K1 : IntermediateField F1 Closure := adjoin F1 {sqrtBeta}
theorem K1_unramifiedAt (h : sqrtBeta ∉ F1) (P) (hP : finitePlaceBelow (K := B) P ∉ S) :
    Algebra.IsUnramifiedAt (𝓞 F1) P.asIdeal                     -- Kummer step
def Kfield : IntermediateField B Closure := K1.restrictScalars B   -- instances Normal, IsGalois
theorem Kfield_isPGroup (h) ; Kfield_unramified (h) ; sigma_sqrtBeta_mem (σ : Closure ≃ₐ[B] Closure)
theorem sqrtBeta_mem_OmegaBcl : sqrtBeta ∈ OmegaBcl
theorem sqrtBeta_mem_Omega : sqrtBeta ∈ Omega
```

### `DyadicLink/Kummer.lean` — step 2
```lean
def tOm : Omega := ⟨sqrtBeta, sqrtBeta_mem_Omega⟩ ; aOm bOm : Omega
theorem tOm_sq : tOm ^ 2 = aOm + bOm * genusRootOmega 3
def ref (x : ZMod 2) : Omega            -- ref 0 = tOm, ref 1 = genusRootOmega 5 * tOm⁻¹
def kummerChar (g : GB) : ZMod 2
theorem kummerChar_action (g : GB) :
    (g : Ghat) tOm = binarySign (kummerChar g) * ref ((genusLabel g).toAdd 3)
theorem kummerChar_mul (g h : GB) : kummerChar (g * h) =
    kummerChar g + kummerChar h + (genusLabel g).toAdd 5 * (genusLabel h).toAdd 3
theorem kummerChar_sq (g) : kummerChar (g ^ 2) = (genusLabel g).toAdd 3 * (genusLabel g).toAdd 5
theorem kummerChar_commutator (g h) : kummerChar (g⁻¹ * h⁻¹ * g * h) =
    (genusLabel g).toAdd 5 * (genusLabel h).toAdd 3 + (genusLabel g).toAdd 3 * (genusLabel h).toAdd 5
def kummerForm : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2) →ₗ[ZMod 2] ZMod 2   -- v₅ w₃
abbrev KummerQ := GroupModel kummerForm   -- discrete; kummerQ_hasPGroupOpenNormalBasis
def kummerMap : GB →ₜ* KummerQ            -- g ↦ ⟨(genusLabel g).toAdd, kummerChar g⟩
theorem fixes_tOm_of_kummerMap_eq_one {g : GB} (hg : kummerMap g = 1) : (g : Ghat) tOm = tOm
```

### `DyadicLink/Comparison.lean` — steps 3 and 4
```lean
theorem retained_cocycle_thirteen (v w : V) : Retained.cocycle v w 13 = v 5 * w 3
theorem relationVector_pair35 : ∀ i : Fin 21, Retained.relationVector i 27 = 0   -- x₃x₅ ⊥ cut initials
theorem universal_cocycle_pair35 (v w : V) : Universal.cocycle v w 27 = v 5 * w 3
theorem reduction_thirteen (w : Universal.W) : Retained.reduction w 13 = w 27
def retainedToKummer (c : V) : Retained.Q →* KummerQ     -- (v, w) ↦ (v, w 13 + ∑ i, c i * v i)
def genChar : V := fun i => kummerChar (gen i)
theorem kummerMap_freeMap (f : Cut.Source) :
    kummerMap (freeMap f) = retainedToKummer genChar (Cut.retainedFree f)
theorem freeMap_fixes_sqrtBeta (f : Cut.Source) (hf : Cut.retainedFree f = 1) :
    ((freeMap f : GB) : Ghat) tOm = tOm
theorem fixes_sqrtBeta_of_retained (ρ : GB →* Retained.Q)
    (hρ : ∀ f, ρ (freeMap f) = Cut.retainedFree f) {g : GB} (hg : ρ g = 1) : (g : Ghat) tOm = tOm
```

### `DyadicLink/RetainedField.lean` — step 5 for any `I : Retained.Input`
```lean
theorem coe_beta₁ : ((Discriminant.beta₁ : CanonicalGenus.Carrier) : Closure) = beta
theorem retainedKer_fixes_tOm (I) {σ : Ghat} (hσ : σ ∈ I.retainedKer) : σ tOm = tOm
theorem tOm_mem_M (I : Retained.Input) : tOm ∈ I.M
def sqrtBetaM (I) : I.M ; theorem sqrtBetaM_sq (I) : sqrtBetaM I ^ 2 = I.genusToM Discriminant.beta₁
theorem log_rootDiscriminant_M_le (I : Retained.Input)
    (he2 : (rationalPrimeIdeal 2).ramificationIdxIn (𝓞 I.M) = 8)
    (he3 : (rationalPrimeIdeal 3).ramificationIdxIn (𝓞 I.M) = 2)
    (he5 : (rationalPrimeIdeal 5).ramificationIdxIn (𝓞 I.M) = 2)
    (he241 : (rationalPrimeIdeal 241).ramificationIdxIn (𝓞 I.M) = 2)
    (hunr : ∀ p : ℕ, p.Prime → p ∉ ({2, 3, 5, 241} : Finset ℕ) →
      (rationalPrimeIdeal p).ramificationIdxIn (𝓞 I.M) = 1) :
    Real.log (rootDiscriminant I.M) ≤ Witness.logRD
theorem log_rootDiscriminant_input_M_le (he2 he3 he5 he241 hunr for Retained.input.M) : …
```

### `DyadicLink/Concrete.lean` — the unconditional `hdiscM`
```lean
theorem log_rootDiscriminant_input_M :
    Real.log (rootDiscriminant Retained.input.M) ≤ Witness.logRD
```
Uses T10 (`Levels/LocalData.lean`, `Levels/Unramified.lean`):
`Retained.Input.Admissible.local_types Retained.input.admissible_M` (indices at 2, 3, 5),
`Retained.ramificationIdxIn_241` with `Retained.BinOmega_le_of_admissible`,
`Retained.ramificationIdxIn_eq_one_away`. If T10 renames these, only this 45-line
module needs updating; `log_rootDiscriminant_M_le` keeps the parametric form.

`DyadicLink/All.lean` imports all five.

## Rebuild

    ./.toolchain/bin/lake build UnitDistance.Sqrt241.DyadicLink.All

Axiom check: `lake env lean` on a scratch file importing
`UnitDistance.Sqrt241.DyadicLink.All` with `#print axioms` for the declarations above.

## Notes

* `sqrtBeta` is `CanonicalGenus.squareRoot beta` (a chosen root); stream E's hypothesis
  `hs₁` does not depend on the sign.
* The proof of `√β₁ ∈ Ω` does not decide whether `β₁` is a square in `F₁` (it is not,
  by PARI: `[F₁(√β₁):ℚ] = 16`); both cases are handled.
* The same argument applies verbatim to `√β₂` (not needed: stream E's
  `log_rootDiscriminant_le_of_sqrt_beta₁` recovers it by Galois conjugation).
