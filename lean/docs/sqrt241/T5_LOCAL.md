# T5: local maps into Ω, normalization, labels

Owner: T5 agent. Plan: [TOWER_PLAN.md](TOWER_PLAN.md) §3 T5 (§1.1 items 2, 5, 6,
§1.3, §2.E, §2.F). Rules: [CONVENTIONS.md](CONVENTIONS.md). Directory:
`UnitDistance/Sqrt241/Local/`. Namespace of everything: `UnitDistance.Sqrt241.Local`
(opens `Tower`, `Base`, `CanonicalGenus`, `PrimeCompletion`).

Status (2026-09-29): **T5 done.** All modules below compile (`lake build
UnitDistance.Sqrt241.Local.Elements` builds all of `Local/`); every listed declaration
has axioms `propext, Classical.choice, Quot.sound` (checked with `#print axioms` from a
scratch file outside the repository). No `sorry`/`axiom`/`native_decide`.
**T6 interface filled:** `Local.localElements : Presentation.LocalElements` with
`localElements_relations`, `localElements_labels`, hence (via T6)
`localElements_presentation : localElements.sourceLifts.Presentation genuineRelation`
and `localElements_relators_generate`, unconditional. (The final proof uses
`localElements`, `localElements_relations` and `localElements_labels` through
`Retained.input`; it obtains the presentation as `Retained.Input.hgen` and does not use
`localElements_presentation` itself. See [SUBMISSION.md](SUBMISSION.md).)

## Interface for T6 / T8 / T9 / T10 (`Local/Elements.lean`)

```lean
def localElements : Presentation.LocalElements where
  conj := ![conj₁, conj₂]                  -- labels 93, 163
  tameInertia := tameInertia               -- 16, 32, 64, 128   (𝔮₁, 𝔮₂, 𝔯₁, 𝔯₂)
  tameFrobenius := tameFrobenius           -- 229, 215, 166, 90
  dyadic := dyadicLocal                    -- a 79/129, b 4/8, c 110/158 (𝔭₁/𝔭₂)
  cap := ![frob29 0, frob29 1, ⟨frob7 ^ 2, frob7_sq_mem⟩]   -- 228, 216, 14
theorem localElements_relations : localElements.Relations
theorem localElements_labels : localElements.Labels
theorem localElements_presentation : localElements.sourceLifts.Presentation genuineRelation
theorem localElements_relators_generate :
    closedNormalClosure (Set.range (localElements.sourceLifts.relators genuineRelation)) = relationKernel
theorem genusLabel_of_hasLabelHat (g : GB) (v) (hg : HasLabelHat (g : Ghat) v) : genusLabel g = ofAdd v
theorem genusLabel_conj (g : GB) : genusLabel (conjGB sigmaHat g) = ofAdd (sigmaMatrix (genusLabel g).toAdd)
def placeIndex : Fin 4 → Fin 2 := ![dyadicPlace, place3, place5, place29]
def localMap (k : Fin 4) (P : Fin 2) : AbsoluteDecomposition (splitPrime k) →ₜ* GB   -- normalized
-- σ̂-stability (second-prime data are G_B-conjugates of σ̂-conjugates of first-prime data):
theorem localMapB_sigma (p hsq P₀) : ∃ h ∈ GB, ∀ d, (localMapB p hsq P₀ 1 d : Ghat) =
    h * (sigmaHat * localMapB p hsq P₀ 0 d * sigmaHat⁻¹) * h⁻¹
theorem dyadicLocal_sigma : ∃ h ∈ GB, ∀ g, (dyadicLocal 1 g : Ghat) = h * (sigmaHat * dyadicLocal 0 g * sigmaHat⁻¹) * h⁻¹
theorem tame_sigma (k : Fin 2) : ∃ h ∈ GB, τ(k,2nd) = h (σ̂ τ(k,1st) σ̂⁻¹) h⁻¹ ∧ φ(k,2nd) = h (σ̂ φ(k,1st) σ̂⁻¹) h⁻¹
theorem frob29_sigma : ∃ h ∈ GB, (frob29 1 : Ghat) = h * (sigmaHat * frob29 0 * sigmaHat⁻¹) * h⁻¹
-- (c₂ = σ̂ c₁ σ̂⁻¹ literally: coe_conj₂; F₇ commutes with (F₇²)⁴.)
```
Local facts beyond the structure, for T8 (local blocks, cut words) and T10 (indices):
tame generation `tame_generates`, the local cut `localCut` / `dyadicCutD` /
`image_cards_of_factor` / `decompositionMapB_factor` (dyadic `e = 8`, `f = 4`),
`decomposition7_range'`, `decomposition29_range'`, `inertia_killed`, `frob7_not_mem`.

## Conventions

* Bit `k` of a genus vector ↔ radicand `α_k` of `[-1, ε, π₂, π₂', π₃, π₃', π₅, π₅']`
  (`CanonicalGenus.radicand k`, root `CanonicalGenus.genusRoot k`); strings like
  `10111010` list `α₀ … α₇` left to right (construction.md §3.4); masks are
  `RetainedQuadratic.binaryVector 8 mask` (bit `k` of `mask` ↔ `α_k`), as in T7/T8.
* **Labels.** `HasLabel (σ : Gal(Closure/ℚ)) (v : Fin 8 → ZMod 2) : Prop :=
  ∀ k, σ (genusRoot k) = binarySign (v k) * genusRoot k` (`Multiquadratic.binarySign`,
  `1 ↦ -1`). In `Ĝ`: `HasLabelHat (g : Ghat) v := ∃ σ, toGhat σ = g ∧ HasLabel σ v`.
  With `E ≤ Ω` (T3's `canonicalGenus_le_Omega`), `HasLabelHat.apply_genusRoot` gives
  the action on `⟨genusRoot k, _⟩`, so T3's `genusLabel g = ofAdd v` follows in one line.
  No T5 statement assumes `E ≤ Ω`.
* Place index `P : Fin 2`: `0` = first prime of `B` (`(π₂)`, `(π₃)`, `(π₅)`, `(π₂₉)`,
  embedding `iotaN`), `1` = second prime (`iotaN'`). The chosen place of the ℚ package
  above `p` lies over `P₀ = dyadicPlace / place3 / place5 / …` (not known in advance).
* Square-class tables at both `p`-adic roots of 241 are the Base stream's
  (`Base/Local.lean` `iotaN_alpha`, `Base/LocalRoots.lean` `algHom_eq_iotaN_or`);
  T5 does not duplicate them.

## Delivered (compiled, axioms clean)

### `Local/Place.lean` — chosen places restricted to `B` (no Ω)
```lean
-- p : Nat.Primes, h : IsSquare (241 : ℚ_[p.val])
def placeRoot (p h) : ℚ_[p.val]                 -- image of √241 at the chosen place
theorem placeRoot_sq ; theorem absoluteEmbedding_baseRoot
def placeEmb (p h) : B →ₐ[ℚ] ℚ_[p.val]          -- the chosen place restricted to B
theorem absoluteEmbedding_coe (p h) (x : B) :
    absoluteEmbedding p (x : Closure) = algebraMap (Base p) _ ((equiv p).symm (placeEmb p h x))
theorem decomposition_fixes_B (p h) (d : AbsoluteDecomposition p) (x : B) : d.val (x : Closure) = x
theorem decomposition_fixes_baseRoot (p h) (d) : d.val baseRoot = baseRoot
abbrev splitPrime : Fin 4 → Nat.Primes := ![2, 3, 5, 29]
theorem isSquare_241_two / _three / _five / _29 ; theorem isSquare_241 (k : Fin 4)
```

### `Local/Conjugation.lean` — labels and the σ-rule (no Ω)
```lean
def HasLabel (g : Closure ≃ₐ[ℚ] Closure) (v : Fin 8 → ZMod 2) : Prop
theorem hasLabel_one ; HasLabel.mul (v + w) ; HasLabel.inv ; HasLabel.pow (n • v) ; HasLabel.unique
def sigmaMatrix (v) : Fin 8 → ZMod 2 := ![v 0, v 0 + v 1, v 0 + v 3, v 0 + v 2, v 5, v 4, v 7, v 6]
theorem sigmaMatrix_sigmaMatrix ; sigmaMatrix_add
theorem hasLabel_conj {s g} (hs : s baseRoot = -baseRoot) (hg : HasLabel g v) :
    HasLabel (s * g * s⁻¹) (sigmaMatrix v)
```

### `Local/DyadicSigns.lean` — dyadic genus signs (no Ω)
```lean
def dyadicSignVector (P : Fin 2) (v : Fin 3 → ZMod 2) : Fin 8 → ZMod 2   -- linear in v
def dyadicMasks : Fin 2 → Fin 3 → ℕ := ![![79, 4, 110], ![129, 8, 158]]
theorem dyadicSignVector_genusBasis (P i) : dyadicSignVector P (genusBasis i).toAdd = binaryVector 8 (dyadicMasks P i)
abbrev prime2 := PadicTwoGlobalMap.prime ; def dyadicEmb : B →ₐ[ℚ] ℚ_[2] ; def dyadicPlace : Fin 2
theorem dyadicEmb_eq_zero (h : dyadicPlace = 0) : dyadicEmb = iota2 ; dyadicEmb_eq_one
theorem globalEmbedding_coe (x : B) : PadicTwoGlobalMap.globalEmbedding (x : Closure) = algebraMap ℚ_[2] _ (dyadicEmb x)
theorem decomposition_genusRoot (σ : PadicTwoMaximalProTwo.AbsoluteGroup) (k) :
    (PadicTwoGlobalMap.decomposition σ).val (genusRoot k) =
      binarySign (dyadicSignVector dyadicPlace (PadicTwoMaximalProTwo.absoluteSigns σ).toAdd k) * genusRoot k
```
Local generators `(a, b, c) = PadicTwoQuadraticRelation.generator 0, 1, 2` (signs of
`rec(-1), rec(5), rec(2)`), `(x, y, z) = (b, a, a·c)`: at `𝔭₁` x `00100000` (4),
y `11110010` (79), z `10000100` (33); at `𝔭₂` x `00010000` (8), y `10000001` (129),
z `11111000` (31).

### `Local/Maps.lean` — maps into Ĝ and G_B, normalization, dyadic map
```lean
def toGhat : Gal(Closure/ℚ) →ₜ* Ghat := ProP.absoluteToNormal ℚ Omega _
theorem toGhat_apply (σ) (x : Omega) : (toGhat σ x : Closure) = σ x ; toGhat_surjective
theorem toGhat_mem_GB_iff (σ) : toGhat σ ∈ GB ↔ σ baseRoot = baseRoot ; toGhat_not_mem_GB_iff
def sigmaLift : Gal(Closure/ℚ) ; theorem toGhat_sigmaLift : toGhat sigmaLift = sigmaHat ; sigmaLift_baseRoot
def HasLabelHat (g : Ghat) (v) : Prop ; HasLabelHat.mul/inv/pow ; hasLabelHat_one
theorem HasLabelHat.conj_sigmaHat (hg : HasLabelHat g v) : HasLabelHat (sigmaHat * g * sigmaHat⁻¹) (sigmaMatrix v)
theorem HasLabelHat.unique (hE : CanonicalGenus.field ≤ Omega) ; HasLabelHat.apply_genusRoot (hE) (hg) (k)
def decompositionMap (p : Nat.Primes) : AbsoluteDecomposition p →ₜ* Ghat    -- = toGhat ∘ val
def decompositionMapB (p h) : AbsoluteDecomposition p →ₜ* GB
def conjGB (g : Ghat) : GB →ₜ* GB                                        -- h ↦ g h g⁻¹
def frame (P₀ P : Fin 2) : Ghat := if P = P₀ then 1 else sigmaHat
def localMapB (p h) (P₀ P : Fin 2) : AbsoluteDecomposition p →ₜ* GB := (conjGB (frame P₀ P)).comp (decompositionMapB p h)
theorem localMapB_hasLabel (p h P₀ P d) (hd : HasLabel d.val v) :
    HasLabelHat (localMapB p h P₀ P d) (if P = P₀ then v else sigmaMatrix v)
def dyadicDecomposition : PadicTwoMaximalProTwo.AbsoluteGroup →ₜ* AbsoluteDecomposition prime2
def dyadicAbsolute : PadicTwoMaximalProTwo.AbsoluteGroup →ₜ* GB
def dyadicLocal (P : Fin 2) : PadicTwoMaximalProTwo.Group →ₜ* GB      -- lift through the pro-2 quotient
@[simp] theorem dyadicLocal_projection (P σ) : dyadicLocal P (projection σ) = conjGB (frame dyadicPlace P) (dyadicAbsolute σ)
theorem dyadicLocal_hasLabel (P g) : HasLabelHat (dyadicLocal P g) (dyadicSignVector P (signs g).toAdd)
theorem dyadicLocal_generator_hasLabel (P i) :
    HasLabelHat (dyadicLocal P (PadicTwoQuadraticRelation.generator i)) (binaryVector 8 (dyadicMasks P i))
```

### `Local/Complex.lean` — c₁, c₂
```lean
def complexEmb : Closure →+* ℂ ; theorem complexEmb_B (b : B) : complexEmb b = complexEmbPlus b
def conjAbs : Gal(Closure/ℚ) ; conjAbs_isConj ; conjAbs_mul_self ; conjAbs_baseRoot
theorem conjAbs_hasLabel : HasLabel conjAbs signPlus
def conj₁ : GB := ⟨toGhat conjAbs, _⟩ ;  def conj₂ : GB := conjGB sigmaHat conj₁
theorem coe_conj₂ : (conj₂ : Ghat) = sigmaHat * conj₁ * sigmaHat⁻¹
theorem conj₁_hasLabel : HasLabelHat conj₁ (binaryVector 8 93)       -- 10111010
theorem conj₂_hasLabel : HasLabelHat conj₂ (binaryVector 8 163)      -- 11000101
theorem conj₁_sq : conj₁ ^ 2 = 1 ; conj₂_sq ; conj₁_mul_self
def phi₁ : Omega →+* ℂ ; theorem phi₁_B (b : B) ; theorem conj₁_isConj : IsConj phi₁ (conj₁ : Ghat)
def phi₂ : Omega →+* ℂ := phi₁ ∘ σ̂⁻¹ ; theorem conj₂_isConj : IsConj phi₂ (conj₂ : Ghat)
```

### `Local/TameLocal.lean`, `Local/TameAbsolute.lean`, `Local/TameData.lean`, `Local/TamePairs.lean` — tame pairs
Generic local lemma (`Tame.exists_generating_tame_pair`: odd `p`, finite Galois 2-extension
`L/ℚ_p`, nonresidue unit radical and ramified radical `w² = p·d_w`), its absolute
finite-level form (`exists_absolute_tame_pair`; labels computed at the chosen place by
absorbing the embedding change into the local roots), the tables, and the profinite
statement by compactness (for every finite Galois layer `F ⊆ Ω`, the finite level is
applied to `F·E`, so `E ≤ Ω` is not needed).
```lean
abbrev tamePrime : Fin 2 → Nat.Primes := ![3, 5] ; def tamePlace : Fin 2 → Fin 2 := ![place3, place5]
def tameIndex (k P : Fin 2) : Fin 4                  -- 𝔮₁ 𝔮₂ 𝔯₁ 𝔯₂ = (0,0) (0,1) (1,0) (1,1)
def tameK : Fin 4 → Fin 2 ; def tameP : Fin 4 → Fin 2
def tameTau (q : Fin 4) := binaryVector 8 (![16, 32, 64, 128] q)
def tamePhi (q : Fin 4) := binaryVector 8 (![229, 215, 166, 90] q)
def tameN : Fin 4 → ℕ := ![3, 3, 5, 5]
def tameDecompositionMap (q) : AbsoluteDecomposition (tamePrime (tameK q)) →ₜ* GB   -- normalized
def tameInertiaMap (q) : AbsoluteInertia (tamePrime (tameK q)) →ₜ* GB ; tameInertiaMap_apply
def tameInertia (q : Fin 4) : GB ;  def tameFrobenius (q : Fin 4) : GB
theorem tameInertia_hasLabel (q) : HasLabelHat (tameInertia q) (tameTau q)
theorem tameFrobenius_hasLabel (q) : HasLabelHat (tameFrobenius q) (tamePhi q)
theorem tame_relation (q) : tameFrobenius q * tameInertia q * (tameFrobenius q)⁻¹ = tameInertia q ^ tameN q
theorem tame_generates (q) (U : OpenNormalSubgroup GB) :
    ProfiniteTame.quotientGenerates (tameInertiaMap q) (tameDecompositionMap q) U (tameInertia q) (tameFrobenius q)
-- also: tameInertiaAbs k, tameFrobeniusAbs k (absolute elements at the chosen place), their labels,
-- tame_generating_relation k, exists_generated_tame_pair_of_closed, quotientGenerates_comp,
-- isClosed_hasLabel, genusRestriction : Gal(Closure/ℚ) →ₜ* Gal(Carrier/ℚ)
```

### `Local/Frobenius.lean`, `Local/FrobeniusLocal.lean`, `Local/Caps.lean` — 29 and 7
```lean
abbrev absFrob (p) : AbsoluteDecomposition p := SigmaUnramified.absoluteFrobenius p
theorem image_zpowers_of_inertia (p) (f : AbsoluteDecomposition p →ₜ* H) [DiscreteTopology H]
    (hf : ∀ σ : AbsoluteInertia p, f σ.val = 1) (d) : f d ∈ Subgroup.zpowers (f (absFrob p))
theorem range_eq_zpowers_of_inertia (p f hf) : f.toMonoidHom.range = Subgroup.zpowers (f (absFrob p))
def genusRestrictionD (p) : AbsoluteDecomposition p →ₜ* Gal(Carrier/ℚ) ; genusRestrictionD_inertia (e_E(p) = 1)
theorem frobenius_label_of_split / frobenius_label_of_inert        -- the exponent-two trick
theorem Tame.frobenius_unit_radical' …                              -- valuation-ring radicand (needed at 7)
theorem exists_absolute_frobenius_split … ; exists_absolute_frobenius_seven …   -- finite level
def betaQ (k) : Genus.Q241 ; theorem radQ_pow_24 : radQ k ^ 24 = frob7Sign k + 7 * betaQ k ; betaQ_den
abbrev prime29 ; def place29 : Fin 2 ; def frob29Vec (P) := binaryVector 8 (![228, 216] P)
def decomposition29 (P : Fin 2) : AbsoluteDecomposition prime29 →ₜ* GB   -- normalized
def frob29 (P : Fin 2) : GB ; theorem frob29_hasLabel (P) : HasLabelHat (frob29 P) (frob29Vec P)
abbrev prime7 ; def frob7 : Ghat := decompositionMap prime7 (absFrob prime7)
theorem frob7_not_mem : frob7 ∉ GB ; frob7_sq_mem : frob7 ^ 2 ∈ GB
theorem frob7_sq_hasLabel : HasLabelHat (frob7 ^ 2) (binaryVector 8 14) ; sigmaMatrix_frob7 (σ fixes it)
theorem decomposition7_range (q : Ghat →ₜ* H) [DiscreteTopology H]
    (hI : ∀ σ : AbsoluteInertia prime7, q (decompositionMap prime7 σ.val) = 1) :
    (q.comp (decompositionMap prime7)).toMonoidHom.range = Subgroup.zpowers (q frob7)
theorem decomposition29_range (P) (q : GB →ₜ* H) [DiscreteTopology H] (hI : …) :
    (q.comp (decomposition29 P)).toMonoidHom.range = Subgroup.zpowers (q (frob29 P))
```

### `Local/DyadicCut.lean` — the ℚ₂-local cut, `e = 8`, `f = 4`
```lean
def localCut : PadicTwoMaximalProTwo.Group →ₜ* Dyadic.D
theorem localCut_presentation : localCut.comp SigmaDyadic.localPresentation = Dyadic.ArithmeticPresentation.model
theorem localCut_surjective ; localCut_generator (i) : localCut (generator i) = ![D.y, D.x, D.y * D.z] i
theorem retainedDyadic_localCut (g) : SigmaDyadic.retainedDyadic (localCut g) = retainedLocalQ g   -- ℚ retained field
theorem factor_through_localCut (ψ f) (h : ψ ∘ localPresentation = f ∘ model) : ψ = f.comp localCut
theorem ker_eq_localCut_ker (ψ f) (hf : Injective f) (hψ : ψ = f.comp localCut) : ψ.ker = localCut.ker
def dyadicCutD : AbsoluteDecomposition prime2 →* Dyadic.D ; dyadicCutD_decomposition ; dyadicCutD_surjective
theorem retained_decompositionMap (d) : sigmaRetainedModelMap (SigmaUnramified.decompositionMap prime2 d) =
    SigmaDyadic.retainedDyadic (dyadicCutD d)                        -- comparison for T11 route T
theorem retained_restriction_eq_one_iff (d : AbsoluteDecomposition prime2) :
    decompositionRestriction prime2 ArithmeticRetained.RetainedField sigmaRetainedAbsoluteEmbedding d = 1 ↔
      dyadicCutD d = 1                                               -- same kernel as the ℚ retained field
theorem dyadicCutD_inertia_card : Nat.card (dyadicCutD.comp (AbsoluteInertia prime2).subtype).range = 8
theorem image_cards_of_factor (ψ : AbsoluteDecomposition prime2 →* H) (f : D →* H) (hf : Injective f)
    (hψ : ψ = f.comp dyadicCutD) : Nat.card (ψ.comp inertia.subtype).range = 8 ∧ Nat.card ψ.range = 32
theorem decompositionMapB_dyadic (σ) : decompositionMapB prime2 _ (decomposition σ) = dyadicLocal dyadicPlace (projection σ)
theorem decompositionMapB_factor (q : GB →* H) (f : D →* H) (hq : q ∘ dyadicLocal dyadicPlace = f ∘ localCut) :
    q.comp (decompositionMapB prime2 _) = f.comp dyadicCutD
```
(`Presentation.localPresentation`/`genuineRelation` are definitionally
`SigmaDyadic.localPresentation`/`genuineRelation`.)

### `Local/Unramified.lean`, `Local/CapRanges.lean` — Ω/ℚ unramified outside {2,3,5,241}
```lean
def ramSupportQ : Set (HeightOneSpectrum (𝓞 ℚ)) := {v | ((7230 : ℤ) : 𝓞 ℚ) ∈ v.asIdeal}
theorem place_not_mem_ramSupportQ (p) (hp : p.val ∉ {2, 3, 5, 241}) : place p ∉ ramSupportQ
theorem B_unramified : IsUnramifiedAtFinitePlacesOutside ℚ B ramSupportQ
theorem isUnramified_rat_of_B (L : IntermediateField B Closure) [FiniteDimensional B L]
    (hL : IsUnramifiedAtFinitePlacesOutside B L S) : IsUnramifiedAtFinitePlacesOutside ℚ L ramSupportQ
theorem layer_unramified (K : IntermediateField B Closure) [FiniteDimensional B K] (hK : K ≤ OmegaBcl) :
    IsUnramifiedAtFinitePlacesOutside B K S          -- finite subextensions of Ω/B (useful for T10)
theorem inertia_fixes_Omega (p) (hp) (σ : AbsoluteInertia p) (x) (hx : x ∈ Omega) : σ.val.val x = x
theorem inertia_killed (p : Nat.Primes) (hp : p.val ∉ ({2, 3, 5, 241} : Finset ℕ))
    (σ : AbsoluteInertia p) : decompositionMap p σ.val = 1
theorem inertia_killed_B (p hp hsq P₀ P σ) : localMapB p hsq P₀ P σ.val = 1
theorem decomposition7_range' (q : Ghat →ₜ* H) [DiscreteTopology H] :
    (q.comp (decompositionMap prime7)).toMonoidHom.range = Subgroup.zpowers (q frob7)
theorem decomposition29_range' (P) (q : GB →ₜ* H) [DiscreteTopology H] :
    (q.comp (decomposition29 P)).toMonoidHom.range = Subgroup.zpowers (q (frob29 P))
theorem decomposition_range_unramified (p) (hp : p.val ∉ {2, 3, 5, 241}) (q : Ghat →ₜ* H) [DiscreteTopology H] :
    (q.comp (decompositionMap p)).toMonoidHom.range = Subgroup.zpowers (q (decompositionMap p (absFrob p)))
```
For the census primes (T10), `exists_absolute_frobenius_split` (any odd split `p` with a unit
square-class table at the chosen place, e.g. from `Base.padicInt_eq_mul_sq_of_toZMod` at
both roots) and `frobenius_label_of_split` give the Frobenius labels; with
`decomposition_range_unramified` the decomposition image is cyclic on the Frobenius.

## Open items / notes

* The ℚ₂-local cut field `L₂` is not defined as an `IntermediateField`; its indices are
  delivered as image cardinalities on the chosen decomposition group at `2`
  (`image_cards_of_factor`: inertia `8`, decomposition `32`), the form T10 uses with
  `PrimeCompletion.ramification_residue_of_absolute_image_cards`. The kernel comparison
  with the ℚ retained field (`retained_decompositionMap`) is the input of T11's route T.
* Tame local indices at 3, 5 (`e = 2`, `f = 2`) are T10's: upper bounds from the cut words
  `τ², φ²` and `tame_generates`, lower bounds from the labels.
* The choice of place above each `p` is the ℚ package's; the local maps are normalized by
  `frame` (both roots of 241 are covered by the Base tables).

## Rebuild

    ./.toolchain/bin/lake build UnitDistance.Sqrt241.Local.Elements

(builds all of `Local/`; ≈ 1–2 min after the upstream cone and T6 are built.)

## Resume

T5 is complete. Possible follow-ups (only if a consumer asks): an explicit field `L₂`,
convenience restatements for T10's level fields.
