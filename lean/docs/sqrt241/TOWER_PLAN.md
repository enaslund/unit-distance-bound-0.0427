# Tower over B = ℚ(√241): implementation plan (streams C, D, E)

Status: plan, 2026-09-29, kept as a record; it has been carried out, and the delivered
proof is described in [SUBMISSION.md](SUBMISSION.md). No Lean proofs are claimed here. Conventions:
[CONVENTIONS.md](CONVENTIONS.md); port overview: [../SQRT241_PORT.md](../SQRT241_PORT.md);
mathematics: `papers/0.04273/research/construction.md` §3;
finite data: `papers/0.04273/certificates/{kummer241.gp,
cup241.gp, lie241.py, lie241c.py, gs241.py}`.

The plan rests on a survey of the 426 project modules that lie in the import
cone of the ℚ tower theorem and outside the analytic/geometric cone (§2),
on reading the key interfaces (quoted below with their real names), on a
Lean typing experiment for the two-closure architecture (§1.4), and on PARI
and Python recomputation of the design data (§1.5). Statements in §3 are
interface specifications; their proofs are not written.

## 0. Summary

* **Architecture.** Two worlds and one bridge. The *B-world* is a literal
  retyping (ℚ → F) of the ℚ maximal-pro-p machinery and relation bound, in
  `AlgebraicClosure B`, producing Ω_B, G_B := Gal(Ω_B/B), H¹ = 8 and
  H² ≤ 7. The *ℚ-world* lives in `AlgebraicClosure ℚ` (as CONVENTIONS
  require): Ω := χ⁻¹(Ω_B) for a fixed B-isomorphism χ of closures, Ĝ :=
  Gal(Ω/ℚ), G_B the fixing subgroup of B (open, index 2). All local data
  come from the ℚ development's ℚ_p-decomposition groups restricted to Ω;
  second primes and c₂ are σ̂-conjugates; the cut kernel is normal in Ĝ and
  every level is Galois over ℚ.
* **M is not a radical tower.** M := fixed field of `core := ker ρ_B ⊓
  σ̂(ker ρ_B)σ̂⁻¹`, where ρ_B : G_B →ₜ* Q_B = F₂⁸ × F₂¹⁵ is defined through the
  presentation. Every property of M that the other streams need follows from
  ρ_B (lower bounds on local images) and the cut (upper bounds). The ℚ
  catalogue/radical/canonical-retained modules are not ported (most of the
  53 N modules of §2).
* **Reuse.** Of the 426 modules (44.9k lines): 224 are reused unchanged
  (25.7k lines: all of the group-augmentation/Jennings/Fox/GS machinery, the
  finite dyadic group D, the local ℚ₂ and ℚ_p theory, the pro-2 presentation
  machinery, the rational-prime index lemmas), 72 are generalized (6.8k
  lines, mostly retyping ℚ → F or a target/parameter change), 63 need a
  B-analogue (5.5k lines of templates), 53 are not needed (5.1k lines: the
  explicit ℚ retained/catalogue fields and the historical endpoints), and 14
  are mixed (§2).
* **New mathematics in Lean**, in decreasing risk: the relation bound with
  two real places (bounded-kernel detection and a B character with
  prescribed inertia, T4); the Galois-over-ℚ transport for Ω_B (T1); the
  root discriminant of M by comparison with the verified ℚ retained field at 2
  (T11); the global initial form of the genuine dyadic relation (T6); the ℚ₂
  local cut field L₂ with e = 8, f = 4 (T5); the Kummer classification over B
  (T3); B local square classes and labels, including the inert prime 7 (T5).
* **Effort.** ≈ 22–33 agent-days in 13 work packages (§3.3); the sequential
  chain T0 → T1 → T5a → T8 → T9 → T10 → T11 → T12 is ≈ 12–18 agent-days, with
  the relation bound T4 → T6 beside it; with five agents and interface-first
  development (parameters for the presentation and the labels) about 8–12
  days elapsed, plus machine time.

## 1. Architecture decision

### 1.1 What is kept from the proposal, and what changes

Kept: everything in the fixed closure of ℚ; B = ℚ⟮baseRoot⟯; Ω_B Galois over
ℚ with G_B of index 2 in Ĝ; local data at a split p from ℚ_p-decomposition
groups (which lie in G_B) and their σ̂-conjugates; cut words at the second
prime defined as σ̂-conjugates, so that the cut kernel is Ĝ-normal and all
levels are Galois over ℚ; the genus field literally the maximal elementary
abelian subextension, equal to the image of the canonical E; the relation
bound via Kummer images of finite stages with a detection kernel of order ≤ 2
coming from the two real places, and an inertia-correcting character using
h(B) = 1.

Changed or made precise:

1. **Ω_B is built over B, in `AlgebraicClosure B`, by retyping.** The ℚ files
   `FinitePExtension*`, `MaximalProP*`, `ProPOpenNormalStage`, `ProPStage*`,
   `AbsoluteProP*`, `CentralLiftCorrection`, `ProTwoH2AbsoluteKernel` and the
   H² reduction are ℚ only in their typing; they use
   `Field.absoluteGaloisGroup F = Gal(AlgebraicClosure F/F)` and upstream
   decomposition groups `finitePlaceAbsoluteDecompositionGroup F v`, which are
   generic in F but fixed to `AlgebraicClosure F`. Retyping with
   `AlgebraicClosure F` is mechanical; retyping with an arbitrary closure
   (`[IsAlgClosure F C]`, as one survey suggested) would require transporting
   every upstream local object and is not recommended.
   Defining Ω_B over ℚ instead (compositum of ℚ-Galois layers containing B)
   does not save work: the stage-kernel theorem of the relation bound needs
   *maximality over B* (a finite Galois 2-extension of B unramified outside S
   lies in Ω_B), which over-ℚ layers only give after the same conjugation
   transport lemma that proves Ω_B Galois over ℚ (T1).
2. **The ℚ-world is in `AlgebraicClosure ℚ`**, with Ω := χ⁻¹(Ω_B) for
   `χ : AlgebraicClosure ℚ ≃ₐ[B] AlgebraicClosure B`. Then B ≤ Ω literally, the
   canonical E ≤ Ω, and every ℚ local map is `finitePlaceAbsoluteDecompositionInclusion
   ℚ v` followed by restriction to Ω, exactly as in the ℚ package
   (`AbsoluteLocalCompactness.finitePlaceDecompositionToMaximalProPOutside`),
   with `maximalSigmaProTwo` replaced by Ω. The ℚ retained field of the
   verified package lives in the same closure with the same chosen p-adic
   places; the root-discriminant route T of T11 uses this.
3. **G_B is a subgroup of Ĝ** (the fixing subgroup of B), not a separate type.
   Conjugation by σ̂, normality of the cut and all local maps live in Ĝ. The
   B-world results (generators, H² ≤ 7, pro-2 basis) are transported once
   along `bridge : Gal(Ω_B/B) ≃ₜ* G_B` (continuous cohomology is invariant:
   `continuousCohomologyZModPLiftedLinearEquiv`).
4. **M is abstract** (as in §0). Why this is enough: the downstream and
   analytic streams need (i) E → M, √3, √−1 ∈ M, (ii) K_j/M unramified at
   finite places, i.e. inertia of K_j injects into Gal(M/ℚ), (iii) the exact
   types of M at 2, 29, 7 and f ≥ 4 at the census primes (for a Galois
   M ⊇ E, (1/[M:ℚ]) log ζ_M only decreases when local types grow), and
   (iv) rd(M) ≤ ℓ, a property of the local fields (T11). Lower bounds on local
   images come from ρ_B; upper bounds from the cut, because kernelHat ≤ core
   makes Gal(M/ℚ) a quotient of Ĝ/kernelHat. [M:ℚ] = 2²⁴ if
   core = ker ρ_B (expected); nothing uses it.
5. **Labels and normalization.** The ℚ package chooses its places of
   `AlgebraicClosure ℚ` by `Classical.choice` (`IsAlgClosed.lift` in upstream
   `FinitePlaceH2Localization.lean`); whether the chosen place above p lies
   over PARI's first prime of B cannot be decided in advance. Each local map
   is therefore *normalized* by conjugating with σ̂ when needed (`frame`,
   T5), and the local root-action theorems are proved for both p-adic roots
   of 241 (they apply verbatim to the σ̂-conjugated pair). First primes:
   𝔭₁ ↔ √241 ≡ 7 (mod 32), 𝔮₁ ↔ ≡ 2 (mod 3), 𝔯₁ ↔ ≡ 1 (mod 5),
   29₁ ↔ ≡ 3 (mod 29) (`Base.pi29` has positive valuation there); with the
   Frobenius lift normalized to fix √π_𝔮 these reproduce every vector of
   construction.md §3.4 (survey check). The complex embedding needs no
   normalization: it is chosen as a B-algebra lift of `Base.complexEmbPlus`.
6. **No B_𝔭 ≅ ℚ_p bridge.** At split p every ℚ_p-decomposition group fixes
   √241 (241 is a square in ℚ₂, ℚ₃, ℚ₅, ℚ₂₉) and is the decomposition group
   of a prime of B; `PrimeCompletion.decompositionEquiv p` already
   identifies it with Gal(ℚ̄_p/ℚ_p).

### 1.2 Key definitions (exact types)

Namespaces `UnitDistance.Sqrt241.*`; `Closure := AlgebraicClosure ℚ`
(`CanonicalGenus.Closure`), `B := Base.B : IntermediateField ℚ Closure`
(exists: `UnitDistance/Sqrt241/Base/Field.lean`, with `sigma`, `embPlus`,
`embMinus`, `placePlus`, `placeMinus`; `Base/Integers.lean` has `eps`,
`pi2 … pi5'`, `pi29`, `pi29'`; `Base/ClassNumber.lean` has
`isPrincipalIdealRing`, `classNumber_eq_one` — work in progress of another
stream, not yet verified).

```lean
-- B-world (T0), generic retype in namespace UnitDistance.Sqrt241.ProP (F any number field)
def IsAdmissibleFiniteLayer (F : Type) [Field F] [NumberField F] (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 F))) (E : FiniteGaloisIntermediateField F (AlgebraicClosure F)) : Prop :=
  IsPGroup p (E ≃ₐ[F] E) ∧ ClassFieldTower.Sawin.IsUnramifiedAtFinitePlacesOutside F E T
def maximalProPOutside (F) [..] (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 F))) :
    IntermediateField F (AlgebraicClosure F)
-- instance on B
namespace UnitDistance.Sqrt241.Tower
abbrev Bbar : Type := AlgebraicClosure B
def S : Set (HeightOneSpectrum (𝓞 B)) := {v | (30 : 𝓞 B) ∈ v.asIdeal}        -- the six primes above 2,3,5
def OmegaB : IntermediateField B Bbar := ProP.maximalProPOutside B 2 S
abbrev GBw : Type := Gal(OmegaB/B)                                           -- B-world group

-- bridge (T1)
instance : IsAlgClosure B Closure := ⟨inferInstance, inferInstance⟩          -- checked (§1.4)
def chi : Closure ≃ₐ[B] Bbar := IsAlgClosure.equiv B Closure Bbar
def Omega : IntermediateField ℚ Closure :=
  (OmegaB.restrictScalars ℚ).map (chi.symm.restrictScalars ℚ).toAlgHom
instance Omega_isGalois : IsGalois ℚ Omega
theorem B_le_Omega : B ≤ Omega
abbrev Ghat : Type := Gal(Omega/ℚ)
def GB : Subgroup Ghat := (IntermediateField.restrict B_le_Omega).fixingSubgroup
theorem GB_isOpen : IsOpen (GB : Set Ghat)
theorem GB_index : GB.index = 2
def bridge : GBw ≃ₜ* GB
theorem Ghat_hasPGroupOpenNormalBasis : ProCGroups.ProC.HasPGroupOpenNormalBasis 2 Ghat
def sigmaHat : Ghat := Classical.choose exists_not_mem_GB                       -- any lift of σ
theorem sigmaHat_baseRoot : (sigmaHat ⟨baseRoot, _⟩ : Closure) = -baseRoot

-- generators and presentation (T3, T6)
def genusLabel : GB →ₜ* Multiplicative (Fin 8 → ZMod 2)  -- action on CanonicalGenus.genusRoot; kernel = Φ(G_B)
def gen (i : Fin 8) : GB                                 -- genusLabel (gen i) = ofAdd (Pi.single i 1)
def freeMap : FiniteFreeProTwo.Carrier 8 →ₜ* GB          -- surjective, ker ≤ closedPowerCommutator
def relationKernel : ClosedSubgroup (FiniteFreeProTwo.Carrier 8)
def relator : Fin 7 → relationKernel                     -- c₁², c₂², 4 tame words, genuine relation at 𝔭₂
theorem relator_generates :
  closedNormalClosure (Set.range fun i => (relator i : FiniteFreeProTwo.Carrier 8)) = relationKernel

-- local elements (T5); all in GB except frob7
def conj₁ : GB          -- complex conjugation of phi₁ : Omega →+* ℂ lifting Base.complexEmbPlus
def conj₂ : GB          -- ⟨sigmaHat * conj₁ * sigmaHat⁻¹, _⟩
def dyadicLocal (P : Fin 2) : PadicTwoMaximalProTwo.Group →ₜ* GB   -- P = 1: sigmaHat-conjugate of P = 0
def tameInertia (q : Fin 4) : GB
def tameFrobenius (q : Fin 4) : GB                       -- q ∈ {𝔮₁,𝔮₂,𝔯₁,𝔯₂}
def frob29 (P : Fin 2) : GB
def frob7 : Ghat        -- frob7 ∉ GB, frob7 ^ 2 ∈ GB

-- cut, retained quotient, M, detector, levels (T7–T9)
def words : Set (FiniteFreeProTwo.Carrier 8)             -- 21 quadratic + 2 cubic + 7 deep literal words (T8)
def kernel : Subgroup (FiniteFreeProTwo.Carrier 8) := closedNormalClosure words
def kernelHat : Subgroup Ghat                            -- image of kernel under freeMap, inside GB; Ĝ-normal, closed
abbrev QB : Type := ClassTwo.GroupModel cocycleB          -- (Fin 8 → ZMod 2) × (Fin 15 → ZMod 2), card 2²³
def retainedMap : GB →ₜ* QB                               -- ρ_B, surjective, base = genusLabel, kills kernelHat
def retainedKer : Subgroup Ghat := retainedMap.toMonoidHom.ker.map GB.subtype
def core : Subgroup Ghat := retainedKer ⊓ retainedKer.map (MulAut.conj sigmaHat).toMonoidHom   -- open, normal
def M : IntermediateField ℚ Omega := IntermediateField.fixedField core
def detector : Ghat →ₜ* DetectorGroup                     -- Ĝ ⧸ (Magnus kernel ⊓ σ̂-conjugate), finite
def level (j : ℕ) : IntermediateField ℚ Omega              -- generalized GaloisRetainedFamily, ρ := Ĝ → Ĝ ⧸ kernelHat
```

### 1.3 Why the pieces fit

* **Cut normal in Ĝ.** The cut is defined on the free source (as over ℚ;
  the Magnus detector, the GS local cover and the free universal retained map
  are all free-presentation arguments). Its 30 literal words are σ̂-stable up
  to G_B-conjugacy and consequences: first-prime words ↦ second-prime words;
  second-prime words ↦ σ̂²-conjugates (σ̂² ∈ G_B) of first-prime words; the
  word y₂² present at 𝔭₂ only has its 𝔭₁ counterpart in the kernel through
  the genuine relation r₁ and the 𝔭₁ cuts; (F₇²)⁴ commutes with F₇ ∉ G_B.
  Hence the image `kernelHat` is normal in Ĝ.
* **Levels Galois over ℚ.** They are fixed fields of pullbacks of open
  normal subgroups of Ĝ/kernelHat (`GaloisQuotientTower.exists_family`,
  generic in k, K); `kernelHat ≤ core` puts M in every level.
* **Centralizer index 2¹⁶ in Gal(K_j/ℚ).** The Ĝ-class of c₁ contains the
  G_B-classes of c₁ and c₂ = σ̂c₁σ̂⁻¹, which are disjoint because their
  elementary images differ (10111010 vs 11000101), and each has size ≥ 2¹⁵
  in the detector (lie241c.py: class of c₁ in G_B/D₄ of size 2¹⁵);
  `card_le_centralizer_index_of_conjugates_injective` with parameter set
  (U₂ × U₃) × Bool.
* **Prime freedom** needs no non-abelian labels: for each witness prime p
  there is d < 0, a square in ℚ_p, with √d ∈ ℚ(√−1, √2, √3, √5) ⊆ E:
  d = −15, −2, −1, −3, −1 at p = 2, 3, 5, 7, 29. Complex conjugation moves
  √d and every element of every decomposition group above p fixes it.
* **K_j/M unramified at finite places.** K_j/B is unramified outside S (Ω_B);
  at 2, 3, 5 the rational e of K_j and M agree (8, 2, 2): lower bounds from
  ρ_B, upper bounds from the cut. No computation at 241 is needed.
* **The omitted place.** The distinguished (omitted) dyadic place is the
  normalized 𝔭₁; its genuine relation is in the closed normal closure of the
  seven relators by `relator_generates`; the 𝔭₂ genuine relation is a relator
  and is covered by the 𝔭₂ D-block in GS.
* **Root discriminant.** At 2, M and the ℚ retained field of the verified
  package have the same inertia kernel at the ℚ package's chosen place (same
  ℚ₂ local generators, both local images ≅ D), so v₂(disc)/degree agrees and
  the ℚ bound (9/4) transfers; at 3, 5, 241 compare with ℚ(√−3), ℚ(√5), B.

### 1.4 Checked in Lean (scratch, not in the repository)

`Exp1.lean` (scratch) elaborates against the current build: `B := ℚ⟮baseRoot⟯`,
`IsAlgClosure B Closure` via `⟨inferInstance, inferInstance⟩` (must be an
`instance`), `IsAlgClosure.equiv B Closure (AlgebraicClosure B)`,
`Field.absoluteGaloisGroup B` (needs `Mathlib.FieldTheory.AbsoluteGaloisGroup`),
`Gal(Ω/B)` and `Gal(Ω/ℚ)` for `Ω : IntermediateField B (AlgebraicClosure B)`
(ℚ-structure `DivisionRing.toRatAlgebra`, `IsScalarTower.rat` found),
`AlgEquiv.restrictScalarsHom ℚ : Gal(Ω/B) →* Gal(Ω/ℚ)`, and
`((⊥ : IntermediateField B Ω).restrictScalars ℚ).fixingSubgroup`.
`Algebra.IsAlgebraic ℚ (AlgebraicClosure B)` is *not* inferred (needs
`Algebra.IsAlgebraic.trans`). Mathlib's `IntermediateField.fixingSubgroupEquiv`
is only a `MulEquiv`; the homeomorphism is new (T1), but a continuous
bijection of compact Hausdorff groups suffices
(`ContinuousMulEquiv.ofBijectiveCompactToT2`, used in `SigmaFreeSource`).

### 1.5 Data checks (PARI/Python, scratch)

* Second-prime data are σ-transforms: with σ on V given by e₀↦e₀, e₁↦e₀+e₁,
  e₂↦e₀+e₃, e₃↦e₀+e₂, e₄↔e₅, e₆↔e₇ (σ(ε) = −ε⁻¹, σ(π₂) = −π₂′, σ(π₃) = π₃′,
  σ(π₅) = π₅′), the transposed action maps x₁,y₁,z₁ ↦ x₂,y₂,z₂, c₁ ↦ c₂,
  Frob(29₁) ↦ Frob(29₂) and fixes Frob(7), exactly as in construction.md
  §3.4 and `kummer241.gp`.
* Presentation initials (survey): with squares at bits 0..7 and pairs (j<i)
  at 8 + lexicographic index, the seven relator initials have masks
  `[2506108509, 17181200803, 7520389136, 26852200480, 42966974464,
  39192625152, 606158977]`, dual functionals `[4, 2, 20, 34, 524288,
  1048578, 7]`, and the omitted 𝔭₁ initial `277423951` is their XOR
  (`b_dual.py`, `cupcheck.py` in the scratch directory; the cup-product
  matrices agree with `cup241.gp` at all 36 pairs and 8 places).
* Census: in 41..97 the primes 41, 47, 53, 59, 61, 67, 79, 83, 97 split in B
  (18 primes of norm ≤ 100) and 43, 71, 73, 89 are inert; Frobenius vectors
  of all 18 split primes were recomputed (`census.gp`).
* Dyadic local field: N₀ = ℚ(ζ₄₀, √(−2+3i)) has one prime above 2 with
  e = 8, f = 4 and v₂(disc) = 72, i.e. normalized different 9/4; for
  ℚ(ζ₈, √5) it is 2. Another stream's `scripts/sqrt241/dyadic_radicals.gp`
  finds explicit D₄-radicals β₁ ∈ B(√π₂′), β₂ ∈ B(√−π₂) with norms π₃′, π₃
  realising the [y,z]-functionals; B(√π₂′, √π₃′, √β₁, √2) has a prime of
  type (8,2) with normalized different 9/4.

## 2. The ℚ tower pipeline, module by module

**Scope.** The 426 project modules (44,940 lines) in the import cone of the
tower-side imports of `SharperPairFixedBaseBridgeRun20260920.lean`
(`SigmaCutUnconditional`, `SigmaCutFamilyRamification`,
`SigmaCutFamilyPrimeFreedom`, `GaloisRetainedFamily`, `GaloisFixedArithmetic`,
`RetainedDyadicDifferentComplement`) and outside the cone of its
analytic/geometric imports (`ArithmeticSequence`, `SIntegerWitnessGraph`,
`RelativeResidueFixedBase`, `ImaginaryQuadraticContinuation`,
`WitnessPrimePairs`, `RationalGaloisAlgebra`,
`SharperPairArithmeticRateCoreRun20260920`), computed from
`scripts/source_inventory.py --json`. Not listed: 1,287 upstream modules
(492k lines; Yamaguchi, AINTLIB, …), all reused unchanged; and 338 project
modules shared with the analytic cone (43k lines, stream A's), of which the
tower reuses `KummerInvariantRadicand`, `MultiquadraticTower`,
`GaloisConjugationFixedField` (centralizer and signature lemmas) unchanged.

**Legend.** U reuse unchanged · G reuse via generalization (what) · A
B-analogue to write (what it must prove; statements in §3) · N not needed ·
mixed codes (U/N, G/A, …) mean the module splits. Statuses come from eight
read-only survey agents, each reading its group's sources in full, and from
the lead's reading of the central modules. The WP in each heading is the
work package that owns the G/A items of that group.

**Totals.** U 224 modules / 25,729 lines · G 72 / 6,777 · A 63 / 5,461 ·
N 53 / 5,148 · mixed 14 / 1,825 (U/N 3, U/A 3, U/G 1, G/A 5, A/N 2).

#### A. Maximal pro-p extension and finite stages — 16 modules, 1384 lines (WP T0, T1)

| module | lines | port | what / how |
|---|---:|:-:|---|
| `AbsoluteProPFactor` | 149 | G | retype ℚ → F, AlgebraicClosure ℚ → AlgebraicClosure F (copy into Sqrt241/ProP; ℚ cone untouched) |
| `AbsoluteProPRestriction` | 143 | G | retype ℚ → F, AlgebraicClosure ℚ → AlgebraicClosure F (copy into Sqrt241/ProP; ℚ cone untouched) |
| `AbsoluteProPUnramified` | 80 | G | retype ℚ → F, AlgebraicClosure ℚ → AlgebraicClosure F (copy into Sqrt241/ProP; ℚ cone untouched) |
| `FinitePExtension` | 123 | G | retype ℚ → F, AlgebraicClosure ℚ → AlgebraicClosure F (copy into Sqrt241/ProP; ℚ cone untouched) |
| `FinitePExtensionSupport` | 95 | G | retype ℚ → F, AlgebraicClosure ℚ → AlgebraicClosure F (copy into Sqrt241/ProP; ℚ cone untouched) |
| `MaximalProPGroup` | 111 | G | retype ℚ → F, AlgebraicClosure ℚ → AlgebraicClosure F (copy into Sqrt241/ProP; ℚ cone untouched) |
| `MaximalProPOutside` | 80 | G | retype ℚ → F, AlgebraicClosure ℚ → AlgebraicClosure F (copy into Sqrt241/ProP; ℚ cone untouched) |
| `MaximalProTwoSigma` | 38 | A | Ω_B := maximalProPOutside B 2 S_B, pro-2 basis, layer characterization |
| `ProPOpenNormalStage` | 163 | G | retype ℚ → F, AlgebraicClosure ℚ → AlgebraicClosure F (copy into Sqrt241/ProP; ℚ cone untouched) |
| `ProPStageLocalConditions` | 46 | G | retype ℚ → F, AlgebraicClosure ℚ → AlgebraicClosure F (copy into Sqrt241/ProP; ℚ cone untouched) |
| `ProPStageRestriction` | 111 | G | retype ℚ → F, AlgebraicClosure ℚ → AlgebraicClosure F (copy into Sqrt241/ProP; ℚ cone untouched) |
| `SigmaFiniteFieldInclusion` | 58 | A | K →ₐ[B] Ω_B from IsPGroup + unramified outside S_B (for E); relative, not UnramifiedAway 30030 |
| `SigmaFinitePrimeSupport` | 40 | A | S_B = {v : 30 ∈ v}, Finset of the six primes (card ≤ 6 suffices) |
| `SigmaFiniteRamification` | 65 | A | relative ramification over 𝓞_B (241 ramifies in B) |
| `SigmaPrimeSupport` | 48 | A | S_B = {v : 30 ∈ v}, Finset of the six primes (card ≤ 6 suffices) |
| `SigmaRamification` | 34 | N | ℤ-level 30030 certificate; state relatively |

#### B. Relation bound (H²) — 32 modules, 3148 lines (WP T4)

| module | lines | port | what / how |
|---|---:|:-:|---|
| `ActualLocalTensorH2` | 102 | U | generic in the base number field |
| `CentralLiftCorrection` | 181 | G | base F; hThree → hchar : PrescribedQuadraticInertia F T |
| `CoinducedH2Evaluation` | 114 | U | generic in the base number field |
| `CoinducedH2Transport` | 33 | U | generic in the base number field |
| `FieldTensorCyclicH2` | 157 | U | generic in the base number field |
| `FieldUnitsH2LocalInflation` | 64 | U | generic in the base number field |
| `FieldUnitsIdeleDetection` | 73 | U | generic; assumes unramified infinite places (hinf), so used only over B(i) |
| `FiniteCyclicFinitePlaceH2` | 41 | A | bounded cyclic detection: finite-detection kernel of B(i)/B is {0, x₀} |
| `FiniteLocalTowerEmbedding` | 244 | U | generic in the base number field |
| `FiniteTensorBaseChangeH2` | 50 | U | generic in the base number field |
| `FiniteTensorGaloisInflationH2` | 109 | U | generic in the base number field |
| `FiniteTensorTowerDetection` | 52 | U/A | U; add image version fieldUnitsH2_finite_detection_tower_mem_image |
| `HomKernelTransfer` | 36 | U | generic in the base number field |
| `ImaginaryGaloisEnlargement` | 53 | G | base F, compositum with B(i) in AlgebraicClosure B |
| `ImaginaryQuadraticBase` | 56 | A | B(i) = Extension (-1 : B): Galois, cyclic, totally complex |
| `LocalGaloisTowerRestriction` | 211 | U | generic in the base number field |
| `LocalTensorH2Evaluation` | 164 | U | generic in the base number field |
| `MaximalSigmaH2Bound` | 44 | A | finrank H²(Gal(Ω_B/B)) ≤ 7 |
| `MaximalSigmaH2Reduction` | 182 | G | base F; stage bound 2^7; d = 7 |
| `OneInfinitePlaceNorm` | 63 | G | local norm at all places but one infinite place ⇒ at that place (Fintype.prod_eq_single) |
| `ProTwoH2AbsoluteKernel` | 136 | G | base F; hThree → hchar : PrescribedQuadraticInertia F T |
| `RationalFiniteFieldUnitsH2` | 49 | A | pair detection for finite Galois 2-extensions of B (x = 0 ∨ x = x₀) |
| `RationalFiniteFieldUnitsH2Reduction` | 82 | A | pair detection for finite Galois 2-extensions of B (x = 0 ∨ x = x₀) |
| `RationalFiniteKummerReduction` | 119 | G/A | Kummer image ≤ 2⁶·2 (kernel of size 2) via natCard_range_le_of_map_ker |
| `SupportedIdeleCocycles` | 111 | U | generic in the base number field |
| `SupportedIdeleLocalization` | 77 | U | generic in the base number field |
| `SupportedIdeleOutsideH2` | 88 | U | generic in the base number field |
| `TensorBaseChangeH2` | 135 | U | generic in the base number field |
| `TensorEvaluationH2` | 99 | U | generic in the base number field |
| `TensorH2CoefficientChange` | 49 | U | generic in the base number field |
| `TensorUnitCohomologyNorm` | 105 | U | generic in the base number field |
| `TotallyComplexFieldUnitsH2` | 69 | U | generic; applied with base B(i) (totally complex) |

#### C. Generators (H¹), genus field, explicit ℚ catalogue — 46 modules, 4274 lines (WP T2, T3)

| module | lines | port | what / how |
|---|---:|:-:|---|
| `ArithmeticCatalogIntegers` | 121 | N | explicit ℚ retained/completed field or ℚ-only genus description; M is not built by radicals |
| `ArithmeticCatalogOddRamification` | 47 | N | explicit ℚ retained/completed field or ℚ-only genus description; M is not built by radicals |
| `ArithmeticCatalogOddSquareclasses` | 143 | N | explicit ℚ retained/completed field or ℚ-only genus description; M is not built by radicals |
| `ArithmeticCatalogRadicands` | 180 | N | explicit ℚ retained/completed field or ℚ-only genus description; M is not built by radicals |
| `ArithmeticCatalogRamification` | 80 | A/N | genus part → E unramified outside S over B (E3); retained/completed parts N |
| `ArithmeticCatalogSquareRelation` | 49 | N | explicit ℚ retained/completed field or ℚ-only genus description; M is not built by radicals |
| `ArithmeticChosenGenusField` | 98 | A | replaced by facts on CanonicalGenus.field: Galois over ℚ, Gal(E/B) ≅ F₂⁸ via rootSignHom, degree 512 |
| `ArithmeticChosenGenusRoots` | 47 | A | replaced by facts on CanonicalGenus.field: Galois over ℚ, Gal(E/B) ≅ F₂⁸ via rootSignHom, degree 512 |
| `ArithmeticGenusConjugation` | 56 | A | two real places: sign vectors 10111010 (v₁), 11000101 (v₂) |
| `ArithmeticGenusFrattini` | 106 | G | base ℚ → F, 7 → n, genus equivalence as parameter |
| `ArithmeticGenusSquareClasses` | 88 | A | square roots of V·B×² lie in any field ⊇ E (replaces root_mem_of_supported) |
| `ArithmeticQuadraticClassification` | 113 | A | Kummer classification over B: quadratic L/B unramified outside S ⇒ L = B(√α), α ∈ V (h(B)=1, units) |
| `CatalogCompletedContainmentData` | 35 | N | explicit ℚ retained/completed field or ℚ-only genus description; M is not built by radicals |
| `CatalogCompletedSquareclassData` | 84 | N | explicit ℚ retained/completed field or ℚ-only genus description; M is not built by radicals |
| `CatalogRetainedCoordinates` | 113 | N | explicit ℚ retained/completed field or ℚ-only genus description; M is not built by radicals |
| `CatalogSquareclassData` | 162 | N | explicit ℚ retained/completed field or ℚ-only genus description; M is not built by radicals |
| `CatalogWordSquareclasses` | 82 | N | explicit ℚ retained/completed field or ℚ-only genus description; M is not built by radicals |
| `CoprimeDiscriminantCompositum` | 132 | U | generic over ℚ; not used for E (E/ℚ nonabelian) |
| `CyclicQuarticNorm` | 155 | U | dyadic local (feeds PadicTwoNoCyclicQuartic) |
| `GeneratedOddRamification` | 95 | N | explicit ℚ retained/completed field or ℚ-only genus description; M is not built by radicals |
| `GeneratedQuadraticEmbedding` | 44 | U | generic radical/quadratic tools (rootSignHom, isUnramifiedAt_of_integral_product) |
| `GeneratedQuadraticExponent` | 37 | U | generic radical/quadratic tools (rootSignHom, isUnramifiedAt_of_integral_product) |
| `GeneratedQuadraticGalois` | 89 | U | generic radical/quadratic tools (rootSignHom, isUnramifiedAt_of_integral_product) |
| `GeneratedQuadraticRamification` | 110 | N | absolute UnramifiedAway 30030; E handled directly |
| `GeneratedQuadraticSigns` | 86 | U | generic radical/quadratic tools (rootSignHom, isUnramifiedAt_of_integral_product) |
| `GeneratedQuadraticTower` | 119 | U | generic radical/quadratic tools (rootSignHom, isUnramifiedAt_of_integral_product) |
| `IndependentQuadraticTower` | 198 | U | generic radical/quadratic tools (rootSignHom, isUnramifiedAt_of_integral_product) |
| `NormExtensionCatalog` | 215 | N | explicit ℚ retained/completed field or ℚ-only genus description; M is not built by radicals |
| `QuadraticGeneratedRootFamily` | 119 | N | explicit ℚ retained/completed field or ℚ-only genus description; M is not built by radicals |
| `QuadraticLiftSquare` | 38 | U | generic radical/quadratic tools (rootSignHom, isUnramifiedAt_of_integral_product) |
| `QuadraticLocalSquareclass` | 63 | U | generic radical/quadratic tools (rootSignHom, isUnramifiedAt_of_integral_product) |
| `QuadraticNormTwist` | 64 | U | generic radical/quadratic tools (rootSignHom, isUnramifiedAt_of_integral_product) |
| `QuadraticRadicalPresentation` | 38 | U | generic radical/quadratic tools (rootSignHom, isUnramifiedAt_of_integral_product) |
| `QuadraticRamification` | 158 | U | generic radical/quadratic tools (rootSignHom, isUnramifiedAt_of_integral_product) |
| `QuadraticRationalSignLift` | 71 | N | explicit ℚ retained/completed field or ℚ-only genus description; M is not built by radicals |
| `QuadraticRootCharacterSurjectivity` | 97 | U | generic radical/quadratic tools (rootSignHom, isUnramifiedAt_of_integral_product) |
| `QuadraticRootFamily` | 51 | N | explicit ℚ retained/completed field or ℚ-only genus description; M is not built by radicals |
| `QuadraticRootFamilyGalois` | 80 | N | explicit ℚ retained/completed field or ℚ-only genus description; M is not built by radicals |
| `QuadraticSignLift` | 158 | U/N | binarySign U; signLift* ℚ-only N |
| `QuadraticUnramifiedOutside` | 112 | G | absolute UnramifiedAway → relative Algebra.IsUnramifiedAt (𝓞 B) (B is ramified at 241) |
| `QuadraticUnramifiedRadicand` | 54 | G | absolute UnramifiedAway → relative Algebra.IsUnramifiedAt (𝓞 B) (B is ramified at 241) |
| `SigmaGeneratorRank` | 32 | A | Frattini = fixing(E_B), rank 8 |
| `SigmaGenusGenerators` | 91 | G | Fin 7 → Fin 8, base B |
| `SigmaQuadraticClassification` | 89 | A | every index-2 fixed field of Gal(Ω_B/B) lies in E_B |
| `UnramifiedAwayDiscriminant` | 41 | N | explicit ℚ retained/completed field or ℚ-only genus description; M is not built by radicals |
| `UnramifiedAwayEquiv` | 34 | G | absolute UnramifiedAway → relative Algebra.IsUnramifiedAt (𝓞 B) (B is ramified at 241) |

#### D. Free source, relators, presentation — 29 modules, 2754 lines (WP T3, T5, T6)

| module | lines | port | what / how |
|---|---:|:-:|---|
| `ClassTwoCentralCharacters` | 81 | U | generic pro-2 presentation machinery |
| `ClassTwoCollection` | 148 | U | generic pro-2 presentation machinery |
| `ClassTwoCollectionDiagonal` | 64 | U | generic pro-2 presentation machinery |
| `ClassTwoTameWords` | 67 | U | generic pro-2 presentation machinery |
| `CompactGroupDescent` | 46 | U | generic pro-2 presentation machinery |
| `DyadicArithmeticPresentation` | 225 | U | local rank-3 D₃₂ presentation with the genuine ℚ₂ relation; used at both dyadic places |
| `FiniteFreeProTwo` | 121 | U | generic pro-2 presentation machinery |
| `OriginalQuadraticRelations` | 57 | A | U₈ = F₂⁸×F₂³⁶, 7 B initials, dual coordinates (masks computed) |
| `OriginalRelatorGeneration` | 138 | G | → closedNormalClosure_eq_of_initials (β, n, ℓ parameters) |
| `ProTwoCompletedConsequence` | 219 | U | generic pro-2 presentation machinery |
| `ProTwoCompletedLocalFamily` | 106 | U | generic pro-2 presentation machinery |
| `ProTwoCompletedSubstitution` | 83 | U | generic pro-2 presentation machinery |
| `ProTwoElementaryQuotient` | 123 | U | generic pro-2 presentation machinery |
| `ProTwoFiniteQuotient` | 36 | U | generic pro-2 presentation machinery |
| `ProfiniteGeneratedTameCompactness` | 125 | U | generic pro-2 presentation machinery |
| `ProfiniteGeneratedTameFiniteImage` | 43 | U | generic pro-2 presentation machinery |
| `ProfiniteTameCompactness` | 89 | U | generic pro-2 presentation machinery |
| `RelativeRelatorReplacement` | 116 | U | local rank-3 D₃₂ presentation with the genuine ℚ₂ relation; used at both dyadic places |
| `SigmaComplexConjugation` | 67 | A | c₁ (normalized embedding, v₁), c₂ = σ̂c₁σ̂⁻¹; sign labels |
| `SigmaFreeRetained` | 65 | A | retained map through the presentation: ρ_B : G_B →ₜ* Q_B (no retained field) |
| `SigmaFreeSource` | 67 | A | FiniteFreeProTwo.Carrier 8 → G_B minimal, generators dual to Kummer basis |
| `SigmaOriginalRelators` | 148 | A | 7 relators (c₁², c₂², 4 tame, genuine dyadic at 𝔭₂) + genuineRelation_image lemma |
| `SigmaPresentation` | 24 | A | wrappers with bound 7 |
| `SigmaRelatorGeneration` | 36 | A | wrappers with bound 7 |
| `SigmaRetainedProjection` | 80 | A | retained map through the presentation: ρ_B : G_B →ₜ* Q_B (no retained field) |
| `SpecifiedRelators` | 122 | U | generic pro-2 presentation machinery |
| `UniversalQuadraticFree` | 50 | G | types Fin 7/Q → Fin 8/U₈ |
| `UniversalQuadraticGroup` | 108 | A | U₈ = F₂⁸×F₂³⁶, 7 B initials, dual coordinates (masks computed) |
| `UniversalQuadraticTame` | 100 | N | use ClassTwo.Tame.word_odd, GroupModel.square_coordinates |

#### E. Odd-prime local theory, tame pairs, Frobenius caps, local/global transport — 62 modules, 5844 lines (WP T5, T10)

| module | lines | port | what / how |
|---|---:|:-:|---|
| `ArithmeticOddLocalPairs` | 89 | A | labeled generating tame pairs with B-radical labels (Gal(E_B/B)) |
| `ChosenPrimeInertia` | 101 | U | local p-adic layer; any finite Galois M/ℚ with embedding |
| `ChosenPrimeInertiaCard` | 58 | U | local p-adic layer; any finite Galois M/ℚ with embedding |
| `ChosenPrimeInertiaImage` | 47 | U | local p-adic layer; any finite Galois M/ℚ with embedding |
| `ChosenPrimeInertiaMap` | 125 | U | local p-adic layer; any finite Galois M/ℚ with embedding |
| `CyclicLocalHilbert` | 73 | U | (1+X), (1+X)(1+X²) |
| `ExtraPrimeGenusAction` | 70 | G | prime and integer-radicand table as parameters (29, census) |
| `ExtraPrimeGenusWitness` | 127 | A | Frobenius labels at 29₁, 7 and census primes; abelian label trick only inside G_B |
| `ExtraPrimeRadicals` | 75 | A | Frobenius labels at 29₁, 7 and census primes; abelian label trick only inside G_B |
| `FiniteAbsoluteInertiaImage` | 80 | U | local p-adic layer; any finite Galois M/ℚ with embedding |
| `FiniteFieldImage` | 47 | U | local p-adic layer; any finite Galois M/ℚ with embedding |
| `FiniteInertiaFixedField` | 56 | U | local p-adic layer; any finite Galois M/ℚ with embedding |
| `FiniteInertiaRestriction` | 58 | U | local p-adic layer; any finite Galois M/ℚ with embedding |
| `GaloisCyclicResidueInertia` | 71 | U | local p-adic layer; any finite Galois M/ℚ with embedding |
| `IntrinsicInertiaBaseChange` | 37 | U | local p-adic layer; any finite Galois M/ℚ with embedding |
| `IntrinsicInertiaComparison` | 68 | U | local p-adic layer; any finite Galois M/ℚ with embedding |
| `LocalAbsoluteInertiaRestriction` | 59 | U | local p-adic layer; any finite Galois M/ℚ with embedding |
| `LocalArtinRestriction` | 341 | U | local p-adic layer; any finite Galois M/ℚ with embedding |
| `LocalArtinUnitContainment` | 64 | U | local p-adic layer; any finite Galois M/ℚ with embedding |
| `LocalArtinUnitIndex` | 48 | U | local p-adic layer; any finite Galois M/ℚ with embedding |
| `LocalInertiaFiniteImage` | 95 | U | local p-adic layer; any finite Galois M/ℚ with embedding |
| `LocalResidueSurjectivity` | 42 | U | local p-adic layer; any finite Galois M/ℚ with embedding |
| `LocalTowerRestriction` | 213 | U | local p-adic layer; any finite Galois M/ℚ with embedding |
| `OddAbsoluteFiniteGeneration` | 159 | A | labeled generating tame pairs with B-radical labels (Gal(E_B/B)) |
| `OddAbsoluteFinitePairs` | 119 | N | superseded by the generating versions |
| `OddLocalHilbert` | 139 | U | B's C₂×C₂ block is OddLocal.D 0 (Hilbert (1+X)²); or generalize Fin 5 |
| `OddLocalModels` | 102 | U | B's C₂×C₂ block is OddLocal.D 0 (Hilbert (1+X)²); or generalize Fin 5 |
| `OddLocalRetainedImage` | 70 | G | retained model and vectors as parameters |
| `OddTameCharacter` | 144 | U | local p-adic layer; any finite Galois M/ℚ with embedding |
| `OddTameFrobenius` | 80 | U | local p-adic layer; any finite Galois M/ℚ with embedding |
| `OddTameRadicalAction` | 68 | G | radicand d : ℤ → valuation-ring element (needed at 7) |
| `OddTameRamification` | 99 | U | local p-adic layer; any finite Galois M/ℚ with embedding |
| `OddTameResidueGeneration` | 76 | U | local p-adic layer; any finite Galois M/ℚ with embedding |
| `PadicFiniteGaloisIntrinsic` | 61 | U | local p-adic layer; any finite Galois M/ℚ with embedding |
| `PadicFiniteGaloisValuation` | 102 | U | local p-adic layer; any finite Galois M/ℚ with embedding |
| `PadicOddGeneratingPair` | 129 | G | parameter structure (p, radicand table, ramified class p·c); index by p |
| `PadicOddGenusAction` | 128 | G | parameter structure (p, radicand table, ramified class p·c); index by p |
| `PadicOddIntrinsicInertia` | 52 | G | parameter structure (p, radicand table, ramified class p·c); index by p |
| `PadicOddIntrinsicInertiaReverse` | 50 | G | parameter structure (p, radicand table, ramified class p·c); index by p |
| `PadicOddRadicals` | 75 | U/A | lemmas U; sign tables A (square classes of a_i+b_i r) |
| `PadicOddTamePair` | 131 | G | parameter structure (p, radicand table, ramified class p·c); index by p |
| `PrimeIdealValuationInertia` | 91 | U | local p-adic layer; any finite Galois M/ℚ with embedding |
| `RationalCompletionPadic` | 110 | U | local p-adic layer; any finite Galois M/ℚ with embedding |
| `RationalGaloisBaseChange` | 82 | U | local p-adic layer; any finite Galois M/ℚ with embedding |
| `RationalInertiaBaseChange` | 100 | U | local p-adic layer; any finite Galois M/ℚ with embedding |
| `RationalLocalAbsoluteEmbedding` | 70 | U | local p-adic layer; any finite Galois M/ℚ with embedding |
| `RationalLocalFiniteRestriction` | 64 | U | local p-adic layer; any finite Galois M/ℚ with embedding |
| `RationalLocalPairGeneration` | 111 | G | drop IsMulCommutative: absorb the embedding change (exists_embedding_change) |
| `RationalLocalPairTransfer` | 73 | G | drop IsMulCommutative: absorb the embedding change (exists_embedding_change) |
| `RationalPrimeCompletion` | 114 | U | local p-adic layer; any finite Galois M/ℚ with embedding |
| `RationalPrimeCompletionValuation` | 59 | U | local p-adic layer; any finite Galois M/ℚ with embedding |
| `RetainedCyclicLocalModels` | 171 | G/A | strictness lemmas to any GroupModel β; elements c₁ c₂ Frob(29ⱼ) F₇² new |
| `RetainedOddLocalModels` | 180 | A | odd maps into Q_B at 4 tame places, dual coordinates |
| `SigmaAbsoluteLocalRestriction` | 55 | G | target maximalSigmaProTwo → Ω (normal over ℚ); inertia_killed for p ∉ {2,3,5,241} |
| `SigmaAbsoluteOddGeneration` | 147 | A | odd_generating_relation at 𝔮₁, 𝔯₁ (normalized), σ̂-conjugates at 𝔮₂, 𝔯₂ |
| `SigmaAbsoluteOddRelations` | 105 | N | superseded by the generating versions |
| `SigmaExtraFrobenius` | 107 | A | Frob(29₁) ∈ G_B, F₇ ∉ G_B with F₇² ∈ G_B (vector 01110000) |
| `SigmaFinitePrimeImages` | 37 | G | target maximalSigmaProTwo → Ω (normal over ℚ); inertia_killed for p ∉ {2,3,5,241} |
| `SigmaOddFiniteGeneration` | 46 | G | target maximalSigmaProTwo → Ω (normal over ℚ); inertia_killed for p ∉ {2,3,5,241} |
| `SigmaOddLocalImage` | 54 | G | target maximalSigmaProTwo → Ω (normal over ℚ); inertia_killed for p ∉ {2,3,5,241} |
| `SigmaOddRelationWitness` | 116 | A/N | genus helpers for E_B/G_B A; main theorems N |
| `SigmaUnramifiedFrobenius` | 124 | G | target maximalSigmaProTwo → Ω (normal over ℚ); inertia_killed for p ∉ {2,3,5,241} |

#### F. Dyadic place: ℚ₂ theory, the group D, global transport — 63 modules, 6715 lines (WP T5, T6)

| module | lines | port | what / how |
|---|---:|:-:|---|
| `ArithmeticDyadicAbelianization` | 48 | G | to (L, e : D ≃* Gal(L/ℚ₂), √5): gives e = 8, f = 4 for L₂ |
| `ArithmeticDyadicField` | 79 | N | built on the explicit ℚ retained field; replaced by the local field L₂ |
| `ArithmeticDyadicGenerators` | 106 | G | to (L, e : D ≃* Gal(L/ℚ₂), √5): gives e = 8, f = 4 for L₂ |
| `ArithmeticDyadicGenus` | 102 | N | built on the explicit ℚ retained field; replaced by the local field L₂ |
| `ArithmeticDyadicInertia` | 87 | G | to (L, e : D ≃* Gal(L/ℚ₂), √5): gives e = 8, f = 4 for L₂ |
| `ArithmeticDyadicInertiaCards` | 37 | G | to (L, e : D ≃* Gal(L/ℚ₂), √5): gives e = 8, f = 4 for L₂ |
| `ArithmeticDyadicIntrinsic` | 84 | G | to (L, e : D ≃* Gal(L/ℚ₂), √5): gives e = 8, f = 4 for L₂ |
| `ArithmeticDyadicModel` | 104 | N | built on the explicit ℚ retained field; replaced by the local field L₂ |
| `ArithmeticDyadicValuation` | 38 | G | to (L, e : D ≃* Gal(L/ℚ₂), √5): gives e = 8, f = 4 for L₂ |
| `DyadicAbelianization` | 45 | U | finite group D of order 32 and its certificates; same D at 𝔭₁, 𝔭₂ |
| `DyadicAlgebra` | 238 | U | finite group D of order 32 and its certificates; same D at 𝔭₁, 𝔭₂ |
| `DyadicAugmentation` | 182 | U | finite group D of order 32 and its certificates; same D at 𝔭₁, 𝔭₂ |
| `DyadicCertificates` | 235 | U | finite group D of order 32 and its certificates; same D at 𝔭₁, 𝔭₂ |
| `DyadicClosedPresentation` | 86 | U | finite group D of order 32 and its certificates; same D at 𝔭₁, 𝔭₂ |
| `DyadicDimension` | 62 | U | finite group D of order 32 and its certificates; same D at 𝔭₁, 𝔭₂ |
| `DyadicDimensionCertificate` | 56 | U | finite group D of order 32 and its certificates; same D at 𝔭₁, 𝔭₂ |
| `DyadicFiltration` | 118 | U | finite group D of order 32 and its certificates; same D at 𝔭₁, 𝔭₂ |
| `DyadicFinal` | 57 | U | finite group D of order 32 and its certificates; same D at 𝔭₁, 𝔭₂ |
| `DyadicFirstOrder` | 101 | U | finite group D of order 32 and its certificates; same D at 𝔭₁, 𝔭₂ |
| `DyadicFox` | 207 | U | finite group D of order 32 and its certificates; same D at 𝔭₁, 𝔭₂ |
| `DyadicGenuineFoxInitial` | 159 | U | finite group D of order 32 and its certificates; same D at 𝔭₁, 𝔭₂ |
| `DyadicGraded` | 170 | U | finite group D of order 32 and its certificates; same D at 𝔭₁, 𝔭₂ |
| `DyadicGradedCertificates` | 140 | U | finite group D of order 32 and its certificates; same D at 𝔭₁, 𝔭₂ |
| `DyadicGradedLinear` | 94 | U | finite group D of order 32 and its certificates; same D at 𝔭₁, 𝔭₂ |
| `DyadicGradedMaps` | 152 | U | finite group D of order 32 and its certificates; same D at 𝔭₁, 𝔭₂ |
| `DyadicGroup` | 190 | U | finite group D of order 32 and its certificates; same D at 𝔭₁, 𝔭₂ |
| `DyadicHilbert` | 105 | U | finite group D of order 32 and its certificates; same D at 𝔭₁, 𝔭₂ |
| `DyadicInertiaRadical` | 70 | U | finite group D of order 32 and its certificates; same D at 𝔭₁, 𝔭₂ |
| `DyadicIntrinsicBaseInertia` | 66 | G | to (L, e : D ≃* Gal(L/ℚ₂), √5): gives e = 8, f = 4 for L₂ |
| `DyadicLiteralPresentation` | 175 | U | finite group D of order 32 and its certificates; same D at 𝔭₁, 𝔭₂ |
| `DyadicPresentationIdentities` | 102 | U | finite group D of order 32 and its certificates; same D at 𝔭₁, 𝔭₂ |
| `DyadicTopology` | 16 | U | finite group D of order 32 and its certificates; same D at 𝔭₁, 𝔭₂ |
| `FreeThreeDyadicQuotient` | 77 | U | purely local ℚ₂ theory (G_{ℚ₂}(2), rank 3, genuine relation) |
| `FreeThreeQuadratic` | 150 | U | purely local ℚ₂ theory (G_{ℚ₂}(2), rank 3, genuine relation) |
| `FreeThreeQuadraticTensor` | 64 | U | purely local ℚ₂ theory (G_{ℚ₂}(2), rank 3, genuine relation) |
| `LocalQuadraticModel` | 214 | U | purely local ℚ₂ theory (G_{ℚ₂}(2), rank 3, genuine relation) |
| `PadicTwoFiniteRestriction` | 97 | U | purely local ℚ₂ theory (G_{ℚ₂}(2), rank 3, genuine relation) |
| `PadicTwoGenusField` | 105 | U | purely local ℚ₂ theory (G_{ℚ₂}(2), rank 3, genuine relation) |
| `PadicTwoGlobalGenus` | 117 | A | kummerSigns on G_B; x,y,z vectors at 𝔭₁ (00100000,11110010,10000100) and 𝔭₂ |
| `PadicTwoGlobalMap` | 108 | G | target Ω (normal, corestrict to G_B at split 2); expose normalAbsoluteRestriction |
| `PadicTwoGlobalMapSurjective` | 56 | U/G | surjectivity U; range lemma G |
| `PadicTwoImaginaryNorm` | 46 | U | purely local ℚ₂ theory (G_{ℚ₂}(2), rank 3, genuine relation) |
| `PadicTwoMaximalProTwo` | 236 | U | purely local ℚ₂ theory (G_{ℚ₂}(2), rank 3, genuine relation) |
| `PadicTwoNoCyclicQuartic` | 22 | U | purely local ℚ₂ theory (G_{ℚ₂}(2), rank 3, genuine relation) |
| `PadicTwoNoQuarticCharacter` | 80 | U | purely local ℚ₂ theory (G_{ℚ₂}(2), rank 3, genuine relation) |
| `PadicTwoNormCatalog` | 118 | U | purely local ℚ₂ theory (G_{ℚ₂}(2), rank 3, genuine relation) |
| `PadicTwoQuadraticAction` | 77 | U | purely local ℚ₂ theory (G_{ℚ₂}(2), rank 3, genuine relation) |
| `PadicTwoQuadraticCharacters` | 134 | U | purely local ℚ₂ theory (G_{ℚ₂}(2), rank 3, genuine relation) |
| `PadicTwoQuadraticClosure` | 99 | U | purely local ℚ₂ theory (G_{ℚ₂}(2), rank 3, genuine relation) |
| `PadicTwoQuadraticField` | 117 | U | purely local ℚ₂ theory (G_{ℚ₂}(2), rank 3, genuine relation) |
| `PadicTwoQuadraticModel` | 106 | U | purely local ℚ₂ theory (G_{ℚ₂}(2), rank 3, genuine relation) |
| `PadicTwoQuadraticModelGenerators` | 102 | U | purely local ℚ₂ theory (G_{ℚ₂}(2), rank 3, genuine relation) |
| `PadicTwoQuadraticRelation` | 171 | U | purely local ℚ₂ theory (G_{ℚ₂}(2), rank 3, genuine relation) |
| `PadicTwoRootSigns` | 107 | U/A | local root lemmas U; B tables (signsVector, classRep, local_squares, sqrt241_residue) A |
| `PadicTwoSquareclassIndependence` | 100 | U | purely local ℚ₂ theory (G_{ℚ₂}(2), rank 3, genuine relation) |
| `PadicTwoSquareclasses` | 148 | U | purely local ℚ₂ theory (G_{ℚ₂}(2), rank 3, genuine relation) |
| `PadicTwoSumSquares` | 73 | U | purely local ℚ₂ theory (G_{ℚ₂}(2), rank 3, genuine relation) |
| `PadicTwoUnitImages` | 38 | U | purely local ℚ₂ theory (G_{ℚ₂}(2), rank 3, genuine relation) |
| `PrincipalUnitGradedExponent` | 59 | U | finite group D of order 32 and its certificates; same D at 𝔭₁, 𝔭₂ |
| `SigmaDyadicCompletedRelation` | 119 | G | local halves U (move out); global halves Fin 7 → Fin 8, instantiated at 𝔭₁ and 𝔭₂ |
| `SigmaDyadicFreeMap` | 107 | G | local halves U (move out); global halves Fin 7 → Fin 8, instantiated at 𝔭₁ and 𝔭₂ |
| `SigmaDyadicInertiaCard` | 64 | A | inertia 8 / decomposition 32 in cut quotients where D injects (via L₂) |
| `SigmaDyadicRetainedDiagram` | 93 | G/A | RetainedQuadratic.Q → Q_B; dual functionals per place; layer certificate |

#### G. Group augmentation, Jennings, Fox calculus, Golod–Shafarevich — 73 modules, 9269 lines (WP T8)

| module | lines | port | what / how |
|---|---:|:-:|---|
| `FilteredBasisHilbert` | 100 | U | filtered Hilbert series calculus |
| `FilteredCompletedBlockPresentation` | 110 | G | retained group → parameter (R, ρ, layer 1/2 injectivity, 3 characters); move withDyadicIndices out |
| `FilteredHilbert` | 313 | U | filtered Hilbert series calculus |
| `FilteredHilbertMaps` | 78 | U | filtered Hilbert series calculus |
| `FilteredHilbertPi` | 78 | U | filtered Hilbert series calculus |
| `FilteredLinearInjection` | 66 | U | filtered Hilbert series calculus |
| `FilteredOptimizedGolodShafarevich` | 162 | U/N | theorems U; optimizedTowerPolynomial* N (Sqrt241.towerPolynomial) |
| `GroupAugmentation` | 201 | U | augmentation filtration, dimensionSubgroup, layerMap |
| `GroupAugmentationClassTwo` | 265 | U | ClassTwo.GroupModel β hosts Q_B and U_8 |
| `GroupAugmentationCoefficientInjection` | 144 | U | Fox calculus, characterFoxRetraction |
| `GroupAugmentationCompletedGeneratorLifts` | 142 | U | completed words, CompletedProTwoPresentation/Consequence |
| `GroupAugmentationCompletedPresentation` | 85 | U | completed words, CompletedProTwoPresentation/Consequence |
| `GroupAugmentationCompletedRelations` | 177 | U | completed words, CompletedProTwoPresentation/Consequence |
| `GroupAugmentationCompletedSubstitution` | 77 | U | completed words, CompletedProTwoPresentation/Consequence |
| `GroupAugmentationCompletedWords` | 116 | U | completed words, CompletedProTwoPresentation/Consequence |
| `GroupAugmentationDyadic` | 123 | U | Dyadic.D specific; same D at both dyadic places of B |
| `GroupAugmentationDyadicRanks` | 69 | U | Dyadic.D specific; same D at both dyadic places of B |
| `GroupAugmentationFilteredRows` | 108 | U | induced rows, hilbertPolynomial |
| `GroupAugmentationFoxCharacters` | 96 | U | Fox calculus, characterFoxRetraction |
| `GroupAugmentationFoxDerivative` | 139 | U | Fox calculus, characterFoxRetraction |
| `GroupAugmentationFoxExact` | 131 | U | Fox calculus, characterFoxRetraction |
| `GroupAugmentationFoxHilbert` | 134 | U | Fox calculus, characterFoxRetraction |
| `GroupAugmentationFoxNaturality` | 78 | U | completed words, CompletedProTwoPresentation/Consequence |
| `GroupAugmentationFoxPresentation` | 112 | U | Fox calculus, characterFoxRetraction |
| `GroupAugmentationFoxSubstitution` | 106 | U | Fox calculus, characterFoxRetraction |
| `GroupAugmentationGeneratorHom` | 43 | U | augmentation filtration, dimensionSubgroup, layerMap |
| `GroupAugmentationGenerators` | 160 | U | augmentation filtration, dimensionSubgroup, layerMap |
| `GroupAugmentationGlobalBlocks` | 132 | U | Dyadic.D specific; same D at both dyadic places of B |
| `GroupAugmentationGlobalCommonRow` | 165 | U | Dyadic.D specific; same D at both dyadic places of B |
| `GroupAugmentationHilbert` | 111 | U | induced rows, hilbertPolynomial |
| `GroupAugmentationHilbertShift` | 109 | U | Fox calculus, characterFoxRetraction |
| `GroupAugmentationInducedFox` | 114 | U | induced rows, hilbertPolynomial |
| `GroupAugmentationInducedHilbert` | 192 | U | induced rows, hilbertPolynomial |
| `GroupAugmentationLayerRanks` | 131 | U | augmentation filtration, dimensionSubgroup, layerMap |
| `GroupAugmentationLayers` | 146 | U | augmentation filtration, dimensionSubgroup, layerMap |
| `GroupAugmentationLog` | 109 | U | augmentation filtration, dimensionSubgroup, layerMap |
| `GroupAugmentationMoments` | 58 | U | Fox calculus, characterFoxRetraction |
| `GroupAugmentationNilpotence` | 229 | U | augmentation filtration, dimensionSubgroup, layerMap |
| `GroupAugmentationProTwoFox` | 142 | U | Fox calculus, characterFoxRetraction |
| `GroupAugmentationProductBasis` | 155 | U | induced rows, hilbertPolynomial |
| `GroupAugmentationQuadraticFoxMoments` | 72 | U | Dyadic.D specific; same D at both dyadic places of B |
| `GroupAugmentationRelationBlocks` | 231 | U | Dyadic.D specific; same D at both dyadic places of B |
| `GroupAugmentationRetainedQuadratic` | 165 | A | Q_B := GroupModel on F₂⁸×F₂¹⁵ (card 2²³), ρ₁ ρ₂ : Dyadic.D →* Q_B, layer certificates |
| `GroupAugmentationRetainedQuadraticRelations` | 108 | N | ℚ 16-row elimination; B uses the 21 initials (T6) |
| `GroupAugmentationRowHilbert` | 172 | U | induced rows, hilbertPolynomial |
| `GroupAugmentationStrictness` | 73 | U | augmentation filtration, dimensionSubgroup, layerMap |
| `GroupAugmentationWordDegrees` | 73 | U | augmentation filtration, dimensionSubgroup, layerMap |
| `JenningsAdaptedGenerators` | 263 | U | global_local_kernel_cost (all-n layer injectivity) |
| `JenningsAdaptedLayers` | 140 | U | global_local_kernel_cost (all-n layer injectivity) |
| `JenningsAdaptedProduct` | 154 | U | global_local_kernel_cost (all-n layer injectivity) |
| `JenningsAugmentationBasis` | 79 | U | Jennings/PBW basis of any finite 2-group |
| `JenningsBasisChange` | 216 | U | Jennings/PBW basis of any finite 2-group |
| `JenningsBinaryHilbert` | 46 | U | Jennings/PBW basis of any finite 2-group |
| `JenningsBinaryWords` | 153 | U | Jennings/PBW basis of any finite 2-group |
| `JenningsCollection` | 246 | U | Jennings/PBW basis of any finite 2-group |
| `JenningsDyadicHilbert` | 78 | U | Dyadic.D specific; same D at both dyadic places of B |
| `JenningsDyadicInduction` | 106 | U | Dyadic.D specific; same D at both dyadic places of B |
| `JenningsDyadicRowHilbert` | 104 | U | Dyadic.D specific; same D at both dyadic places of B |
| `JenningsFilteredBasis` | 80 | U | Jennings/PBW basis of any finite 2-group |
| `JenningsFilteredInduction` | 94 | U | global_local_kernel_cost (all-n layer injectivity) |
| `JenningsFilteredSpanning` | 134 | U | Jennings/PBW basis of any finite 2-group |
| `JenningsGeneratedLayers` | 68 | U | Jennings/PBW basis of any finite 2-group |
| `JenningsGeneratorBasis` | 74 | U | Jennings/PBW basis of any finite 2-group |
| `JenningsGenerators` | 122 | U | Jennings/PBW basis of any finite 2-group |
| `JenningsGlobalKernelCost` | 97 | U | global_local_kernel_cost (all-n layer injectivity) |
| `JenningsGroupNormalForm` | 84 | U | Jennings/PBW basis of any finite 2-group |
| `JenningsHomogeneousRelations` | 180 | U | Jennings/PBW basis of any finite 2-group |
| `JenningsInducedKernelHilbert` | 78 | U | Dyadic.D specific; same D at both dyadic places of B |
| `JenningsInitialForms` | 120 | U | Jennings/PBW basis of any finite 2-group |
| `JenningsLayerNormalForm` | 113 | U | Jennings/PBW basis of any finite 2-group |
| `JenningsOrderedBasis` | 112 | U | Jennings/PBW basis of any finite 2-group |
| `JenningsOrderedSpans` | 93 | U | Jennings/PBW basis of any finite 2-group |
| `JenningsWeights` | 135 | U | Jennings/PBW basis of any finite 2-group |

#### H. Cut, local blocks, retained model, truncated Magnus, explicit ℚ retained field — 49 modules, 5213 lines (WP T7, T8, T9)

| module | lines | port | what / how |
|---|---:|:-:|---|
| `ArithmeticCompletedEmbedding` | 73 | N | explicit ℚ retained/completed/canonical field; M is abstract (ρ_B defined through the presentation) |
| `ArithmeticCompletedField` | 82 | N | explicit ℚ retained/completed/canonical field; M is abstract (ρ_B defined through the presentation) |
| `ArithmeticCompletedSquareclasses` | 127 | N | explicit ℚ retained/completed/canonical field; M is abstract (ρ_B defined through the presentation) |
| `ArithmeticLocalBlockCosts` | 127 | A | index 2×C₂, 4×C₂×C₂, 1×Dyadic.D (𝔭₂), 3×C₄; sum = Sqrt241.towerPolynomial at 34/117 |
| `ArithmeticRetainedAugmentation` | 68 | N | explicit ℚ retained/completed/canonical field; M is abstract (ρ_B defined through the presentation) |
| `ArithmeticRetainedCharacters` | 131 | N | explicit ℚ retained/completed/canonical field; M is abstract (ρ_B defined through the presentation) |
| `ArithmeticRetainedField` | 82 | N | explicit ℚ retained/completed/canonical field; M is abstract (ρ_B defined through the presentation) |
| `ArithmeticRetainedGalois` | 59 | N | explicit ℚ retained/completed/canonical field; M is abstract (ρ_B defined through the presentation) |
| `ArithmeticRetainedModel` | 95 | N | explicit ℚ retained/completed/canonical field; M is abstract (ρ_B defined through the presentation) |
| `ArithmeticRetainedModelChoice` | 96 | N | explicit ℚ retained/completed/canonical field; M is abstract (ρ_B defined through the presentation) |
| `ArithmeticRetainedModelGenerators` | 108 | N | explicit ℚ retained/completed/canonical field; M is abstract (ρ_B defined through the presentation) |
| `ArithmeticRetainedQuadraticAction` | 166 | N | explicit ℚ retained/completed/canonical field; M is abstract (ρ_B defined through the presentation) |
| `ArithmeticRetainedRoots` | 47 | A | √−1, √3 in M via E ⊆ M; generalize conjugation_fixes_root from 7 to d > 0 |
| `ArithmeticRetainedSquareclasses` | 126 | N | explicit ℚ retained/completed/canonical field; M is abstract (ρ_B defined through the presentation) |
| `CanonicalRetainedEquiv` | 168 | N | explicit ℚ retained/completed/canonical field; M is abstract (ρ_B defined through the presentation) |
| `CanonicalRetainedField` | 69 | N | explicit ℚ retained/completed/canonical field; M is abstract (ρ_B defined through the presentation) |
| `RetainedDyadicLifts` | 119 | G | centralShear U; dual functionals per dyadic place; regenerated decides |
| `RetainedMagnusCutPresentation` | 64 | A | deep words (z_j⁴, [y_j,z_j]², Frob(29_j)⁴, (F₇²)⁴), retains-and-detects with bound 2¹⁵ |
| `RetainedMagnusGenus` | 101 | G | n = 8, W = Fin 15, conjugation vector as parameter |
| `RetainedQuadraticCutWords` | 198 | A | 21 quadratic forms over Fin 15 (regenerated); odd_word_coordinates U |
| `RetainedQuadraticFox` | 109 | G | retained group, dyadic map and characters as parameters |
| `RetainedQuadraticTopology` | 21 | G | discrete instances for Q_B |
| `RetainedQuadraticUniversal` | 206 | N | explicit ℚ retained/completed/canonical field; M is abstract (ρ_B defined through the presentation) |
| `SigmaCut` | 113 | A | B cut on FiniteFreeProTwo.Carrier 8: 21 quadratic + 2 cubic + 7 deep literal words; Ĝ-level kernel |
| `SigmaCutAbsoluteGenus` | 97 | A | exclusion data for c₁, c₂ (or replaced by the √d argument, T10) |
| `SigmaCutArithmeticWitness` | 89 | A | Ĝ-level detector (σ̂-core of the Magnus kernel), index 2¹⁶, abstract M |
| `SigmaCutCompletedPresentation` | 136 | G/A | Fin 8; the 7th original relator is the genuine 𝔭₂ relation (completed word in the D block) |
| `SigmaCutCyclic` | 123 | G | two real C₂ blocks; three C₄ caps (29₁, 29₂, F₇²) |
| `SigmaCutDyadic` | 103 | A | 𝔭₁ via the genuine relation (consequence), 𝔭₂ via σ̂-conjugated lifts; y₂² literal |
| `SigmaCutDyadicInertia` | 95 | G | per dyadic place / Fin 5 / retained map on G_B |
| `SigmaCutFiniteArithmetic` | 35 | G | per dyadic place / Fin 5 / retained map on G_B |
| `SigmaCutFiniteRestriction` | 47 | G | per dyadic place / Fin 5 / retained map on G_B |
| `SigmaCutInfinite` | 92 | G/A | Fin 8, B blocks, 34/117, generalized dyadic slot |
| `SigmaCutLocalFamily` | 158 | A | B local family (10 blocks + distinguished 𝔭₁) |
| `SigmaCutLocalGenus` | 50 | A | exclusion data for c₁, c₂ (or replaced by the √d argument, T10) |
| `SigmaCutLocalWords` | 141 | A | local words for the 30 cut words (regenerated); originals incl. the non-literal 𝔭₂ relation |
| `SigmaCutOdd` | 98 | G | four C₂×C₂ blocks; Frobenius squares are quadratic words |
| `SigmaCutUnconditional` | 21 | A | B presentation ⇒ infinite cut |
| `TruncatedMagnusAugmentation` | 160 | G | Fin 7 → Fin n (2^584 group), e 0 → conjugation vector, 16 → 21 rows, bound → parameter |
| `TruncatedMagnusCertificates` | 132 | A | regenerated data: 21 rows, 7 + 8 functionals, 8 pairs, 2 dyadic cubics; word lists |
| `TruncatedMagnusConjugacy` | 165 | G | Fin 7 → Fin n (2^584 group), e 0 → conjugation vector, 16 → 21 rows, bound → parameter |
| `TruncatedMagnusConjugacyFlexible` | 93 | G | Fin 7 → Fin n (2^584 group), e 0 → conjugation vector, 16 → 21 rows, bound → parameter |
| `TruncatedMagnusConjugacyIndex` | 83 | G | Fin 7 → Fin n (2^584 group), e 0 → conjugation vector, 16 → 21 rows, bound → parameter |
| `TruncatedMagnusFree` | 126 | G | Fin 7 → Fin n (2^584 group), e 0 → conjugation vector, 16 → 21 rows, bound → parameter |
| `TruncatedMagnusGroup` | 137 | G | Fin 7 → Fin n (2^584 group), e 0 → conjugation vector, 16 → 21 rows, bound → parameter |
| `TruncatedMagnusLinear` | 143 | G | Fin 7 → Fin n (2^584 group), e 0 → conjugation vector, 16 → 21 rows, bound → parameter |
| `TruncatedMagnusPresentationWords` | 134 | A | regenerated data: 21 rows, 7 + 8 functionals, 8 pairs, 2 dyadic cubics; word lists |
| `TruncatedMagnusQuotient` | 73 | G | Fin 7 → Fin n (2^584 group), e 0 → conjugation vector, 16 → 21 rows, bound → parameter |
| `TruncatedMagnusWords` | 127 | A | regenerated data: 21 rows, 7 + 8 functionals, 8 pairs, 2 dyadic cubics; word lists |

#### I. Levels, local indices, prime freedom, historical endpoints — 41 modules, 3118 lines (WP T9, T10)

| module | lines | port | what / how |
|---|---:|:-:|---|
| `AbsoluteDecompositionPrime` | 138 | U | rational-prime indices from absolute image cards; generic Galois/level tools |
| `AbsoluteLocalCompactness` | 93 | G | compactness U; finitePlaceDecompositionToMaximalProPOutside → target Ω |
| `AbsolutePrimeImages` | 59 | U | rational-prime indices from absolute image cards; generic Galois/level tools |
| `AbsolutePrimeIndices` | 73 | U | rational-prime indices from absolute image cards; generic Galois/level tools |
| `FullResult` | 34 | N | historical ℚ endpoints (reached only via RetainedDyadicDifferentReduction → FullResultReduced) |
| `FullResultReduced` | 96 | N | historical ℚ endpoints (reached only via RetainedDyadicDifferentReduction → FullResultReduced) |
| `GaloisBaseEquiv` | 62 | U | rational-prime indices from absolute image cards; generic Galois/level tools |
| `GaloisEmbeddingConjugation` | 23 | U | rational-prime indices from absolute image cards; generic Galois/level tools |
| `GaloisEmbeddingImageCard` | 30 | U | rational-prime indices from absolute image cards; generic Galois/level tools |
| `GaloisEmbeddingRestriction` | 95 | U | rational-prime indices from absolute image cards; generic Galois/level tools |
| `GaloisFiniteQuotientField` | 85 | U | rational-prime indices from absolute image cards; generic Galois/level tools |
| `GaloisFixedArithmetic` | 71 | G | RetainedField → M (√−1, √3 ∈ M), 7 → 3, 4096 → 65536, Sqrt241 thetaMin (shared with stream A) |
| `GaloisPrimeConjugation` | 59 | U | rational-prime indices from absolute image cards; generic Galois/level tools |
| `GaloisQuotientDescent` | 35 | U | rational-prime indices from absolute image cards; generic Galois/level tools |
| `GaloisQuotientTower` | 151 | U | rational-prime indices from absolute image cards; generic Galois/level tools |
| `GaloisRetainedFamily` | 123 | G | RetainedField → parameter M with √−1; 4096 → n |
| `GenusLocalExclusions` | 52 | A | prime freedom via ℚ(√d) ⊂ E, d = −15, −2, −1, −3, −1 at 2, 3, 5, 7, 29 |
| `ImaginarySevenUnramified` | 146 | G | √7 → √3 (stream A's entireness item M2) |
| `ProfiniteQuotientTower` | 115 | U | rational-prime indices from absolute image cards; generic Galois/level tools |
| `QuadraticSevenConjugation` | 64 | G | √7 → √3 (stream A's entireness item M2) |
| `QuadraticSevenDescent` | 75 | G | √7 → √3 (stream A's entireness item M2) |
| `RelativeUnramifiedIndices` | 41 | U | rational-prime indices from absolute image cards; generic Galois/level tools |
| `RelativeUnramifiedOdd` | 106 | U | rational-prime indices from absolute image cards; generic Galois/level tools |
| `RelativeUnramifiedSigma` | 68 | G | finiteUnramified_of_base_and_ramificationIdxIn_eq (K/B unramified outside S, equal e at 2, 3, 5) |
| `RetainedSelectedIndices` | 37 | A | M's local images/indices (lower bounds via ρ_B, upper via cut) |
| `RetainedSelectedLocalData` | 52 | A | M's local images/indices (lower bounds via ρ_B, upper via cut) |
| `SIntegerWitnessAnalytic` | 85 | N | historical ℚ endpoints (reached only via RetainedDyadicDifferentReduction → FullResultReduced) |
| `SIntegerWitnessAsymptotics` | 68 | N | historical ℚ endpoints (reached only via RetainedDyadicDifferentReduction → FullResultReduced) |
| `SIntegerWitnessGaloisFamily` | 73 | N | historical ℚ endpoints (reached only via RetainedDyadicDifferentReduction → FullResultReduced) |
| `SIntegerWitnessInfiniteQuotient` | 99 | N | historical ℚ endpoints (reached only via RetainedDyadicDifferentReduction → FullResultReduced) |
| `SIntegerWitnessQuadratic` | 63 | N | historical ℚ endpoints (reached only via RetainedDyadicDifferentReduction → FullResultReduced) |
| `SIntegerWitnessRetained` | 53 | N | historical ℚ endpoints (reached only via RetainedDyadicDifferentReduction → FullResultReduced) |
| `SIntegerWitnessRetainedDescent` | 62 | N | historical ℚ endpoints (reached only via RetainedDyadicDifferentReduction → FullResultReduced) |
| `SigmaCutDyadicDecomposition` | 95 | A | dyadic decomposition range = image of D (both places), card 32 |
| `SigmaCutExtraDecomposition` | 90 | A | 29: C₄; 7: range zpowers F₇, card 8 |
| `SigmaCutFamily` | 145 | A | levels, toLevel, levelRetained, levelConjugation, index 2¹⁶ |
| `SigmaCutFamilyPrimeFreedom` | 52 | A | c moves primes above 2, 3, 5, 29, 7 (√d argument) |
| `SigmaCutFamilyRamification` | 47 | A | rational e, f of levels at the five primes; K_j/M unramified |
| `SigmaCutFiniteLocalData` | 85 | A | selected_local_image_cards for Fin 5 |
| `SigmaCutOddDecomposition` | 74 | A | 3, 5: range = closure{τ, φ}, cards 2 and 4 |
| `SigmaCutTarget` | 44 | N | historical ℚ endpoints (reached only via RetainedDyadicDifferentReduction → FullResultReduced) |

#### K. Root discriminant — 10 modules, 2683 lines (WP T11)

| module | lines | port | what / how |
|---|---:|:-:|---|
| `ArithmeticRetainedDiscriminant` | 190 | U | generic UnramifiedAtOddPrimes.not_dvd_absNorm_differentIdeal etc.; ℚ part is a black-box input to T11 |
| `GenusDiscriminant` | 408 | U/N | qNegThree_discr, qFive_discr, chosenGenus_natAbs_discr used by T11; genus-compositum method N for E_B |
| `IntegralClosureValuationTower` | 50 | U | generic |
| `NumberFieldNumericInvariance` | 61 | U | generic |
| `RetainedDiscriminantBridge` | 150 | A | log rd from exact factorization for M (T11 D4) |
| `RetainedDyadicDifferentComplement` | 535 | U | black box: ℚ retained v₂(disc) ≤ (9/4)[R:ℚ] for T11 route T; template for route β |
| `RetainedDyadicDifferentGenerator` | 367 | U | imported as part of the ℚ black box; template for route β |
| `RetainedDyadicDifferentInertia` | 294 | U | imported as part of the ℚ black box; template for route β |
| `RetainedDyadicDifferentNorm` | 416 | U | black box: ℚ retained v₂(disc) ≤ (9/4)[R:ℚ] for T11 route T; template for route β |
| `RetainedDyadicDifferentReduction` | 212 | U | generic relativeDifferentTwoExponent; B copies must not import FullResultReduced |

#### L. Analytic modules in the tower cone — 4 modules, 483 lines (stream B)

| module | lines | port | what / how |
|---|---:|:-:|---|
| `FiniteEulerCorrection` | 147 | U | analytic tools (stream B) |
| `FixedZetaCertificate` | 159 | N | ℚ numbers (template for stream B) |
| `PrimeDebitLogDerivative` | 70 | U | analytic tools (stream B) |
| `RetainedFixedZetaReduction` | 107 | N | historical ℚ endpoints (reached only via RetainedDyadicDifferentReduction → FullResultReduced) |

#### Z. Other — 1 module, 55 lines (WP T10)

| module | lines | port | what / how |
|---|---:|:-:|---|
| `SigmaRetainedInertia` | 55 | A | M's local images/indices (lower bounds via ρ_B, upper via cut) |

## 3. Work packages

Module paths are under `UnitDistance/Sqrt241/`; all new files follow the
CONVENTIONS header. "Retype" means: copy the ℚ file into the B tree and
replace `ℚ` by a variable number field `F` (or by `B`), `AlgebraicClosure ℚ`
by `AlgebraicClosure F`, leaving the verified ℚ cone byte-identical.
Estimates are agent-days (one agent, continuous work), in the calibration of
SQRT241_PORT.md §3; they are ranges, not commitments.

### T0 — Generic maximal pro-p machinery over a number field (retype)

*Inputs:* none (upstream `IsUnramifiedAtFinitePlacesOutside` and friends are
generic). *Files:* `ProP/{FinitePExtension, FinitePExtensionSupport,
MaximalProPOutside, MaximalProPGroup, ProPOpenNormalStage, ProPStageRestriction,
ProPStageLocalConditions, AbsoluteProPRestriction, AbsoluteProPUnramified,
AbsoluteProPFactor}.lean` (1.2k lines to retype), then `Tower/OmegaB.lean`.
Expose the private `normalAbsoluteRestriction` (as `absoluteToNormal`), it is
needed in T5.

```lean
namespace UnitDistance.Sqrt241.ProP
variable (F : Type) [Field F] [NumberField F]
def maximalProPOutside (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 F))) : IntermediateField F (AlgebraicClosure F)
theorem maximalProPOutside_isGalois : IsGalois F (maximalProPOutside F p T)
theorem isAdmissibleFiniteLayer_iff_le_maximalProPOutside (E : FiniteGaloisIntermediateField F (AlgebraicClosure F)) :
  IsAdmissibleFiniteLayer F p T E ↔ E.toIntermediateField ≤ maximalProPOutside F p T
theorem maximalProPOutside_galoisGroup_hasPGroupOpenNormalBasis [Fact p.Prime] :
  ProCGroups.ProC.HasPGroupOpenNormalBasis p Gal(maximalProPOutside F p T / F)
def absoluteToMaximalProPOutside : Field.absoluteGaloisGroup F →ₜ* Gal(maximalProPOutside F p T / F)
theorem absoluteToMaximalProPOutside_inertia (v) (hv : v ∉ T) (σ : finitePlaceAbsoluteInertiaSubgroup F v) :
  absoluteToMaximalProPOutside F p T (finitePlaceAbsoluteDecompositionInclusion F v σ.1) = 1
theorem exists_maximalProPOutside_factor_of_inertia_trivial … -- as in ℚ, with F
def proPOpenNormalStage (U : OpenNormalSubgroup Gal(maximalProPOutside F p T / F)) : FinitePExtension F p T
namespace UnitDistance.Sqrt241.Tower
def S : Set (HeightOneSpectrum (𝓞 B)) := {v | (30 : 𝓞 B) ∈ v.asIdeal}
def SFin : Finset (HeightOneSpectrum (𝓞 B))            -- the six primes P2,P2',P3,P3',P5,P5' of Base/Primes
theorem mem_SFin_iff (v) : v ∈ SFin ↔ v ∈ S ;  theorem SFin_card : SFin.card = 6   -- (≤ 6 suffices)
def OmegaB : IntermediateField B (AlgebraicClosure B) := ProP.maximalProPOutside B 2 S
```
*Effort:* 1–1.5. *Risk:* low (instance search with `F = ↥B`, heartbeats).

### T1 — Bridge between the worlds; Ω Galois over ℚ

*Inputs:* T0, `Base.Field` (σ, B Galois over ℚ). *File:* `Tower/Bridge.lean`,
`Tower/ConjugationTransport.lean`.

```lean
-- conjugation transport (the only genuinely new lemma here)
theorem IsUnramifiedAtFinitePlacesOutside.map_semilinear
    {F : Type} [Field F] [NumberField F] (τ : AlgebraicClosure F ≃+* AlgebraicClosure F)
    (τ₀ : F ≃+* F) (hτ : ∀ a, τ (algebraMap F _ a) = algebraMap F _ (τ₀ a))
    (T : Set (HeightOneSpectrum (𝓞 F))) (E : IntermediateField F (AlgebraicClosure F)) [FiniteDimensional F E]
    (hE : IsUnramifiedAtFinitePlacesOutside F E T) :
    IsUnramifiedAtFinitePlacesOutside F (E.map_semilinear τ hτ) (τ₀.comapHeightOneSpectrum ⁻¹' T)
    -- new: E.map_semilinear = τ(E) as an F-subfield; τ₀.comapHeightOneSpectrum = induced bijection of primes
theorem OmegaB_stable (τ : AlgebraicClosure B ≃ₐ[ℚ] AlgebraicClosure B) : OmegaB.map_semilinear τ _ = OmegaB
instance : IsGalois ℚ (OmegaB.restrictScalars ℚ)
-- two closures
instance : IsAlgClosure B Closure := ⟨inferInstance, inferInstance⟩
def chi : Closure ≃ₐ[B] AlgebraicClosure B := IsAlgClosure.equiv B Closure (AlgebraicClosure B)
def Omega : IntermediateField ℚ Closure
instance : IsGalois ℚ Omega ;  theorem B_le_Omega : B ≤ Omega
abbrev Ghat := Gal(Omega/ℚ)
def GB : Subgroup Ghat
theorem GB_isOpen : IsOpen (GB : Set Ghat) ;  theorem GB_index : GB.index = 2 ;  instance : GB.Normal
theorem mem_GB_iff (g : Ghat) : g ∈ GB ↔ (g ⟨baseRoot, _⟩ : Closure) = baseRoot
def bridge : Gal(OmegaB/B) ≃ₜ* GB           -- ContinuousMulEquiv.ofBijectiveCompactToT2
theorem GB_hasPGroupOpenNormalBasis : HasPGroupOpenNormalBasis 2 GB
theorem Ghat_hasPGroupOpenNormalBasis : HasPGroupOpenNormalBasis 2 Ghat  -- normal cores; |Ĝ/G_B| = 2
def sigmaHat : Ghat ;  theorem sigmaHat_not_mem : sigmaHat ∉ GB
-- maximality in the ℚ-world form (used by T3 and T11)
theorem le_Omega_of_admissible (K : IntermediateField ℚ Closure) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hB : B ≤ K) (h2 : IsPGroup 2 Gal(K/ℚ))
    (hS : IsUnramifiedAtFinitePlacesOutside B (K.extendScalars hB) S) : K ≤ Omega
```
The transport lemma is proved by twisting the B-algebra structure of τ(E) by
τ₀ and applying upstream `IsUnramifiedAtFinitePlacesOutside.congrTop`
(`RamificationSupportTransport.lean`; only B-linear today); the base twist
changes neither the ring map image nor `Algebra.IsUnramifiedAt`. Upstream
`InfiniteGaloisCorrespondence.semilinearRingEquivPreimageIntermediateField`
and `algEquiv_autCongr_continuous` give the field and continuity plumbing.
*Effort:* 1.5–2.5. *Risk:* medium (semilinear transport of
`Algebra.IsUnramifiedAt`, two `Algebra ℚ` structures on `AlgebraicClosure B`:
fix `DivisionRing.toRatAlgebra` once; `Algebra.IsAlgebraic ℚ (AlgebraicClosure B)`
is not inferred).

### T2 — Base arithmetic and the canonical genus field (with the Base stream)

*Inputs:* `Base/*` (other stream: `B`, `sigma`, `𝓞 B = ℤ[ω]`, `eps`,
`pi2 … pi29'`, `P2 … P7`, `isPrincipalIdealRing`, `classNumber_eq_one`,
`Units.unit_eq_mul_sq`); stream B's `Genus/*` (E Galois over ℚ of degree 512
and its local types — reuse, do not duplicate). *Files:* `Base/Selmer.lean`,
`Genus/Kummer.lean` (signEquiv), `Genus/Unramified.lean`, `Genus/Signs.lean`
(coordinate with stream B on names).

```lean
def alphaB (i : Fin 8) : B          -- CanonicalGenus.radicandA i + CanonicalGenus.radicandB i * Base.sqrt241
theorem alpha_independent (w : Fin 8 → ZMod 2)
    (h : IsSquare (∏ i, alphaB i ^ (w i).val)) : w = 0             -- valuations at P2..P5', signs at v₁, v₂
theorem mem_V_of_even_outside_S (x : Bˣ)
    (h : ∀ v, v ∉ S → Even (Multiplicative.toAdd (v.valuationOfNeZero x))) :
    ∃ (w : Fin 8 → ZMod 2) (c : Bˣ), (x : B) = (∏ i, alphaB i ^ (w i).val) * c ^ 2   -- h(B)=1, units
-- the canonical E (CanonicalGenus.field, unchanged definitions)
theorem CanonicalGenus.base_le_field : B ≤ CanonicalGenus.field
abbrev CanonicalGenus.fieldB : IntermediateField B Closure := CanonicalGenus.field.extendScalars base_le_field
instance : IsGalois ℚ CanonicalGenus.field                   -- normal_iff_forall_map_le'; σ maps √ε ↦ ±√−1√ε/ε etc.
def CanonicalGenus.signEquiv : Gal(fieldB/B) ≃* Multiplicative (Fin 8 → ZMod 2)   -- GeneratedQuadraticSigns.rootSignHom
theorem CanonicalGenus.finrank_Q : Module.finrank ℚ CanonicalGenus.field = 512
theorem CanonicalGenus.unramifiedOutside : IsUnramifiedAtFinitePlacesOutside B fieldB S  -- isUnramifiedAt_of_integral_product + sup
theorem CanonicalGenus.signs (φ) (c) (hc : IsConj φ c) (hφ : φ.comp (algebraMap B _) = Base.complexEmbPlus) :
    signEquiv c = ofAdd ![1,0,1,1,1,0,1,0]     -- and ![1,1,0,0,0,1,0,1] for complexEmbMinus
theorem sqrt3_mem : ∃ r ∈ CanonicalGenus.field, r ^ 2 = 3   -- π₃π₃′ = −3 ;  similarly √−1, √2, √5
```
*Effort:* 1–1.5 beyond the Base stream. *Risk:* low–medium (the definitions of
`CanonicalGenus` are frozen and live under `open scoped Classical`).

### T3 — Generators: H¹ = 8, genus field, free source

*Inputs:* T0, T1, T2. *Files:* `Genus/Kummer.lean`, `Genus/Classification.lean`,
`Genus/Frattini.lean`, `Genus/Source.lean`.

```lean
theorem not_isUnramifiedAt_of_odd_valuation {F L} [..] (a : Fˣ) (β : L) (hβ : β ^ 2 = algebraMap F L a)
    (v : HeightOneSpectrum (𝓞 F)) (hv : Odd (Multiplicative.toAdd (v.valuationOfNeZero a)))
    (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal] : ¬ Algebra.IsUnramifiedAt (𝓞 F) w.asIdeal
theorem exists_sq_generator {F L} [Field F] [CharZero F] [Field L] [Algebra F L] [Algebra.IsQuadraticExtension F L] :
    ∃ (a : Fˣ) (β : L), β ^ 2 = algebraMap F L a ∧ IntermediateField.adjoin F {β} = ⊤
def genusFieldB : IntermediateField B (AlgebraicClosure B)     -- = chi-image of CanonicalGenus.fieldB
theorem quadratic_le_genus (L : IntermediateField B (AlgebraicClosure B)) [FiniteDimensional B L]
    (h2 : Module.finrank B L = 2) (hL : IsUnramifiedAtFinitePlacesOutside B L S) : L ≤ genusFieldB
theorem genusFieldB_le_OmegaB : genusFieldB ≤ OmegaB
theorem frattini_eq : closedPowerCommutator 2 Gal(OmegaB/B) =
    (IntermediateField.restrict genusFieldB_le_OmegaB).fixingSubgroup
theorem OmegaB_generatorRank : topologicalGeneratorRank Gal(OmegaB/B) = 8
-- ℚ-world form (through bridge)
def genusLabel : GB →ₜ* Multiplicative (Fin 8 → ZMod 2)     -- action on CanonicalGenus.genusRoot
theorem genusLabel_ker : genusLabel.toMonoidHom.ker = closedPowerCommutator 2 GB
def gen (i : Fin 8) : GB ;  theorem gen_label (i) : genusLabel (gen i) = ofAdd (Pi.single i 1)
def freeMap : FiniteFreeProTwo.Carrier 8 →ₜ* GB
theorem freeMap_surjective ; theorem freeMap_minimal : freeMap.toMonoidHom.ker ≤ closedPowerCommutator 2 _
theorem freeMap_generator (i) : freeMap (FiniteFreeProTwo.generator 8 i) = gen i
def relationKernel : ClosedSubgroup (FiniteFreeProTwo.Carrier 8)
def freeQuotientEquiv : (FiniteFreeProTwo.Carrier 8 ⧸ (relationKernel : Subgroup _)) ≃ₜ* GB
theorem canonicalGenus_le_Omega : CanonicalGenus.field ≤ Omega  -- E ≤ Ω (T1 le_Omega_of_admissible + T2)
```
Generic tools (reuse): `ProTwoElementaryQuotient.{closedPowerCommutator_eq_ker,
generatorRank_of_powerCommutator_card}`, `FiniteFreeProTwo.exists_minimal_surjection_for_generators`,
`GeneratedQuadraticSigns.rootSignHom_{surjective,injective}`,
`QuadraticRamification.isUnramifiedAt_of_integral_product`, Mathlib
`Algebra.IsQuadraticExtension.exists_algEquiv_quadraticAlgebra`,
`HeightOneSpectrum.valuation_liesOver`, `Algebra.isUnramifiedAt_iff_map_eq`,
upstream `mem_idealNthPowerRadicalKummerSubgroup_iff_valuation`,
`range_ordinaryUnitToIdealRadical_eq_ker_toClassTorsion`.
*Effort:* 1.5–2. *Risk:* medium (no ℚ template for the Kummer classification;
`Algebra ↥B ↥E` diamonds between `algebra'` and `extendScalars`).

### T4 — Relation bound H²(G_B) ≤ 7 (critical path, highest risk)

*Inputs:* T0 (stages over B), T2 (units mod squares ⟨−1, ε⟩, S), Base.
*Files:* `H2/InfinitePlaceNorm.lean`, `H2/ImaginaryBase.lean`,
`H2/PairDetection.lean`, `H2/KummerCount.lean`, `H2/Character.lean`,
`H2/LiftCorrection.lean`, `H2/AbsoluteKernel.lean`, `H2/Bound.lean`.

Mathematics. For a stage E/B (finite Galois 2-extension unramified outside
S), let f be the field-unit Kummer map and g the S-place localization. Over
ℚ, finite places detect field-unit H² (via ℚ(i) and the single infinite
place) so ker g ≤ ker f. Over B the product formula leaves the two real
places: the finite-detection kernel Z_{E/B} has at most two elements, so
|range f| ≤ |range g|·|f(ker g)| ≤ 2⁶·2. The argument is the ℚ one with
three changes (all checked against the code by the survey):

(a) all-but-one infinite place (generalizes `OneInfinitePlaceNorm`; proof:
`chosenLocalArtin_product_principalIdele` with `Fintype.prod_eq_single v₀`
instead of `Fintype.prod_subsingleton`):
```lean
theorem infinite_local_norm_of_local_norms_away [IsAbelianGalois K L] (x : Kˣ) (v₀ : InfinitePlace K)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), IdeleGroup.finiteComponent v (IdeleGroup.principalIdele K x) ∈
      chosenFinitePlaceLocalNormSubgroup (K := K) (L := L) v)
    (hinf : ∀ v : InfinitePlace K, v ≠ v₀ → IdeleGroup.infiniteComponent v (IdeleGroup.principalIdele K x) ∈
      infiniteTensorNormSubgroup (K := K) (L := L) v) :
    IdeleGroup.infiniteComponent v₀ (IdeleGroup.principalIdele K x) ∈ infiniteTensorNormSubgroup (K := K) (L := L) v₀
theorem global_norm_of_local_norms_away [IsCyclic Gal(L/K)] … : x ∈ globalFieldNormSubgroup K L
```
(b) bounded cyclic detection for B(i)/B (new; `FieldTensorCyclicH2.exists_fieldScalarUnitH2`,
`fieldScalarUnitH2_eq_zero_iff_norm`, `fieldScalarUnitH2_tensor_eq_zero_iff_norm`,
`hasseNormPrinciple_cyclic`; a small multiplicativity lemma for the scalar
representative is needed):
```lean
theorem finiteQuadraticFieldUnitsH2_pair (hG : Nat.card Gal(L/K) = 2) (v₀ v₁ : InfinitePlace K)
    (hK : ∀ v : InfinitePlace K, v = v₀ ∨ v = v₁) :
    ∃ x₀ : groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2, ∀ x,
      (∀ v : HeightOneSpectrum (𝓞 K), (fieldUnitsTensorH2 K L (v.adicCompletion K)).hom x = 0) → x = 0 ∨ x = x₀
def BI : Type := KummerInvariantRadicand.Extension (-1 : B)   -- B(i): NumberField, IsGalois, IsCyclic, IsTotallyComplex
```
(c) image version of the tower lemma (proof of `fieldUnitsH2_finite_detection_tower`
with membership instead of `= 0`), the enlargement E ↦ E(i) over B (retype
of `ImaginaryGaloisEnlargement`/`FiniteFieldImage`), and pair detection:
```lean
theorem fieldUnitsH2_finite_detection_tower_mem_image (hrelative : …) (D : Set (groupCohomology (Rep.ofAlgebraAutOnUnits K F) 2))
    (hlower : ∀ y, (∀ v, (fieldUnitsTensorH2 K F (v.adicCompletion K)).hom y = 0) → y ∈ D) (x) (hx : …) :
    x ∈ (finiteGaloisTowerUnitsH2Inflation K F L).hom '' D
theorem fieldUnitsH2_pair (L : Type) [Field L] [NumberField L] [Algebra B L] [FiniteDimensional B L]
    [IsGalois B L] (hP : IsPGroup 2 Gal(L/B)) :
    ∃ x₀ : groupCohomology (Rep.ofAlgebraAutOnUnits B L) 2, ∀ x,
      (∀ v : HeightOneSpectrum (𝓞 B), (fieldUnitsTensorH2 B L (v.adicCompletion B)).hom x = 0) → x = 0 ∨ x = x₀
```
(d) counting:
```lean
theorem natCard_range_le_of_map_ker (f : A →+ B') (g : A →+ C) [Finite f.range] (k : ℕ)
    (hk : Finite (f.ker.map g) ∧ Nat.card (f.ker.map g) ≤ k) : Finite g.range ∧ Nat.card g.range ≤ k * Nat.card f.range
theorem finiteKummerH2_range_natCard_le_of_pair (L) [..] (hmu : (primitiveRoots 2 B).Nonempty) (hP : IsPGroup 2 Gal(L/B))
    (hfin : ∀ v, v ∉ SFin → ChosenFinitePlaceIsUnramified (K := B) (L := L) v) :
    Finite (finiteKummerCoefficientH2Map B L (2 : ℕ+) hmu).hom.toAddMonoidHom.range ∧
      Nat.card (finiteKummerCoefficientH2Map B L (2 : ℕ+) hmu).hom.toAddMonoidHom.range ≤ 2 ^ 6 * 2
```
(e) the stage-kernel theorem over B: `CentralLiftCorrection` and
`ProTwoH2AbsoluteKernel` retyped to F with the ℚ-only `hThree` replaced by a
hypothesis `hchar : PrescribedQuadraticInertia F T`:
```lean
def PrescribedQuadraticInertia (F : Type) [Field F] [NumberField F] (T : Set (HeightOneSpectrum (𝓞 F))) : Prop :=
  ∀ (S' : Finset (HeightOneSpectrum (𝓞 F)))
    (χ : ∀ v : ↥S', finitePlaceAbsoluteDecompositionGroup F v.1 →ₜ* Multiplicative (ZMod 2)),
    ∃ γ : Field.absoluteGaloisGroup F →ₜ* Multiplicative (ZMod 2),
      (∀ v : ↥S', v.1 ∉ T → ∀ σ : finitePlaceAbsoluteInertiaSubgroup F v.1,
          χ v σ.1 = γ (finitePlaceAbsoluteDecompositionInclusion F v.1 σ.1)) ∧
      (∀ v, v ∉ S' → v ∉ T → ∀ σ : finitePlaceAbsoluteInertiaSubgroup F v,
          γ (finitePlaceAbsoluteDecompositionInclusion F v σ.1) = 1)
theorem prescribedQuadraticInertia_B : PrescribedQuadraticInertia B S
theorem finiteKummerContinuousH2Map_ker_le_proPStageInflation_ker (hchar : PrescribedQuadraticInertia F T) (U) (hmu) : …
```
Route R for `prescribedQuadraticInertia_B` (recommended by the survey; ≈ 600–800
lines, mostly adapted): the ideal-square radical of B is ⟨−1, ε⟩ (h(B) = 1,
`Base.Units.unit_eq_mul_sq`); correct the local family at the two dyadic
places (both in S) by multiples of the restrictions of the characters of
B(√−1) and B(√ε) so that the reciprocity functional kills −1 and ε (the
matrix of local values is invertible: f₋(−1) = 0, f₋(ε) = 1, f_ε(−1) = 1,
by the product formula and the signs of ε at v₁, v₂), then call the generic
upstream realizer `exists_absoluteCharacter_of_finiteSupport_radical_annihilator`
(`UPRR/Radical/FiniteSupportInertiaCorrection.lean`, any F, any prime n).
Private generic helpers (`quadraticAbsoluteCharacter*`, `localRadicalValue*`
in `NegativeThreeCharacter.lean`) need `import all` or a copy.
Route D (character of B(√∏π_v)) is shorter to state but needs two local facts
not found in the library (odd valuation ⇒ absolute inertia acts nontrivially;
uniqueness of the nontrivial quadratic character of odd inertia).

(f) endpoint:
```lean
theorem OmegaB_h2 : FiniteDimensional (ZMod 2) (continuousCohomologyZModPLifted 2 Gal(OmegaB/B) 2) ∧
    Module.finrank (ZMod 2) (continuousCohomologyZModPLifted 2 Gal(OmegaB/B) 2) ≤ 7
theorem GB_h2 : … continuousCohomologyZModPLifted 2 GB 2 … ≤ 7     -- via bridge
```
(`finiteDimensional_and_finrank_degree_two_le_of_inflationRange_natCard 7`, generic.)
*Effort:* 3–4.5 (a–d: 1–1.5; B(i) and enlargement: 0.5; e: 1.5–2; f: 0.5).
*Risk:* high but localized: every deep input (cyclic Hasse, Artin product,
H¹(G, C_L) = 0 via `finiteFieldUnitsIdeleH2Map_injective_of_isPGroup`,
S-place Kummer cardinality) is generic upstream; the new parts are finite
bookkeeping plus route R. Fallback if (e) stalls: T6–T9 do not need H² ≤ 7
as a hypothesis-free fact to be *developed*: state them with `hbound` as a
parameter (as the ℚ `SigmaRelatorGeneration.sigmaOriginalRelator_generates_of_h2_bound` does).

### T5 — Local maps into Ω, normalization, labels (ℚ-world)

*Inputs:* T1, T2. *Files:* `Local/Maps.lean`, `Local/Normalize.lean`,
`Local/DyadicSigns.lean`, `Local/OddSigns.lean`, `Local/Frobenius.lean`,
`Local/TamePairs.lean`, `Local/DyadicCut.lean`, `Local/DyadicIndices.lean`.

T5a (needed early by T6, T8): the definitions — `decompositionMap`,
`decompositionMapB`, `frame`, `localMapB`, `dyadicLocal`, `conj₁`, `conj₂`,
the tame elements, `frob29`, `frob7`. T5b: labels, tame pairs, the ℚ₂ local
cut and L₂.

Generalize the target of the ℚ local maps from `maximalSigmaProTwo` to a
normal `Omega` (`SigmaUnramifiedFrobenius`, `SigmaAbsoluteLocalRestriction`,
`SigmaFinitePrimeImages`, `PadicTwoGlobalMap`, `SigmaOddFiniteGeneration`,
`SigmaOddLocalImage`): the only use of the target is restriction
(`normalAbsoluteRestriction`, private today) and the pro-2 basis.

```lean
def absoluteToNormal (Ω : IntermediateField ℚ Closure) [Normal ℚ Ω] : Field.absoluteGaloisGroup ℚ →ₜ* Gal(Ω/ℚ)
def decompositionMap (p : Nat.Primes) : PrimeCompletion.AbsoluteDecomposition p →ₜ* Ghat
theorem decomposition_fixes_baseRoot (p) (h : IsSquare (241 : ℚ_[p.val])) (d) : (d : Field.absoluteGaloisGroup ℚ) baseRoot = baseRoot
def decompositionMapB (p) (h) : PrimeCompletion.AbsoluteDecomposition p →ₜ* GB
theorem inertia_killed (p : Nat.Primes) (hp : p.val ∉ ({2, 3, 5, 241} : Finset ℕ)) (σ : PrimeCompletion.AbsoluteInertia p) :
    decompositionMap p σ.val = 1
-- normalization (the chosen place of Closure above p lies over either prime of B)
def placeRoot (p) (h : IsSquare (241 : ℚ_[p.val])) : ℚ_[p.val]     -- image of baseRoot under the chosen place
def frame (k : Fin 4) : Ghat := if firstPrime k (placeRoot _ _) then 1 else sigmaHat   -- k : 2, 3, 5, 29
def localMapB (k : Fin 4) (P : Fin 2) : PrimeCompletion.AbsoluteDecomposition (splitPrime k) →ₜ* GB
    -- conj by (if P = 1 then sigmaHat else 1) * frame k, composed with decompositionMapB
-- square classes (Hensel; both roots of 241; both are needed)
theorem sqrt241_residue_two (c : Closure) (hc : c ^ 2 = 241) … : ∃ (P : Fin 2) (t : ℤ_[2]), image c = rootResidue P + 32 * t   -- 7, 25
theorem local_squares_two (P : Fin 2) (t : ℤ_[2]) (i : Fin 8) :
    IsSquare ((radicandA i + radicandB i * ((rootResidue P + 32 * t : ℤ_[2]) : ℚ_[2])) * classRep P i)
      -- classRep 𝔭₁ = ![-1,-5,-10,-5,1,5,-5,1], 𝔭₂ = ![-1,5,5,10,5,1,1,-5]
theorem radicand_squareClass (k : Fin 3) (r : ℚ_[oddSplit k]) (hr : r ^ 2 = 241) (i : Fin 8) :
    ∃ u ≠ 0, radicandAt r i = squareClass k (isFirst k r) i * u ^ 2   -- tables at 3, 5, 29 (survey table)
theorem not_isSquare_241_Q7 : ¬ IsSquare (241 : ℚ_[7])
-- labels
def dyadicLocal (P : Fin 2) : PadicTwoMaximalProTwo.Group →ₜ* GB   -- PadicTwoGlobalMap.toGlobal pattern, target GB, normalized
theorem dyadic_labels (P : Fin 2) (i : Fin 3) :
    genusLabel (dyadicLocal P (PadicTwoQuadraticRelation.generator i)) = ofAdd (binaryVector 8 (![![79, 4, 110], ![129, 8, 158]] P i))
    -- (a, b, c) = rec(−1), rec(5), rec(2); (x, y, z) = (b, a, a·c):
    -- 𝔭₁: x 00100000, y 11110010, z 10000100; 𝔭₂: x 00010000, y 10000001, z 11111000 (bit k ↔ α_k)
theorem odd_generating_relation (k : Fin 2) (P : Fin 2) :            -- 𝔮_P (k = 0), 𝔯_P (k = 1)
    ∃ τ φ, genusLabel (τ-image) = ofAdd (tauVec k P) ∧ genusLabel (φ-image) = ofAdd (phiVec k P) ∧
      φ * τ * φ⁻¹ = τ ^ ![3, 5] k ∧ ∀ U : OpenNormalSubgroup GB, ProfiniteTame.quotientGenerates … U τ φ
theorem frob29_label (P : Fin 2) : genusLabel (frob29 P) = ofAdd (![00100111, 00011011] P)
theorem frob7_not_mem : frob7 ∉ GB ;  theorem frob7_sq_label : genusLabel ⟨frob7 ^ 2, _⟩ = ofAdd 01110000
theorem decomposition7_range (q : Ghat →ₜ* H) [DiscreteTopology H] :
    (q.comp (decompositionMap 7)).toMonoidHom.range = Subgroup.zpowers (q frob7)
-- conjugation relation (c₂ and all second-prime data)
theorem genusLabel_conj (g : GB) : genusLabel ⟨sigmaHat * g * sigmaHat⁻¹, _⟩ = ofAdd (sigmaMatrix (genusLabel g).toAdd)
    -- sigmaMatrix v = ![v 0, v 0 + v 1, v 0 + v 3, v 0 + v 2, v 5, v 4, v 7, v 6]
def conj₁ : GB ; theorem conj₁_isConj : IsConj phi₁ conj₁ ; theorem conj₁_label : … = ofAdd 10111010
def conj₂ : GB := ⟨sigmaHat * conj₁ * sigmaHat⁻¹, _⟩ ; theorem conj₂_label : … = ofAdd 11000101
-- ℚ₂-local cut (new, local; survey "Q3(c),(d)")
def localCut : PadicTwoMaximalProTwo.Group →* Dyadic.D
theorem ker_eq_localCut_ker {H} (φ : PadicTwoMaximalProTwo.Group →ₜ* H) (f : Dyadic.D →* H) (hf : Function.Injective f)
    (hφ : φ = f ∘ localCut) : φ.ker = localCut.ker
def L₂ : IntermediateField ℚ_[2] (PadicTwoQuadratic.QuadraticField)   -- fixed field of ker localCut; degree 32, Gal ≅ D
theorem L₂_indices : e = 8 ∧ f = 4     -- generalized ArithmeticDyadic{Abelianization,Valuation,Inertia,Intrinsic,InertiaCards}
```
Label transfer: the ℚ files use `GaloisEmbedding.restriction_independent` /
`decomposition_label_independent`, which need `IsMulCommutative Gal(A/ℚ)`;
Gal(E/ℚ) is not abelian. Absorb the embedding change into the local embedding
instead (`exists_embedding_change`), so labels are computed at the chosen
place directly. At 7, no integer represents the non-square unit class of
ℚ₄₉, so `OddTameRadicalAction.frobenius_unit_radical` must accept a radicand
in the valuation ring (F₇² acts on √α by (N α / 7)).
*Effort:* 3–4 (maps and normalization 0.5–1; square classes and labels 1;
tame pairs 0.5–1; ℚ₂ local cut and L₂ indices 1). *Risk:* medium (choices of
`IsAlgClosed.lift`, `IsSplittingField.lift`, `IsSepClosed.lift` in the local
chain; the ℚ₂ local cut identification is new).

### T6 — Presentation: 8 generators, 7 relators

*Inputs:* T3, T4 (bound, or as parameter), T5 (labels, genuine relation at
𝔭₂). *Files:* `Presentation/Universal.lean` (generated data),
`Presentation/GenuineInitial.lean`, `Presentation/Relators.lean`,
`Presentation/Generation.lean`.

```lean
-- generic, from OriginalRelatorGeneration
theorem closedNormalClosure_eq_of_initials {m n : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod 2) W]
    (β : (Fin m → ZMod 2) →ₗ[ZMod 2] (Fin m → ZMod 2) →ₗ[ZMod 2] W)
    [TopologicalSpace (ClassTwo.GroupModel β)] [DiscreteTopology (ClassTwo.GroupModel β)]
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] (hG : HasPGroupOpenNormalBasis 2 G) (R : ClosedSubgroup G) [R.Normal]
    (hR : (R : Subgroup G) ≤ closedPowerCommutator 2 G) (ρ : Fin n → R) (q : G →ₜ* ClassTwo.GroupModel β)
    (ℓ : Fin n → W →ₗ[ZMod 2] ZMod 2) (init : Fin n → W) (himage : ∀ i, (q (ρ i)).central = init i)
    (hdual : ∀ i j, ℓ i (init j) = if i = j then 1 else 0)
    [FiniteDimensional (ZMod 2) (continuousCohomologyZModPLifted 2 (G ⧸ (R : Subgroup G)) 2)]
    (hbound : Module.finrank (ZMod 2) (continuousCohomologyZModPLifted 2 (G ⧸ (R : Subgroup G)) 2) ≤ n) :
    closedNormalClosure (Set.range (fun i ↦ (ρ i : G))) = (R : Subgroup G)
-- B data (masks computed by the survey's b_dual.py; certificates by decide +kernel)
def UB.cocycle : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 36 → ZMod 2)
def UB.initial : Fin 7 → (Fin 36 → ZMod 2)    -- masks 2506108509, 17181200803, 7520389136, 26852200480, 42966974464, 39192625152, 606158977
def UB.coordinate : Fin 7 → (Fin 36 → ZMod 2) →ₗ[ZMod 2] ZMod 2   -- masks 4, 2, 20, 34, 524288, 1048578, 7
theorem UB.coordinate_initial : ∀ i j, UB.coordinate i (UB.initial j) = if i = j then 1 else 0   -- decide +kernel
-- the new lemma: image of the genuine ℚ₂ relation in any char-2 bilinear group
theorem genuineRelation_image (β : …) (ψ : PadicTwoQuadraticRelation.Source →ₜ* ClassTwo.GroupModel β)
    (r : PadicTwoQuadraticRelation.Source) (hr : PadicTwoQuadraticRelation.detector r = FreeThreeQuadratic.relation) :
    ψ r = ⟨0, β (ψ a).base (ψ a).base + (β (ψ b).base (ψ c).base - β (ψ c).base (ψ b).base)⟩  -- a, b, c = generators 0,1,2
def relator : Fin 7 → relationKernel   -- ĉ₁², ĉ₂², φ̂τ̂φ̂⁻¹(τ̂^N)⁻¹ at 𝔮₁ 𝔮₂ 𝔯₁ 𝔯₂, lift of the genuine relation at 𝔭₂
theorem relator_initial (i) : (UniversalQuadraticB.freeDetector (relator i)).central = UB.initial i
theorem relator_generates : closedNormalClosure (Set.range fun i => (relator i : FiniteFreeProTwo.Carrier 8)) = relationKernel
theorem dyadicOne_consequence : lift-of-genuine-relation-at-𝔭₁ ∈ closedNormalClosure (Set.range relator)   -- one line
theorem completed_dyadicOne_consequence : CompletedProTwoConsequence originalRelations completedGlobalRelation₁
```
*Effort:* 1.5–2. *Risk:* medium (`genuineRelation_image` needs a copy of
`LocalQuadraticModel.modelHom` for `FreeThreeQuadratic`, ≈ 80–120 lines;
instance overrides on `Fin 8`/`Fin 36` as in `OriginalRelatorGeneration`;
`decide` cost ≈ 2× the ℚ certificates).

### T7 — Finite certificates (generated)

*Inputs:* the vectors of construction.md §3.4 (recomputed, §1.5); lie241
data. *Files:* `scripts/sqrt241/generate_tower_certificates.py` (new; no
generator exists for the ℚ masks — `cocycleMasks`, `quadraticMasks`,
`relationMasks`, supports appear only in `.lean` files), writing
`Certificates/{RetainedGroup, DyadicMaps, BlockMaps, CutForms, Magnus,
Exclusions, LocalWords}.lean`; generic parts by generalizing
`TruncatedMagnus*` (Fin 7 → Fin n, `e 0` → a conjugation vector parameter,
16 → 21 rows, bound → parameter), `RetainedQuadraticFox`,
`RetainedCyclicLocalModels`, `RetainedMagnusGenus`.

```lean
abbrev VB := Fin 8 → ZMod 2 ;  abbrev WB := Fin 15 → ZMod 2
def cocycleB : VB →ₗ[ZMod 2] VB →ₗ[ZMod 2] WB                 -- the 36 → 15 reduction of the free quadratic layer
abbrev QB := ClassTwo.GroupModel cocycleB ;  theorem card_QB : Nat.card QB = 2 ^ 23
theorem reduction_ker : (36 → 15 reduction).ker = span (21 relation initials)          -- decide +kernel
def dyadicMapB (P : Fin 2) : Dyadic.D →* QB                  -- bases x_P, y_P, z_P; D₂(D) ↦ independent in WB
theorem dyadicMapB_layer (P) (n) : Function.Injective (layerMap (ZMod 2) Dyadic.D (dyadicMapB P) n)
theorem dyadicCharacter_certificate (P = 0) : ∀ j k, … = Pi.single j 1 k   -- dual functionals (x: v₁+v₂, y: v₁, z: v₅)
theorem tame_layers (q : Fin 4), cap_layers (k : Fin 3), real_layers (i : Fin 2)       -- C₂×C₂, C₄ (square ≠ 1), C₂
theorem cutForms_zero : ∀ i : Fin 21, cutForm i = 0 in WB                         -- quadratic cut words die in QB
theorem magnus_retains_and_detects (hfree) (ρ) (hρ) (L : LiftsB G) (hL : spec) :
    let N := closedNormalClosure (wordsB L); let ψ := freeCut hfree (relatorTails hfree (quadraticWordsB L))
    N ≤ ρ.ker ∧ N ≤ ψ.ker ∧ 2 ^ 15 ≤ (Subgroup.centralizer {⟨ψ (L.c 0), _⟩}).index
```
Magnus data (survey check `magnus_check.py`): 7 generator conjugators suffice
for the second layer (rank 7 = ad(c₁) on L₁), commutators of generator pairs
for the third (rank 8), giving 2^{7+8}; U₂ = Fin 7, U₃ = Fin 8.
*Effort:* 1.5–2.5. *Risk:* medium (`decide +kernel` cost: V₃ has 512
coordinates, `third_row_certificate` 21·8·8 cases; generalizing the Magnus
stack away from `c = e₀`).

### T8 — Cut on the free source, local blocks, infinitude (GS)

*Inputs:* T3 (free source), T5 (local elements and labels), T6
(presentation, or `hgen` as parameter), T7. *Files:* `Cut/Words.lean`,
`Cut/Kernel.lean`, `Cut/LocalFamily.lean`, `Cut/LocalWords.lean`,
`Cut/CompletedPresentation.lean`, `Cut/BlockCosts.lean`, `Cut/Infinite.lean`,
and the generalized `GS/RetainedParameter.lean`.

Words (30, all literal, on `FiniteFreeProTwo.Carrier 8`; lifts are
`Function.surjInv freeMap_surjective` of the local elements, second-prime
lifts are lifts of the σ̂-conjugates): 21 quadratic — c₁², c₂²; tame words at
𝔮₁, 𝔮₂ (with the t² term, N = 3), 𝔯₁, 𝔯₂ (N = 5); **y₂²**; x_P², [x_P,y_P],
[x_P,z_P] (P = 1, 2); τ², φ² at the four tame places — 2 cubic
[[y_P,z_P],z_P] — 7 deep: z_P⁴, [y_P,z_P]², Frob(29_P)⁴, (F₇²)⁴. The 21
quadratic words have independent initials (the Magnus left inverse needs
this), so 𝔭₁ carries only its six cuts (its genuine relation is a
consequence) while 𝔭₂ carries y₂² literally; the genuine r₂ is in the kernel
by `Dyadic.ArithmeticPresentation.literal_presentation` pulled back along the
𝔭₂ local map. The set is σ̂-stable up to G_B-conjugacy and consequences
(y₁² ∈ kernel via r₁ and the 𝔭₁ cuts), which gives Ĝ-normality.

```lean
def words : Set (FiniteFreeProTwo.Carrier 8)
def kernel : Subgroup (FiniteFreeProTwo.Carrier 8) := closedNormalClosure words
abbrev ActualQuotient := FiniteFreeProTwo.Carrier 8 ⧸ kernel
def BArithmeticPresentation : Prop := closedNormalClosure (Set.range fun i => (relator i : _)) = relationKernel
theorem arithmetic_kernel_le (hgen : BArithmeticPresentation) : (relationKernel : Subgroup _) ≤ kernel
def kernelHat : Subgroup Ghat                                    -- image of kernel in GB ≤ Ghat
theorem kernelHat_le_GB ; theorem kernelHat_isClosed ; instance : kernelHat.Normal   -- σ̂-stability
theorem comap_kernelHat (hgen) : kernelHat.comap (GB.subtype.comp freeMap) = kernel
-- local family: IndexB := Fin 2 ⊕ Fin 4 ⊕ Unit ⊕ Fin 3 (real, tame, 𝔭₂-dyadic, caps) + distinguished 𝔭₁
def LocalGroupB : IndexB → Type   -- OddLocal.Cyclic 2 | OddLocal.D 0 | Dyadic.D | OddLocal.Cyclic 4
def otherMap (hgen) (j) : LocalGroupB j →* ActualQuotient ;  theorem otherMap_layers (j) (n) : Injective (layerMap _ _ (otherMap j) n)
theorem cut_local_word_cover (s) (hs : s ∈ words) : ∃ j w, localEval w = 1 ∧ sourceEval w = s
theorem finite_completedPresentation (hgen) [Finite ActualQuotient] : CompletedProTwoPresentation _ _ allRelations
theorem genuine_other_consequence (hgen) : CompletedProTwoConsequence otherRelations completedGlobalRelation₁
theorem sum_costB (t : ℝ) : 1 - 8*t + ∑ j, cost j t + dD t - sD t = (Sqrt241.towerPolynomial t : ℝ)   -- t = 34/117
theorem infinite_of_BArithmeticPresentation (hgen) : Infinite ActualQuotient
theorem infinite_hat (hgen) : Infinite (Ghat ⧸ kernelHat)
```
Generalized GS theorem (only mandatory change in the 73 GS modules):
`FilteredCompletedBlockPresentation.optimized_completed_presentation_positive`
with `(π : P →* RetainedQuadratic.Q) (hdiagram)` replaced by
`(R) (ρ : Dyadic.D →* R) (hρ1 hρ2 : layer injections) (χ : Fin 3 → R →* Multiplicative (ZMod 2)) (hχ) (π : P →* R) (hdiagram : π.comp f = ρ)`,
plus the helper `layer_injections_of_retained` (survey sketch
`gs-generic-sketch.lean`). The ℚ theorem is the instance
`R := RetainedQuadratic.Q`. `hInitial` fixes the 𝔭₁ generator order x, y, z ↔
5, −1, −2, so `SigmaDyadic.completedRelation` is reusable only if the 𝔭₁
lifts come from the ℚ₂-decomposition group in that order (T5 does this).
*Effort:* 3–4. *Risk:* medium (heavy bookkeeping, but every step has a ℚ
template; CompletedWords is the full profinite completion, universes `Type`).

### T9 — Retained map, M, detector, levels

*Inputs:* T6 (presentation), T7, T8. *Files:* `Levels/Retained.lean`,
`Levels/Detector.lean`, `Levels/Family.lean`; generalize
`GaloisRetainedFamily` (RetainedField → any number field M with a √−1, 4096 →
parameter) and `GaloisFixedArithmetic` (shared with stream A).

```lean
def retainedFree : FiniteFreeProTwo.Carrier 8 →ₜ* QB        -- generator i ↦ (e_i, 0)
theorem retainedFree_kills (hgen) : relationKernel ≤ ker ∧ kernel ≤ ker   -- forms and literal_presentation
def retainedMap (hgen) : GB →ₜ* QB ;  theorem retainedMap_surjective ;  theorem retainedMap_base (g) : (retainedMap g).base = (genusLabel g).toAdd
def core (hgen) : Subgroup Ghat := K ⊓ K.map (MulAut.conj sigmaHat).toMonoidHom   -- K := (ker retainedMap).map GB.subtype
theorem core_open_normal ;  theorem kernelHat_le_core
def M (hgen) : IntermediateField ℚ Omega := IntermediateField.fixedField (core hgen)
instance : NumberField M ; instance : IsGalois ℚ M        -- InfiniteGalois.isOpen_and_normal_iff_finite_and_isGalois
def genusToM : CanonicalGenus.Carrier →ₐ[ℚ] M ;  theorem sqrt3_in_M : ∃ r : M, r ^ 2 = 3 ;  theorem i_in_M : ∃ r : M, r ^ 2 = -1
def detector (hgen) : Ghat →ₜ* DetectorGroup                 -- Ghat ⧸ (Magnus kernel ⊓ its σ̂-conjugate), finite
theorem detector_surjective ; theorem kernelHat_le_detector_ker
theorem detector_index : 65536 ≤ (Subgroup.centralizer {detector conj₁}).index
    -- card_le_centralizer_index_of_conjugates_injective with P = (U₂ × U₃) × Bool, g ↦ (b ? σ̂ : 1)·g_p;
    -- different b give different labels (10111010 ≠ 11000101)
def level (hgen) (j : ℕ) : IntermediateField ℚ Omega         -- retainedFamily ρ := Ghat → Ghat ⧸ kernelHat, e := M.val, χ := detector
-- all of GaloisRetainedFamily's outputs: Galois over ℚ, M ≤ level, degree → ∞, conjugation, IsConj, index ≥ 65536
```
Optional "exact" variant: prove ker retainedMap σ̂-stable (it is the preimage
of D₃ of the cut quotient; needs |Γ/D₃| ≤ 2²³ from Jennings spanning) to get
Gal(M/B) ≃* Q_B and [M:ℚ] = 2²⁴. Not needed downstream.
*Effort:* 1.5–2. *Risk:* low–medium.

### T10 — Local indices, unramifiedness, prime freedom, census

*Inputs:* T5, T8, T9. *Files:* `Levels/LocalData.lean`,
`Levels/Unramified.lean`, `Levels/PrimeFreedom.lean`, `Levels/Census.lean`.
Rational e, f are computed exactly as in the ℚ package from absolute image
cardinalities (`AbsolutePrimeIndices.ramification_residue_of_absolute_image_cards`,
`AbsolutePrimeImages.decompositionRestriction_card`, reused unchanged).

```lean
def selectedPrime (a : Fin 5) : Nat.Primes           -- ![2,3,5,29,7], Witness.{ramification,residueDegree}
theorem selected_local_image_cards (K : IntermediateField ℚ Omega) [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (hMK : M hgen ≤ K) (hK : kernelHat ≤ K.fixingSubgroup) (a : Fin 5) :
    Nat.card (inertiaRestriction (selectedPrime a) K j).range = Witness.ramification a ∧
    Nat.card (decompositionRestriction (selectedPrime a) K j).range = Witness.ramification a * Witness.residueDegree a
    -- applies to every level (K = level j) and to M itself (K = M: kernelHat ≤ core)
    -- upper: cut (τ² = φ² = 1; D-factorization; Frob(29)⁴ = 1; F₇⁸ = 1); lower: QB (and E at 3, 5)
    -- 7: range = zpowers F₇, F₇ ∉ GB, (F₇²)² ≠ 1 in QB ⇒ order 8; 29: zpowers Frob, Frob² ≠ 1 in QB
    -- 2: image of D, inertia 8 via L₂ (T5) or via kernel equality with the ℚ retained field
theorem level_ramification_residue (hgen) (j) (a : Fin 5) :
    (rationalPrimeIdeal (Witness.primes a)).ramificationIdxIn (𝓞 (level hgen j)) = Witness.ramification a ∧
    (rationalPrimeIdeal (Witness.primes a)).inertiaDegIn (𝓞 (level hgen j)) = Witness.residueDegree a
theorem M_ramification_residue (hgen) (a : Fin 5) : … (𝓞 (M hgen)) …     -- exact types of M at 2, 29, 7 (and 3, 5)
theorem finiteUnramified_of_base_and_ramificationIdxIn_eq (…) : FiniteUnramified M K    -- K/B unramified outside S, equal e at 2,3,5
theorem level_finiteUnramified (hgen) (j) : FiniteUnramified (M hgen) (level hgen j)
theorem PrimeCompletion.decomposition_fixes_sqrt (p : Nat.Primes) (d : ℚ) (hd : IsSquare (algebraMap ℚ (Base p) d))
    (x : Closure) (hx : x ^ 2 = algebraMap ℚ _ d) (σ : AbsoluteDecomposition p) : σ.val x = x
theorem level_prime_moved (hgen) (j) (a : Fin 5) (P : PrimeNormFiber (level hgen j) (primeNorm a)) :
    Ideal.map (RingOfIntegers.mapRingHom (levelConjugation hgen j).toRingHom) P.1.asIdeal ≠ P.1.asIdeal
    -- c moves √d, D_w fixes √d; d = −15, −2, −1, −3, −1 at 2, 3, 5, 7, 29; √d ∈ ℚ(√−1,√2,√3,√5) ⊆ E ⊆ M
theorem M_census (hgen) (p ∈ {41,47,53,59,61,67,79,83,97}) : 4 ≤ (rationalPrimeIdeal p).inertiaDegIn (𝓞 (M hgen))
    -- Frobenius label (Legendre symbols of α_i at the prime of B under the chosen place; both primes certified),
    -- S(v) ∉ R₂ ⇒ order ≥ 4 in QB
```
The prime-freedom argument (from the survey) replaces the ℚ genus-label
exclusion (`GenusLocalExclusions`, `SigmaCutAbsoluteGenus`), which would need
non-abelian labels over B (Gal(E/ℚ) is not abelian; c₁, c₂ are Ĝ-conjugate).
*Effort:* 2–3. *Risk:* medium (dyadic inertia 8; `AbsoluteDecomposition p`
is dependent on `p : Nat.Primes`, so fix one term per prime; census needs 18
Frobenius labels).

### T11 — Root discriminant of M

*Inputs:* T9, T10, the verified ℚ package (black box). *Files:*
`Discriminant/Generic.lean`, `Discriminant/M.lean`.

Route T (recommended; found independently by the lead and the survey):
v_p(|disc M|)/[M:ℚ] is computed prime by prime through fields with the same
ramification at p. At 2 the comparison field is the ℚ retained field R_ℚ of
the verified package: it lives in the same closure, its dyadic local image at
the ℚ package's chosen place is D through the same ℚ₂ local generators (x, y,
z ↔ 5, −1, −2), so M and R_ℚ have the same inertia kernel at 2 and the
compositum MR_ℚ is unramified over both above 2. No radicand, no disc(E), no
13, no explicit √β.

```lean
theorem discr_factorization_eq_of_unramifiedAbove (F K) [..] [Algebra F K] {p : ℕ} (hp : p.Prime)
    (h : ∀ P : Ideal (𝓞 K), P.IsPrime → (p : 𝓞 K) ∈ P → Algebra.IsUnramifiedAt (𝓞 F) P) :
    (discr K).natAbs.factorization p = Module.finrank F K * (discr F).natAbs.factorization p          -- D1
theorem unramifiedAbove_of_ramificationIdxIn_eq (F K) [IsGalois ℚ F] [IsGalois ℚ K] [Algebra F K] {p} (hp)
    (he : (rationalPrimeIdeal p).ramificationIdxIn (𝓞 K) = (rationalPrimeIdeal p).ramificationIdxIn (𝓞 F)) : …  -- D2
theorem discr_factorization_mul_finrank_eq_of_inertia_ker_eq (p : Nat.Primes) (M₁ M₂) [..]
    (j₁ : M₁ →ₐ[ℚ] Closure) (j₂ : M₂ →ₐ[ℚ] Closure)
    (h : (inertiaRestriction p M₁ j₁).ker = (inertiaRestriction p M₂ j₂).ker) :
    (discr M₁).natAbs.factorization p * finrank ℚ M₂ = (discr M₂).natAbs.factorization p * finrank ℚ M₁   -- D3
theorem log_rootDiscriminant_eq_sum (K) (T : Finset ℕ) (hT : ∀ p, p.Prime → p ∣ (discr K).natAbs → p ∈ T) :
    Real.log (rootDiscriminant K) = ∑ p ∈ T, ((discr K).natAbs.factorization p : ℝ) / finrank ℚ K * Real.log p  -- D4
theorem log_rootDiscriminant_M_le (hgen) :
    Real.log (rootDiscriminant (M hgen)) ≤ (9/4) * Real.log 2 + (1/2) * Real.log 3615
```
Inputs used: support {2, 3, 5, 241}; at 241 compare with B (disc 241,
`Base.discr_eq`); at 3, 5 with ℚ(√−3), ℚ(√5) (`GenusDiscriminant.qNegThree_discr`,
`qFive_discr`) using e = 2; at 2 with R_ℚ: v₂(disc R_ℚ) ≤ 131072 + 256·4096 =
1179648 = (9/4)·2¹⁹ from `retainedField_natAbs_discr_eq_relativeDifferent`,
`retainedField_absNorm_differentIdeal_eq_two_pow_factorization`,
`retainedRelativeDifferentTwoExponent_le`, `chosenGenus_natAbs_discr`,
`retainedField_degree`, and the inertia-kernel equality from T5/T10 (the ℚ
side: `SigmaDyadic.exists_injective_dyadic_map`, `retained_dyadic_inertia_card`).
Mathlib: `natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow`,
`differentIdeal_eq_differentIdeal_mul_differentIdeal`, `not_dvd_differentIdeal_iff`,
`not_dvd_discr_iff_forall_liesOver`, `Ideal.ramificationIdx_tower`.
Import cost: the ℚ retained/discriminant cone (already compiled); import
`RetainedDyadicDifferentComplement` but not the historical `FullResultReduced`
chain in new files.
Fallback route β (stream E, `E_RD_DATA.md`, `scripts/sqrt241/dyadic_radicals.gp`):
R := E(√β₁, √β₂) with explicit D₄-radicals; needs √β₁ ∈ M (Kummer ↔ R₂^⊥ or
cut-word checks at every place), disc(E) through E₃₂ = ℚ(ζ₈, √−3, √5, √241),
and an integral generator at 𝔭₁ (template `RetainedDyadicDifferentGenerator`).
*Effort:* 1.5–2.5 (route T). *Risk:* medium (the kernel equality needs the B
dyadic block to be literally the ℚ₂ one, which this plan guarantees).

### T12 — Assembly and export

*Inputs:* all. *File:* `TowerExport.lean`. Deliver exactly the hypotheses of
stream A's `Sqrt241.target_of_growing_galois_fields` (or of its
infinite-quotient variant: Ω, ρ, e : M →ₐ[ℚ] Ω, χ, `hindex : 65536 ≤ …`,
`hunrM`, `he`, `hf` over `Fin 5`, `hfree`, `hdiscM`, √3 and √−1 in M) and of
stream B's `Analytic.fixedBaseCeiling_lt_of_local_types` (`[Algebra E M]`
via `genusToM`, exact types of M at 2, 29, 7, census f ≥ 4). Then
`#print axioms` from a scratch file; build only own modules.
*Effort:* 0.5–1. *Risk:* low (interface drift between streams: agree on the
statement files early).

### 3.2 Dependencies and parallel schedule

```
Base (other stream) ──► T2 ──┬──► T3 ──► T6 ──┐
T0 ──► T1 ──────────────────┤              │
T0 ──► T4 (H² ≤ 7) ─────────────────────────┤ (hbound; T6 is written with hbound as a parameter)
T1 ──► T5 (local maps, labels, ℚ₂ cut) ─────┼──► T8 ──► T9 ──► T10 ──► T11 ──► T12
T7 (certificates, from data only) ──────────┘
```
Interface-first rule (as the ℚ package did with `ArithmeticPresentation`):
state `BArithmeticPresentation` and the label facts as Props early, and let
T8–T11 take them as parameters; discharge at T12. Definitions that others
need early: `Omega`, `Ghat`, `GB`, `sigmaHat` (T1, day 1–2), `freeMap` (T3),
the local elements (T5a), `QB` (T7).

Suggested allocation (5 agents): (1) T0 → T4; (2) T1 → T3 → T6; (3) T5;
(4) T7 → T8; (5) T2 (with the Base/Genus streams) → T9 → T10 → T11 → T12.

### 3.3 Effort and critical path

| WP | agent-days | risk |
|---|---|---|
| T0 retype | 1–1.5 | low |
| T1 bridge, Galois over ℚ | 1.5–2.5 | medium |
| T2 base, E | 1–1.5 | low–medium |
| T3 H¹, free source | 1.5–2 | medium |
| T4 H² ≤ 7 | 3–4.5 | high |
| T5 local maps, labels | 3–4 | medium |
| T6 presentation | 1.5–2 | medium |
| T7 certificates | 1.5–2.5 | medium |
| T8 cut, GS | 3–4 | medium |
| T9 M, detector, levels | 1.5–2 | low–medium |
| T10 local indices | 2–3 | medium |
| T11 root discriminant | 1.5–2.5 | medium |
| T12 assembly | 0.5–1 | low |
| **total** | **22–33** | |

Critical path (definitions and final discharges): T0 → T1 → T5a → T8 → T9 →
T10 → T11 → T12 ≈ 12–18 agent-days, with T4 → T6 (≈ 4.5–6.5) joining before
T8's discharge. With five agents and interface-first development (T8–T11
written against `BArithmeticPresentation`, `hbound` and the label facts as
parameters): ≈ 8–12 days elapsed, plus machine time (the ℚ build is ≈ 3.6 h;
new modules import large cones). This is above the ≈ 7–10 agent-days that
SQRT241_PORT.md §3 allots to the tower items (M3, M4, N1–N7): that estimate
did not include T1 (Galois over ℚ), the generalized GS theorem, the Ĝ-level
detector, the ℚ₂ local cut, the B character with prescribed inertia or the
normalization of places, which the survey found necessary.

### 3.4 Risks (the six named in the brief first)

1. **Relation bound with two real places (T4).** The deep inputs are generic
   upstream; the new parts are (a)–(d) above (finite bookkeeping, ≈ 400–600
   lines) and the character existence (route R, ≈ 600–800 lines). Checked
   against the code: `fieldUnitsH2_eq_zero_of_idele_injective` assumes all
   infinite places unramified (`hinf`), so detection over B itself fails;
   the ℚ(i)-type tower over B(i) (totally complex) is required. Upstream has
   no invariant/sum map at ramified archimedean blocks, so the Artin-symbol
   route (a)–(b) is the one the existing code supports. Mitigation: T6–T11 take
   `hbound` as a parameter.
2. **Galois-over-ℚ property of the levels (T1, T8, T9).** Reduced to one
   semilinear transport lemma for `IsUnramifiedAtFinitePlacesOutside`
   (twist of the base algebra + `congrTop`), plus σ̂-stability of the word set
   and the σ̂-core for M and the detector. Levels are then fixed fields of
   Ĝ-normal open subgroups (`GaloisQuotientTower`, generic).
3. **The dyadic relation as an actual relator (T6, T8).** The presentation
   uses the genuine r₂ with initial S(y₂)+B(x₂,y₂)+B(x₂,z₂)
   (`genuineRelation_image`, new); the cut uses literal y₂² (independent
   Magnus rows); r₁ is a consequence (`relator_generates`). In GS, 𝔭₁ is the
   distinguished block (`hConsequence`), 𝔭₂ an ordinary D-block whose
   `hlayers` come from Q_B.
4. **Local indices at the inert prime 7, type (1,8) (T5, T10).** F₇ ∉ G_B, so
   the retained model sees only F₇²; the decomposition image is ⟨F₇⟩ of order
   8 = 2·4; `frobenius_unit_radical` must accept a valuation-ring radicand
   (no integer represents the non-square unit class of ℚ₄₉); F₇² acts on √α
   by (Nα/7) = 01110000. The cap word is (F₇²)⁴ ∈ G_B.
5. **Root discriminant (T11).** The ℚ proof's √(−2+3i) needs 13 ∈ S and does
   not transfer; route T avoids any dyadic generator by comparing with the ℚ
   retained field at 2 (same closure, same chosen place, same ℚ₂ local cut).
   Residual risk: the inertia-kernel equality and the prime-by-prime D1–D4
   lemmas (≈ 300–500 lines, no Mathlib tame-different upper bound needed).
6. **h(B) = 1 and units (T2).** Being done by the Base stream with Mathlib's
   Minkowski criterion (`RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc`),
   `Base/Units.unit_eq_mul_sq`; torsion ±1 needs a copy of Mathlib's
   odd-degree lemma. Not yet verified.
7. **Choices and normalization (T5).** The chosen places are
   `IsAlgClosed.lift`-dependent; local tables must be indexed by the image of
   √241 (both roots certified) and the maps normalized by `frame`.
8. **Magnus stack assumes c = e₀ (T7).** B's c₁ = 10111010; parameterize the
   conjugation vector (or use an adapted generator basis).
9. **Elaboration with F = ↥B (T0–T4).** Instance diamonds (`Algebra ℚ` on
   `AlgebraicClosure B`, `algebra'` vs `extendScalars`), heartbeats already
   raised in the ℚ files; `Algebra.IsAlgebraic ℚ (AlgebraicClosure B)` not
   inferred.
10. **Kernel `decide` cost (T6, T7)** ≈ 2× the ℚ certificates, which already
   needed `maxHeartbeats 16000000`.

## 4. Coverage of the new mathematical inputs by upstream and Mathlib

Paths: `Up/` = `UnitDistance/Upstream/Yamaguchi/`, `STRT` = `SawinTotallyRealTowers`,
`UPRR` = `STRT/UnramifiedProPRelationRank`. "Generic" means stated for an
arbitrary number field (any number of infinite places). Every entry was
located in the source by the lead or a survey agent; † marks the ones the
lead read in full.

| input (WP) | covered by (declaration — file) | missing / to write |
|---|---|---|
| cyclic Hasse norm principle (T4) | † `hasseNormPrinciple_cyclic` — `Up/ClassFieldTheory/GlobalClassFieldTheory/ClassFieldAxiom/HasseNormPrinciple.lean` (generic; everywhere-local norms include infinite places) | — |
| global reciprocity / Artin product formula (T4) | † `chosenLocalArtin_product_principalIdele` — `…/Reciprocity/GlobalArtinCompatibility.lean` (product over all `InfinitePlace K` times finprod over finite places); `chosenInfinitePlaceArtinMonoidHom_ker` (`InfinitePlaceArtin.lean`); `chosenFinitePlaceArtinMonoidHom_ker` (`FinitePlaceArtin/Core.lean`) | all-but-one-infinite-place form (≈ 40 lines, from `OneInfinitePlaceNorm`) |
| H¹(G, C_L) = 0, field-unit H² ↪ idele H² (T4) | `finiteFieldUnitsIdeleH2Map_injective_of_isPGroup` — `UPRR/Global/FiniteFieldUnitsIdelePrimitive.lean` (any p-group, no condition at infinity); † `fieldUnitsH2_eq_zero_of_idele_injective` (repo, needs unramified infinite places); † `TotallyComplexFieldUnitsH2.fieldUnitsH2_eq_zero_of_finite_localizations` | bounded cyclic detection for B(i)/B; image version of † `fieldUnitsH2_finite_detection_tower`; B(i) model (`KummerInvariantRadicand.Extension (-1 : B)`) |
| inflation/restriction for field-unit H² (T4) | `finiteGaloisTowerUnitsH2Inflation_injective`, `…Restriction_ker_le_inflation_range` — `Up/GaloisCohomology/Kummer/FiniteGaloisTowerUnitsH2.lean`; `finiteFieldUnitsTensor_inflation_eq_zero_iff` (repo `FiniteTensorGaloisInflationH2`); `exists_fieldScalarUnitH2`, `fieldScalarUnitH2_eq_zero_iff_norm`, `fieldScalarUnitH2_tensor_eq_zero_iff_norm` (repo `FieldTensorCyclicH2`) | multiplicativity of the scalar representative |
| Kummer image of a stage (T4) | `finiteKummerSPlaceH2Localization_range_finite_natCard_le` — `UPRR/Kummer/FiniteKummerSPlaceCardinality.lean` (≤ n^#S); `finiteKummerContinuousH2Map_ker_le_absoluteInflation_ker` — `Up/STRT/FiniteKummerContinuousKernel.lean`; `supportedIdeleH2_finite_eq_zero_of_unramified` (repo) | counting with a kernel of size 2 (`natCard_range_le_of_map_ker`) |
| stage kernel, cocycle lifts (T4) | `exists_inertia_trivial_local_cocycle_lift` (repo `CentralLiftCorrection`, generic F); `finitePlaceUnramifiedQuotientH2_subsingleton` — `UPRR/RelationRank/FinitePlaceUnramifiedH2LocalizationVanishing.lean`; `absoluteDiscreteHom_inertia_support_finite` — `UPRR/RelationRank/AbsoluteDiscreteRamificationSupport.lean`; H2CocycleExtension* — `Up/GaloisCohomology/ProP/` | retype to F |
| quadratic character with prescribed inertia (T4) | `exists_absoluteCharacter_of_finiteSupport_radical_annihilator` — `UPRR/Radical/FiniteSupportInertiaCorrection.lean` (any F, any prime n; needs the reciprocity functional to vanish on the radical); `quadraticAbsoluteCharacter*`, `localRadicalValue*` (private, generic) — `Up/STRT/NegativeThreeCharacter.lean`; radical: `mem_idealNthPowerRadicalKummerSubgroup_iff_valuation` (`UPRR/Radical/IdealPowerRadicalSelmer.lean`), `range_ordinaryUnitToIdealRadical_eq_ker_toClassTorsion` (`…/IdealPowerRadicalExact.lean`) | ℚ-only today (`exists_absoluteCharacter_with_prescribed_inertia_and_real_value` uses 3 ∈ T and ℚ(√−3)); B: radical ⟨−1, ε⟩ and the dyadic correction (route R) |
| continuous H² from finite stages (T4) | `finiteDimensional_and_finrank_degree_two_le_of_inflationRange_natCard` — `Up/GaloisCohomology/ProP/H2InflationRangeCardinality.lean` (generic `d`); `continuousCohomologyZModPLiftedLinearEquiv` — `…/PresentationQuotientEquiv.lean` | — |
| Kummer theory of quadratic extensions (T2, T3) | `KummerInvariantRadicand` (repo, generic: `Extension`, `isGalois_of_invariant`, `nonsquare_of_twisted_norm`); `GeneratedQuadraticSigns.rootSignHom_{surjective,injective}`; `QuadraticRamification.isUnramifiedAt_of_integral_product` (relative); `kummerGeneratedExtension_chosenFinitePlaceIsUnramified_of_valuation_eq_one` — `Up/ClassFieldTheory/KummerTheory/Concrete/SimpleExtensionLocalBehavior.lean`; Mathlib `Algebra.IsQuadraticExtension.exists_algEquiv_quadraticAlgebra`, `HeightOneSpectrum.valuation_liesOver`, `Algebra.isUnramifiedAt_iff_map_eq` | odd valuation ⇒ ramified (K2); L = B(√a) (K3); S-Selmer group = V (I5) |
| h(B) = 1, units (T2) | Mathlib `RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc` (`NumberTheory/NumberField/ClassNumber.lean`), `NumberField.Units.{rank, fundSystem, exist_unique_eq_mul_prod, torsion}`; upstream `numberField_discr_of_mod_four_eq_one` (`Up/STRT/QuadraticFieldDiscriminant.lean`); Base stream: `Base.isPrincipalIdealRing`, `classNumber_eq_one`, `Units.unit_eq_mul_sq` (WIP) | torsion ±1 in even degree (copy of `torsion_eq_one_or_neg_one_of_odd_finrank`) |
| local fields at split p (T5) | `PrimeCompletion.{place, Base, equiv, decompositionEquiv, decomposition_commutes, decomposition_mem_inertia_iff}` (repo `RationalPrimeCompletion`, `RationalLocalAbsoluteEmbedding`); upstream `finitePlaceAbsoluteDecompositionGroup`, `…InertiaSubgroup` (`UPRR/Local/FinitePlaceH2Localization.lean`, `FinitePlaceUnramifiedH1.lean`); `OddTame*`, `LocalArtin*`, `PadicFiniteGalois*` (repo, generic) | B radicand tables (Hensel), valuation-ring radicand at 7 |
| ℚ₂ local group and the genuine relation (T5, T6) | `PadicTwoMaximalProTwo` (rank 3), † `PadicTwoQuadraticRelation.exists_actual_quadratic_relation`, `DyadicArithmeticPresentation.{literal_presentation, arithmetic_presentation, factors_through_model}`, `DyadicClosedPresentation.literalRelations` = [x², y², [x,y], [x,z], [[y,z],z], z⁴, [y,z]²] (repo, local) | `genuineRelation_image` (global initial); ℚ₂ local cut field L₂ with e = 8, f = 4 (generalize `ArithmeticDyadic*`) |
| Hensel / square classes (T5) | Mathlib `hensels_lemma`, `PadicInt.ker_toZModPow`; repo `PadicTwoSquareclasses.exists_sq_eq_of_residue_one` | the B tables |
| different, discriminant (T11) | Mathlib `differentIdeal_eq_differentIdeal_mul_differentIdeal`, `not_dvd_differentIdeal_iff`, `dvd_differentIdeal_iff`, `pow_sub_one_dvd_differentIdeal` (`RingTheory/DedekindDomain/Different.lean`), † `natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow`, † `not_dvd_discr_iff_forall_liesOver`, `absNorm_differentIdeal` (`NumberTheory/NumberField/Discriminant/Different.lean`); repo `rootDiscriminant_eq_of_finiteUnramified`, `GenusDiscriminant.{qNegThree_discr, qFive_discr}`, ℚ retained discriminant results | D1–D4 (prime-by-prime discriminant), inertia-kernel comparison; no tame upper bound needed |
| infinite Galois theory, closures (T1, T9) | Mathlib `InfiniteGalois.{normalAutEquivQuotient, fixingSubgroup_fixedField, isOpen_and_normal_iff_finite_and_isGalois, restrictNormalHom_continuous}`, `IntermediateField.fixingSubgroupEquiv` (MulEquiv only), `IsAlgClosure.equiv`, `ContinuousMulEquiv.ofBijectiveCompactToT2`; upstream `semilinear_conjugation_continuous`, `algEquiv_autCongr_continuous`, `semilinearRingEquivPreimageIntermediateField` (`Up/ValuedFieldTheory/Ramification/GaloisValuation/AbsoluteGalois/InfiniteGaloisCorrespondence.lean`); `IsUnramifiedAtFinitePlacesOutside.{sup, bot, top, congrTop}` (`Up/STRT/RamificationSupport*.lean`, generic in the base) | semilinear transport of ramification support; homeomorphism Gal(Ω_B/B) ≃ₜ* G_B |
| pro-2 presentations (T3, T6) | `relativeNakayama_character` (`Up/ProCGroups/Cohomology/RelativeNakayama.lean`), `invariant_character_family_card_le_finrank_h2` (`Up/GaloisCohomology/ProP/ClosedKernelH2FiniteFamily.lean`), `closedNormalClosure` (`Up/ProCGroups/Presentations/Profinite.lean`), `IsFreeProCGroup` (`Up/ProCGroups/FreeProC/Basic.lean`), Burnside basis (`Up/ProCGroups/ProP/BurnsideBasis.lean`); repo `SpecifiedRelators.closedNormalClosure_eq_of_dual_characters` (generic n), `FiniteFreeProTwo` (generic d) | `closedNormalClosure_eq_of_initials` (generic form of `OriginalRelatorGeneration`) |
| complex conjugation (T5) | Mathlib `NumberField.ComplexEmbedding.exists_comp_symm_eq_of_comp_eq`, `IsConj` (`NumberTheory/NumberField/InfinitePlace/Embeddings.lean`); repo `GaloisEmbedding.restriction_isConj` | sign vectors of the radicands at v₁, v₂ |

Nothing in the list needs a new *deep* theorem: every class-field-theoretic
input used over ℚ is generic upstream. What is missing is B arithmetic
(tables, radical ⟨−1, ε⟩, S-Selmer), the two-real-place bookkeeping, and the
three structural lemmas (semilinear transport, genuine-relation initial, ℚ₂
local cut).

## 5. Coordination, open decisions, resume notes

* **Other streams already active** (untracked, work in progress, not
  verified by this plan): Base (`Sqrt241/Base/{Field, Integers, Primes,
  ClassNumber, Units}.lean`), stream B (`Analytic/*`, `Genus/*` — E Galois of
  degree 512 and E's local types: T2 must reuse, not duplicate), stream A2
  (`Geometry/*`, `docs/sqrt241/A2_GEOMETRY.md`), stream E (root-discriminant
  data, `docs/sqrt241/E_RD_DATA.md`, `scripts/sqrt241/dyadic_radicals.gp`).
* **Interfaces to freeze first** (T12 depends on them): stream A's
  `Sqrt241.target_of_growing_galois_fields` hypothesis list; stream B's
  `Analytic.fixedBaseCeiling_lt_of_local_types` (needs `[Algebra E M]`,
  exact types of M at 2, 29, 7, census f ≥ 4 at 41, 47, 53, 59, 61, 67, 79,
  83, 97); the tower's `Omega`, `Ghat`, `GB`, `sigmaHat`, `M`, `level`.
* **Open decisions** (defaults in brackets): the character route in T4 [R];
  the root-discriminant route [T]; M minimal vs exact [minimal]; cVec
  parameter vs adapted basis in the Magnus stack [parameter]; whether to make
  the retyped ℚ modules generic in place (F implicit from T) or to copy them
  [copy: the ℚ cone stays byte-identical, per CONVENTIONS].
* **Do not import** `FullResultReduced` or the historical `SIntegerWitness*`
  chain in new files; `NumberFieldNumericInvariance` and
  `QuadraticSevenDescent` are needed and must be imported directly.
* **Scratch evidence** (not part of the repository): Lean typing experiment,
  PARI census/L₂ scripts, and the survey scripts (`b_dual.py`, `cupcheck.py`,
  `dyadic241*.py`, `local/sqclass.py`, `magnus_check.py`, `gs-generic-sketch.lean`)
  are in the session scratch directory
  `/tmp/claude-1000/-home-naslund-eric-src-enaslund-unit-distance-bound-master/69c8b3d8-1ca3-4359-a38d-a1666ce4aef4/scratchpad/plan/`;
  the data they check is restated in §1.5 and §3 so the plan does not depend
  on them.
