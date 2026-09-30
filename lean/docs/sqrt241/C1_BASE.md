# Stream C1: arithmetic of the base field B = ℚ(√241)

Modules: `UnitDistance/Sqrt241/Base/*.lean`, umbrella
`UnitDistance.Sqrt241.Base.All`. Namespace `UnitDistance.Sqrt241.Base`
(below, names are relative to it). Everything is proved; axioms of the main
results are `propext, Classical.choice, Quot.sound` (checked with
`#print axioms` from a scratch file outside the repository).

Rebuild (≈ 1 min after the upstream cone is built):

    ./.toolchain/bin/lake build UnitDistance.Sqrt241.Base.All

Import order: `Field → Integers → Primes → ClassNumber → Units`,
`Integers → Signs`, `Units + Signs → SUnits → {Selmer, Residues, Local}`,
`Local + Selmer → {LocalRoots, LocalValuation → Completion}`.

For the tower plan (TOWER_PLAN.md, T2/T5) the interface names are in
`Selmer.lean` (`S`, `SFin`, `alphaB`, `alpha_independent`,
`mem_V_of_even_outside_S`, `CanonicalGenus.base_le_field`) and
`LocalRoots.lean` (square classes for either `p`-adic root of `241`,
`not_isSquare_241_Q7`).

## Conventions

* `B : IntermediateField ℚ Closure := ℚ⟮baseRoot⟯` (`abbrev`), with
  `baseRoot = CanonicalGenus.baseRoot`, `Closure = AlgebraicClosure ℚ`.
  Instances: `NumberField B`, `FiniteDimensional ℚ B`,
  `Algebra.IsQuadraticExtension ℚ B`, `IsGalois ℚ B`, `IsTotallyReal B`,
  `IsPrincipalIdealRing (𝓞 B)`.
* `sqrt241 : B` (the generator, `coe_sqrt241 : (sqrt241 : Closure) = baseRoot`).
* Elements of `𝓞 B`: `mk m n = m + n ω`, `omega = ω = (1 + √241)/2`,
  `ω² = ω + 60`. Coercion `𝓞 B → B` is Mathlib's; `coe_mul`, `coe_pow`,
  `coe_ne_zero` help where `rw [map_mul]` does not see through it.
* Radicands, in the order of `CanonicalGenus.radicand` and of `kummer241.gp`:
  `alpha : Fin 8 → 𝓞 B := ![-1, eps, pi2, pi2', pi3, pi3', pi5, pi5']`.
* Primes follow PARI's `idealprimedec` order: `P2 = (π₂)` is PARI's
  `P2[1]` etc. (checked against the Hilbert-symbol lines of `kummer241.gp`).

## 1. The field (`Field.lean`)

* `finrank_eq_two : Module.finrank ℚ B = 2`; `minpoly_baseRoot`,
  `minpoly_sqrt241 : minpoly ℚ sqrt241 = X ^ 2 - C 241`; `not_isSquare_241`.
* `sqrt241_sq : sqrt241 ^ 2 = 241`, `adjoin_sqrt241_eq_top`,
  `baseRoot_mem_B`, `B_le_field : B ≤ CanonicalGenus.field`.
* Coordinates: `exists_coords (x : B) : ∃ a b : ℚ, x = algebraMap ℚ B a + algebraMap ℚ B b * sqrt241`,
  `coords_injective`, `trace_coords : trace (a + b√241) = 2a`,
  `norm_coords : Algebra.norm ℚ (a + b√241) = a ^ 2 - 241 * b ^ 2`.
* Galois: `sigma : B ≃ₐ[ℚ] B`, `sigma_sqrt241 : sigma sqrt241 = -sqrt241`,
  `sigma_coords`, `sigma_sigma`, `sigma_mul_self : sigma * sigma = 1`, `sigma_ne_one`,
  `algEquiv_eq_one_or_sigma (τ) : τ = 1 ∨ τ = sigma`,
  `mul_sigma_eq_norm : x * sigma x = algebraMap ℚ B (Algebra.norm ℚ x)`,
  `add_sigma_eq_trace`, `algHom_ext` (algebra maps out of `B` agreeing on `√241`).
* Real places: `embPlus, embMinus : B →ₐ[ℚ] ℝ` (`√241 ↦ ±Real.sqrt 241`,
  PARI's first/second real place), `embPlus_coords`, `embMinus_coords`,
  `embMinus_eq_comp_sigma`, `embMinus_apply`, `algHom_real_eq`, `ringHom_real_eq`
  (every map to `ℝ` is one of the two), `complexEmbPlus/Minus`,
  `placePlus, placeMinus : InfinitePlace B`, `placePlus_ne_placeMinus`,
  `infinitePlace_eq (w) : w = placePlus ∨ w = placeMinus`,
  `nrRealPlaces_eq_two`, `nrComplexPlaces_eq_zero`, `card_infinitePlace`.

## 2. The ring of integers and the radicands (`Integers.lean`)

* `integralBasis : Basis (Fin 2) ℤ (𝓞 B)` with `integralBasis 0 = 1`,
  `integralBasis 1 = omega`; `discr_eq : NumberField.discr B = 241`.
* `mk`, `coe_mk : (mk m n : B) = (m + n/2) + (n/2)√241`, `exists_mk`,
  `mk_inj`, `mk_add`, `mk_neg`, `mk_sub`,
  `mk_mul : mk a b * mk c d = mk (ac + 60bd) (ad + bc + bd)`,
  `norm_mk : Algebra.norm ℤ (mk m n) = m² + mn - 60 n²`.
* `sigmaInt : 𝓞 B ≃+* 𝓞 B`, `coe_sigmaInt`, `sigmaInt_mk : σ(mk m n) = mk (m+n) (-n)`,
  `mul_sigmaInt : x * sigmaInt x = Algebra.norm ℤ x`.
* Named elements (all `𝓞 B`): `eps = -71011068 + 4574225√241`,
  `epsInv = 71011068 + 4574225√241`, `pi2 = (-6101 - 393√241)/2`,
  `pi2' = (6101 - 393√241)/2`, `pi3 = 31 - 2√241`, `pi3' = 31 + 2√241`,
  `pi5 = 326 - 21√241`, `pi5' = 326 + 21√241`, `pi29 = -14127 + 910√241`,
  `pi29' = -14127 - 910√241`, `sqrt241Int`; coordinate lemmas `coe_eps`, `coe_pi2`, ….
* Norms `norm_eps = -1`, `norm_pi2 = norm_pi2' = -2`, `norm_pi3(') = -3`,
  `norm_pi5(') = -5`, `norm_pi29(') = 29`, `norm_sqrt241Int = -241`.
* Products: `eps_mul_epsInv = 1`, `pi2_mul_pi2' = 2`, `pi3_mul_pi3' = -3`,
  `pi5_mul_pi5' = -5`, `pi29_mul_pi29' = 29`, `sqrt241Int_mul_self = 241`,
  `eps_mul_sigmaInt_eps : ε σ(ε) = -1`; conjugates `sigmaInt_eps = -epsInv`,
  `sigmaInt_pi2 = -pi2'`, `sigmaInt_pi2' = -pi2`, `sigmaInt_pi3 = pi3'`, … .
* `epsUnit : (𝓞 B)ˣ`.
* `alpha`, `alpha_coords : (alpha i : B) = radicandA i + radicandB i * √241`,
  `coe_alpha : ((alpha i : B) : Closure) = CanonicalGenus.radicand i`,
  `radicand_mem_B`, `norm_alpha : Algebra.norm ℤ (alpha i) = ![1,-1,-2,-2,-3,-3,-5,-5] i`,
  `alpha_ne_zero`.

## 3. Primes (`Primes.lean`)

* Coordinates `coordM, coordN` (`mk_coord`), and for any commutative ring `R`
  and `r : R` with `r * r = r + 60` the ring map
  `evalHom r hr : 𝓞 B →+* R` (`ω ↦ r`), `evalHom_mk`, `evalHom_omega`,
  `evalHom_surjective` (onto `ZMod p`).
* Split primes. For `N ∈ {2, 2', 3, 3', 5, 5', 29, 29'}` and also the ramified
  `N = 241`: `PN : Ideal (𝓞 B) := span {π}`; residue map
  `resN : 𝓞 B →+* ZMod p` (`= evalHom r`, roots `r`: `res2 ω = 0`, `res2' ω = 1`,
  `res3: 0`, `res3': 1`, `res5: 1`, `res5': 0`, `res29: 2`, `res29': 28`,
  `res241: 121`); `PN_eq_ker : PN = RingHom.ker resN`, `mem_PN : x ∈ PN ↔ resN x = 0`;
  instances `isMaximal_PN`, `isPrime_PN`, `liesOver_PN : PN.LiesOver (span {(p : ℤ)})`;
  `absNorm_PN = p`, `inertiaDeg_PN = 1`, `prime_π`, `natCast_mem_PN`, `PN_ne_bot`,
  `residueEquivN : 𝓞 B ⧸ PN ≃+* ZMod p`.
* `span_two_eq : span {2} = P2 * P2'`, `span_three_eq`, `span_five_eq`, `span_29_eq`,
  `span_241_eq : span {241} = P241 ^ 2`; `P2_ne_P2'`, `P3_ne_P3'`, `P5_ne_P5'`,
  `P29_ne_P29'`; `eq_P2_or_P2' : (2 : 𝓞 B) ∈ P → P = P2 ∨ P = P2'` (for prime `P`),
  likewise `eq_P3_or_P3'`, `eq_P5_or_P5'`, `eq_P29_or_P29'`, `eq_P241`.
* Inert 7: `prime_seven : Prime (7 : 𝓞 B)`, `P7 = span {7}`, `isMaximal_P7`,
  `absNorm_P7 = 49`, `inertiaDeg_P7 = 2`, `liesOver_P7`, `eq_P7`,
  `residueEquiv7 : 𝓞 B ⧸ P7 ≃+* GaloisField 7 2`.
* Galois action: `map_sigmaInt_P2 : P2.map sigmaInt = P2'` and the other swaps
  (`P3 ↔ P3'`, `P5 ↔ P5'`, `P29 ↔ P29'`), `map_sigmaInt_P7`, `map_sigmaInt_P241`.
* General helpers: `liesOver_of_natCast_mem`, `natCast_mem_of_liesOver`,
  `inertiaDeg_eq_of_absNorm`, `span_eq_ker_of_norm`, `isMaximal_span_of_norm`,
  `prime_of_norm`, `intCast_dvd_mk_iff : (k : 𝓞 B) ∣ mk a b ↔ k ∣ a ∧ k ∣ b`.

## 4. Class number (`ClassNumber.lean`)

* `minkowskiBound_lt_eight`: the Minkowski bound `(1/2)√241 < 8`.
* `isPrincipalIdealRing : IsPrincipalIdealRing (𝓞 B)` (also an instance),
  `classNumber_eq_one : NumberField.classNumber B = 1`.

## 5. Units (`Units.lean`)

* `unitRank_eq_one`, `torsion_eq_one_or_neg_one`, `mem_torsion_iff`,
  `fundUnit` (Mathlib's `fundSystem`), `eq_pm_zpow (u) : u = ± fundUnit ^ m`,
  `unitNorm : (𝓞 B)ˣ →* ℤˣ`, `unitNorm_epsUnit = -1`,
  `epsUnit_eq : epsUnit = ± fundUnit ^ k` with `k` odd.
* **`unit_eq_mul_sq (u : (𝓞 B)ˣ) : ∃ a b : ℕ, a < 2 ∧ b < 2 ∧ ∃ w, u = (-1) ^ a * epsUnit ^ b * w ^ 2`.**
  (Whether `ε` is itself fundamental is not needed and not proved.)

## 6. S-units modulo squares (`SUnits.lean`, `Signs.lean`)

* Signs (`Signs.lean`): `signPlus = ![1,0,1,1,1,0,1,0]`, `signMinus = ![1,1,0,0,0,1,0,1]`
  (`1` = negative; PARI lines `c1`, `c2`), `embPlus_alpha_sign`, `embMinus_alpha_sign`
  (`signX i = 1 → embX (alpha i) < 0`, `signX i = 0 → 0 < embX (alpha i)`),
  `embPlus_eps_pos`, `embMinus_eps_neg`, `embPlus_mul_embMinus : embPlus x * embMinus x = N(x)`.
* Valuations: `heightOneOf q hq : HeightOneSpectrum (𝓞 B)` (the prime `(q)`),
  `primeS i hi := heightOneOf (alpha i) _` for `2 ≤ i`, `prime_alpha`,
  `exists_prime_generator`, `exists_alpha_of_thirty_mem` (a prime containing `30`
  is `(alpha i)`, `2 ≤ i`), `thirty_mem_span_alpha`,
  `alpha_mem_span_alpha_iff : alpha j ∈ span {alpha i} ↔ j = i` (`2 ≤ i`),
  `intValuation_alpha : (primeS i hi).intValuation (alpha j) = if j = i then exp (-1) else 1`,
  `isSquare_exp_iff : IsSquare (exp n : ℤᵐ⁰) ↔ Even n`,
  `alphaCoords`, `alpha_eq_mk`, `evalHom_alpha`.
* `alphaProd (e : Fin 8 → ℕ) : B := ∏ i, (alpha i : B) ^ e i`, `alphaProd_add`,
  `alphaProd_single`, `alphaProd_mod_two`, `valuation_alphaProd`.
* **`sUnit_squareclass (β : B) (hβ : β ≠ 0) (heven : ∀ v : HeightOneSpectrum (𝓞 B), (30 : 𝓞 B) ∉ v.asIdeal → IsSquare (v.valuation B β)) : ∃ e : Fin 8 → ℕ, (∀ i, e i < 2) ∧ ∃ γ : B, γ ≠ 0 ∧ β = alphaProd e * γ ^ 2`.**
* **`alphaProd_independent {e} (he : ∀ i, e i < 2) {γ : B} (h : alphaProd e = γ ^ 2) : e = 0`**,
  `isSquare_alphaProd_iff`. Together: `V = S-units/squares` has basis `alpha`, dim 8.

### Tower-plan interface (`Selmer.lean`)

* `S : Set (HeightOneSpectrum (𝓞 B)) := {v | (30 : 𝓞 B) ∈ v.asIdeal}` (same definition as
  the plan's `Tower.S`; `mem_S`), `sPlace : Fin 6 → HeightOneSpectrum (𝓞 B)`
  (`sPlace j = (alpha (j+2))`, `sPlace_injective`, `sPlace_zero : sPlace 0 = vP2`, …),
  `mem_S_iff : v ∈ S ↔ ∃ j, v = sPlace j`,
  `mem_S_iff' : v ∈ S ↔ v = vP2 ∨ v = vP2' ∨ v = vP3 ∨ v = vP3' ∨ v = vP5 ∨ v = vP5'`,
  `SFin : Finset _`, `mem_SFin_iff : v ∈ SFin ↔ v ∈ S`, `SFin_card : SFin.card = 6`, `S_finite`.
* Places `vP2, vP2', vP3, vP3', vP5, vP5', vP29, vP29' : HeightOneSpectrum (𝓞 B)`
  (`vPN := heightOneOf π prime_π`, `vPN_asIdeal : vPN.asIdeal = PN`).
* `alphaB (i : Fin 8) : B := radicandA i + radicandB i * sqrt241` (via `algebraMap ℚ B`),
  `alphaB_eq : alphaB i = (alpha i : B)`, `coe_alphaB : (alphaB i : Closure) = radicand i`,
  `alphaB_ne_zero`, `prod_alphaB_pow_val`.
* **`alpha_independent (w : Fin 8 → ZMod 2) (h : IsSquare (∏ i, alphaB i ^ (w i).val)) : w = 0`.**
* **`mem_V_of_even_outside_S (x : Bˣ) (h : ∀ v, v ∉ S → Even (Multiplicative.toAdd (v.valuationOfNeZero x))) : ∃ (w : Fin 8 → ZMod 2) (c : Bˣ), (x : B) = (∏ i, alphaB i ^ (w i).val) * c ^ 2`.**
* `isSquare_valuation_iff_even`, and
  `UnitDistance.Sqrt241.CanonicalGenus.base_le_field : Base.B ≤ CanonicalGenus.field`.
* Units modulo squares are independent: `neg_one_pow_mul_eps_pow_isSquare_iff`
  (`a, b < 2`: `(-1)^a ε^b` is a square in `B` iff `a = b = 0`), `not_isSquare_neg_one`,
  `not_isSquare_eps`, `not_isSquare_neg_eps`.

## 7. Local data

### p-adic embeddings (`Local.lean`)

* General: `evalHom`-based `iotaInt r hr : 𝓞 B →+* ℤ_[p]` and
  `iota r hr : B →ₐ[ℚ] ℚ_[p]` (`√241 ↦ 2r - 1`, `ω ↦ r`), `iota_coe`,
  `iota_sqrt241`; Hensel roots `exists_omegaRoot`, `exists_omegaRoot_two`;
  `padicInt_norm_lt_one_iff : ‖x‖ < 1 ↔ toZMod x = 0`, `padicInt_isUnit_iff`;
  square-class criteria `padicInt_eq_mul_sq_of_toZMod` (odd `p`),
  `padicInt_eq_mul_sq_of_residue8` (`p = 2`).
* Named roots/embeddings for `N ∈ {2, 2', 3, 3', 5, 5', 29, 29'}`:
  `rootN : ℤ_[p]` (`rootN_mul_self`, `toZMod_rootN`, `residue8_root2 = 4`,
  `residue8_root2' = 5`), `iotaN : B →ₐ[ℚ] ℚ_[p]`, `iotaIntN`, `iotaN_coe`.
* Prime correspondence: `mem_PN_iff_norm_iota (x : 𝓞 B) : x ∈ PN ↔ ‖iotaIntN x‖ < 1`.
* Conjugate embeddings: `iota2'_eq_comp_sigma : iota2' = iota2.comp sigma`,
  `iota3'_eq_comp_sigma`, `iota5_eq_comp_sigma` (`iota5 = iota5' ∘ σ`), `iota29'_eq_comp_sigma`.
* Every embedding is named (`LocalRoots.lean`): `sq_eq_241_iff_2 (s : ℚ_[2]) : s ^ 2 = 241 ↔ s = iota2 sqrt241 ∨ s = iota2' sqrt241`
  (and `_3`, `_5`, `_29`), `algHom_eq_iota2_or (f : B →ₐ[ℚ] ℚ_[2]) : f = iota2 ∨ f = iota2'`,
  `ringHom_eq_iota2_or` (and for 3, 5, 29), `algHom_alphaB`.
* Root form of the tables (for a chosen place whose image of `√241` is either root):
  `radicand_squareclassN (i) : ∃ z ≠ 0, radicandA i + radicandB i * iotaN sqrt241 = squareclassN i * z ^ 2`
  for `N ∈ {2, 2', 3, 3', 5, 5', 29, 29'}`. `iota_sqrt241 : iota r hr sqrt241 = 2 r - 1`
  with `residue8_root2 = 4`, `residue8_root2' = 5`, `toZMod_root3 = 0`, `toZMod_root5 = 1`,
  `toZMod_root29 = 2`: so `iota2 √241 ≡ 7`, `iota2' √241 ≡ 1 (mod 8)`, `iota3 √241 ≡ 2 (mod 3)`,
  `iota5 √241 ≡ 1 (mod 5)`, `iota29 √241 ≡ 3 (mod 29)` — the plan's "first primes"
  (numerically `iota2 √241 ≡ 7`, `iota2' √241 ≡ 25 (mod 32)`; Lean records only mod 8).
* `not_isSquare_241_Q7 : ¬ IsSquare (241 : ℚ_[7])`.
* **Square classes** `iotaN_alpha (i) : ∃ z : ℚ_[p], z ≠ 0 ∧ iotaN (alpha i) = squareclassN i * z ^ 2`:

  | N | representatives of `(-1, ε, π₂, π₂', π₃, π₃', π₅, π₅')` |
  |---|---|
  | 2  | 7, 3, 6, 3, 1, 5, 3, 1 |
  | 2' | 7, 5, 5, 10, 5, 1, 1, 3 |
  | 3  | -1, 1, -1, 1, 3, -1, -1, -1 |
  | 3' | -1, -1, -1, 1, -1, 3, -1, -1 |
  | 5  | 1, 2, 2, 1, 1, 2, 10, 2 |
  | 5' | 1, 2, 1, 2, 2, 1, 2, 10 |
  | 29 | 1, 1, 2, 1, 1, 2, 2, 2 |
  | 29'| 1, 1, 1, 2, 2, 1, 2, 2 |

  These reproduce every Hilbert-symbol line of `kummer241.gp` (dyadic x(5), y(-1),
  z(-2); tame τ, φ(-π); cap29) by the standard formulas for `(a, b)_p`.

### Valuations and completions (`LocalValuation.lean`, `Completion.lean`)

* Places `vPN` (defined in `Selmer.lean`).
* **`valuation_vPN_eq (x : B) : vPN.valuation B x = Padic.mulValuation (iotaN x)`**: the
  `𝔭`-adic valuation is the `p`-adic valuation through the embedding (exact equality).
  Generic: `valuation_eq_mulValuation`, `valuation_iota_uniformizer`,
  `norm_iota_eq_one_of_not_mem`, `mulValuation_eq_one_of_norm`.
* **`adicCompletionEquivN : vPN.adicCompletion B ≃+* ℚ_[p]`**, with
  `adicCompletionEquivN_coe (x : B) : adicCompletionEquivN (x : vPN.adicCompletion B) = iotaN x`,
  `continuous_adicCompletionEquivN`, `continuous_adicCompletionEquivN_symm`.
  Generic: for `w = Padic.mulValuation ∘ f` with `f : K →+* ℚ_[p]` of dense range,
  `completionEquivPadic hw hdense : w.Completion ≃+* ℚ_[p]` (`completionEquivPadic_coe`,
  `isUniformInducing_withValToPadic`, `isDenseInducing_withValToPadic`), following
  Mathlib's `Padic.withValRingEquiv`; `denseRange_iota`.

### Residue symbols at unramified primes (`Residues.lean`)

* `isSquare_res29_alpha : (∃ t, res29 (alpha i) = t * t) ↔ frob29 i = 0`,
  `frob29 = ![0,0,1,0,0,1,1,1]`; `isSquare_res29'_alpha`, `frob29' = ![0,0,0,1,1,0,1,1]`.
* `isSquare_quotient_P7_alpha : IsSquare (Ideal.Quotient.mk P7 (alpha i)) ↔ frob7 i = 0`,
  `frob7 = ![0,1,1,1,0,0,0,0]`; `isSquare_mod_seven_alpha`, `norm_mod_seven_congr`.

## Open / next steps

* Hilbert symbols as such are not defined; the square classes above determine them
  (standard formulas at `p = 2` and odd `p`).
* The completion at the inert prime `7` (unramified quadratic over `ℚ₇`) and at
  `(√241)` are not identified with concrete local fields; at `7` only the residue-field
  square classes (`frob7`) are given.
* `adicCompletionEquivN` is a continuous ring isomorphism (hence `ℚ`-linear); it is not
  packaged as `≃A[ℚ]`. `primeS 2 _` and `vP2` are equal places (both `heightOneOf` of
  `pi2`, up to the proof of primality).
* `scripts/sqrt241/generate_base_tables.py primes|local --write` regenerates the
  per-prime block of `Primes.lean` and the embedding/square-class block of `Local.lean`,
  which are enclosed by `-- BEGIN Generated by …`/`-- END Generated by …` lines
  (`--check` compares; see the script header).
