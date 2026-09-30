# Stream E: root discriminant of the tower fields (T11)

Owner: `UnitDistance/Sqrt241/Discriminant/`, `scripts/sqrt241/dyadic_certificate.gp`,
`scripts/sqrt241/generate_dyadic_certificate.py`, this note. Mathematics and PARI
data: [E_RD_DATA.md](E_RD_DATA.md).

## Status (2026-09-29): done, both routes

All modules compile (`lake build UnitDistance.Sqrt241.Discriminant.All`); the
main results depend only on `propext`, `Classical.choice`, `Quot.sound`
(`#print axioms` from a scratch file outside the repository). No `sorry`,
`native_decide`, `axiom`; the model identities use `decide +kernel`.
The submission uses route E in the form `log_rootDiscriminant_le_of_sqrt_beta₁`,
through `DyadicLink.log_rootDiscriminant_input_M`; `Discriminant/All.lean` and
route T (`Discriminant/RouteT.lean`) are outside the submission closure (see
[SUBMISSION.md](SUBMISSION.md)).

### Main theorem (route E)

`UnitDistance.Sqrt241.log_rootDiscriminant_le` (`Discriminant/RootDiscriminant.lean`):

```lean
theorem UnitDistance.Sqrt241.log_rootDiscriminant_le
    (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] [Algebra CanonicalGenus.Carrier K]
    (s₁ s₂ : K) (hs₁ : s₁ ^ 2 = algebraMap Carrier K Discriminant.beta₁)
    (hs₂ : s₂ ^ 2 = algebraMap Carrier K Discriminant.beta₂)
    (he2 : (rationalPrimeIdeal 2).ramificationIdxIn (𝓞 K) = 8)
    (he3 : (rationalPrimeIdeal 3).ramificationIdxIn (𝓞 K) = 2)
    (he5 : (rationalPrimeIdeal 5).ramificationIdxIn (𝓞 K) = 2)
    (he241 : (rationalPrimeIdeal 241).ramificationIdxIn (𝓞 K) = 2)
    (hunr : ∀ p : ℕ, p.Prime → p ∉ ({2, 3, 5, 241} : Finset ℕ) →
      (rationalPrimeIdeal p).ramificationIdxIn (𝓞 K) = 1) :
    Real.log (NumberFieldAnalysis.rootDiscriminant K) ≤ Witness.logRD
```

with `rationalPrimeIdeal = UnitDistance.NumberFieldAnalysis.rationalPrimeIdeal`
and, in `E = CanonicalGenus.Carrier` (namespace `UnitDistance.Sqrt241.Discriminant`:
`rootE = √241`, `genusE i = genusRoot i` as elements of `E`):

* `Discriminant.beta₁ = (-25 + 2·rootE) + (-139 - 9·rootE) · genusE 3`
  (`√π₂' = genusRoot 3`),
* `Discriminant.beta₂ = (-25 - 2·rootE) + (-139 + 9·rootE) · (genusE 0 · genusE 2)`
  (`√(-π₂) = genusRoot 0 · genusRoot 2`).

The hypotheses are the task's, verbatim. **Stronger variant without `s₂`:**
`UnitDistance.Sqrt241.log_rootDiscriminant_le_of_sqrt_beta₁` (same statement,
only `s₁`, `hs₁`): since `K` is Galois, an automorphism with `√241 ↦ -√241`
(`minpoly.exists_algEquiv_of_root'`) transports the dyadic certificate to the
primes above `𝔭₂`. So the tower only has to put `√β₁` into `K_j` (or `M`).
Remarks for the tower side: of the ramification hypotheses, `e₂ = 8` is used
exactly and the ones at 3, 5, 241 only as `e ≤ 2`; replacing
`genusRoot 3` (resp. `genusRoot 0 · genusRoot 2`) by its negative replaces `β`
by `π₃'/β` (resp. `π₃/β`), and `√π₃, √π₃' ∈ E`, so `hs₁`, `hs₂` do not depend on
the sign choice. `E` itself is used only as a source of elements
(`√241, √2 = g₂g₃, √π₂' = g₃, √(-π₂) = g₀g₂, √-3 = g₄g₅, √5 = g₀g₆g₇`); no
property of `E` (degree, discriminant, local types) is needed.

### Other entry points

| declaration | module | content |
|---|---|---|
| `log_rootDiscriminant_le_of_sqrt_beta₁` | RootDiscriminant | main theorem without `s₂` (see above) |
| `Discriminant.log_rootDiscriminant_le_of_realization` | RootDiscriminant | same bound from a `Dyadic.Realization K` (`r,t,g,s` with `r²=241, t²=2, g²=π₂'(r), s²=β₁`), `x₃² = -3`, `x₅² = 5`, `K` Galois, same `e` hypotheses |
| `Discriminant.log_rootDiscriminant_le_of_elements` | RootDiscriminant | same bound from explicit elements of `K`: a `Dyadic.Realization K` (`r,t,g,s` with `r²=241, t²=2, g²=π₂'(r), s²=β₁`), `g', s'` with `g'² = π₂'(-r)`, `s'² = β₁(-r,g')`, `x₃² = -3`, `x₅² = 5`, same `e` hypotheses |
| `Discriminant.log_rootDiscriminant_le_of_dyadic` | RootDiscriminant | assembly: `x₃² = -3, x₅² = 5, r² = 241`, `8·v₂|disc K| ≤ 18·[K:ℚ]`, `e = 2` at 3, 5, 241, unramified outside `{2,3,5,241}` ⇒ `log rd(K) ≤ logRD` |
| `Discriminant.log_rootDiscriminant_le_of_retained_comparison` | RouteT | **route T**: `L` Galois over ℚ with `[Algebra K L]`, `[Algebra ArithmeticRetained.RetainedField L]`, `e₂(L) = 8`, plus the tame/unramified hypotheses ⇒ bound |
| `Discriminant.eight_mul_factorization_two_le_of_comparison` | RouteT | `K → L ← R` Galois, `e₂(L) = e₂(K) = e₂(R)`: `8 v₂(R) ≤ 18 [R:ℚ] ⇒ 8 v₂(K) ≤ 18 [K:ℚ]` |
| `Discriminant.retainedField_eight_mul_factorization_two_le` | RouteT | verified ℚ retained field: `8 v₂|disc R_ℚ| ≤ 18·2¹⁹` (from `retainedRelativeDifferentTwoExponent_le`, `chosenGenus_natAbs_discr`) |
| `Discriminant.Dyadic.Realization.eight_mul_factorization_two_le` | Dyadic | **route E dyadic factor**: realization + conjugate data, all primes above 2 with `e = 8` ⇒ `8 v₂|disc K| ≤ 18 [K:ℚ]` |
| `Discriminant.Dyadic.Realization.eight_mul_factorization_two_le_of_isGalois` | Dyadic | same, `K` Galois, no conjugate data |
| `Discriminant.Dyadic.Realization.not_pow_nineteen_dvd_differentIdeal` | Dyadic | `P ∋ π₂`, `e(P|2) ≤ 8` ⇒ `P¹⁹ ∤ 𝔇(K/ℚ)` |

### Generic lemmas (reusable, any number fields)

`Discriminant/Generic.lean`:
* D1 `factorization_discr_eq_of_unramifiedAbove`: `K/F` unramified at all primes
  above `p` ⇒ `v_p|disc K| = [K:F]·v_p|disc F|` (and the normalized form
  `factorization_discr_mul_finrank_eq_of_unramifiedAbove`).
* D2 `isUnramifiedAt_of_ramificationIdx_le`: every prime of `F` above `p` has
  `e ≥ e₀` and every prime of `K` above `p` has `e ≤ e₀` ⇒ `K/F` unramified above `p`.
* (a) `factorization_discr_mul_finrank_eq_of_ramificationIdxIn_eq`: `F → K` both
  Galois, same `ramificationIdxIn` at `p` ⇒ `v_p(K)·[F:ℚ] = v_p(F)·[K:ℚ]`.
* `ramificationIdx_eq_ramificationIdxIn` (Galois), `not_dvd_natAbs_discr_of_ramificationIdxIn_eq_one`.
* D4 `log_rootDiscriminant_eq_sum`, `log_rootDiscriminant_le_sum`.

`Discriminant/Tame.lean`: `two_mul_factorization_discr_eq_of_sqrt(_of_ramificationIdxIn)`:
`x ∈ K`, `x² = d` squarefree non-square `≡ 1 (4)`, `p ∣ d`, all primes of `K`
above `p` with `e ≤ 2` ⇒ `2·v_p|disc K| = [K:ℚ]` (via `ℚ(x)`, `disc = d`, D1, D2;
no tame different formula).

`Discriminant/NormFactorization.lean`: `factorization_absNorm_eq_sum`
(`v_p(N J) = Σ_{Q|p} f(Q|p)·mult_Q J`) and `mul_factorization_absNorm_le`
(`e(Q|p) = e`, `Q^{d+1} ∤ J` for all `Q | p` ⇒ `e·v_p(N J) ≤ d·[K:ℚ]`).

`Discriminant/Horner.lean`: integer coefficient lists (`horner`, `hornerD`,
`hornerPoly`, monicity, `aeval`), `quadLift` (extend `ψ : R →+* A` to
`QuadraticAlgebra R a 0` by `u` with `u² = ψ a`).

## Mathematics of route E (why no rd(E) and no R = E(√β₁,√β₂) is needed)

For `K` Galois, `v_p|disc K| = Σ_{P|p} f_P·v_P(𝔇_K)` (norm factorization), so it
suffices to bound `v_P(𝔇_K)` at every prime. At `p = 3, 5, 241` compare with
`ℚ(√-3)`, `ℚ(√5)`, `ℚ(√241)` (D1+D2). At `p = 2`: let
`F = ℚ(y) ⊆ K` where `y` generates the prime `Q` above `𝔭₁ = (π₂)` of the
degree-16 field `ℚ(√241, √2, √π₂', √β₁)` (PARI: its dyadic primes are
`(8,1), (2,2), (2,2)` with different exponents `18, 3, 3`; `Q` is principal).
With `f` = char. poly. of `y` (monic, `ℤ`), `u = y⁸/π₂` (unit, char. poly. `h`):

1. `y⁸ = π₂ u` ⇒ every prime `P ∋ π₂` of `K` contains `y`;
2. `f = X⁸ G + 2 Kp`, `Kp(0) = 1` ⇒ `Q = P ∩ 𝓞_F` has `e(Q|2) ≥ 8`; with
   `e(P|2) ≤ 8` this makes `K/F` unramified at `P`;
3. `f'(y) ∈ 𝔇(F/ℚ)` and `f' = X¹⁸ Z + f W` with `Z(0)` odd ⇒ `v_P(f'(y)) ≤ 18`;
4. `𝔇(K/ℚ) = 𝔇(K/F)·𝔇(F/ℚ)𝓞_K` ⇒ `v_P(𝔇_K) ≤ 18`.

The conjugate realization (`r ↦ -r`, `√(-π₂)`, `√β₂`), or for Galois `K` the
image of the realization under an automorphism with `r ↦ -r`, covers the primes
above `𝔭₂ = (π₂')`. Then `8·v₂|disc K| ≤ 18·[K:ℚ]`, i.e. the 2-part of `rd` is at most
`2^{9/4}`.

The certificate is verified in the explicit model `M4 = ℚ[r,t,g,s]` (nested
`QuadraticAlgebra` over ℚ) by `decide +kernel` (`f(y) = 0`, `π₂ u = y⁸`,
`h(u) = 0`: ≈ 25 s), transported to `K` along `quadLift`; the polynomial identities
are proved by `ring`. `π₂ u = y⁸` is checked through the explicit private powers
`y2M`, …, `y8M`: seven single products by `yM` and `pi2M * uM = y8M`, each its own
`decide +kernel`, composed by congruence and transitivity. NanoDa, one of the
independent kernels of the Palomar pipeline, exhausted its memory on a single
reduction of the eightfold product (2026-09-29; `verification/sqrt241-full-20260929/README.md`,
where this repair was reviewed and verified).

## Route T (coordinator's recommendation)

`log_rootDiscriminant_le_of_retained_comparison` needs, besides the tame and
unramified hypotheses, a Galois number field `L` with `K → L ← R_ℚ`
(`R_ℚ = ArithmeticRetained.RetainedField`) and `e₂(L) = 8`. For the tower this is
the compositum `K_j · R_ℚ` inside `AlgebraicClosure ℚ` (via
`ArithmeticDyadic.retainedAbsoluteEmbedding`), with `e₂ = 8` from the equality
of inertia kernels at the chosen dyadic place (tower agents, T5/T10). Route E
instead needs `√β₁ ∈ K_j` (e.g. `√β₁ ∈ M`; `√β₂` then comes for free by Galois
conjugation, `log_rootDiscriminant_le_of_sqrt_beta₁`).

## Files

| module | lines | content |
|---|---|---|
| `Discriminant/Generic.lean` | 225 | D1, D2, (a), D4, unramified primes |
| `Discriminant/Tame.lean` | 209 | quadratic subfields, tame primes |
| `Discriminant/NormFactorization.lean` | 195 | `v_p(N J)` as a sum over primes |
| `Discriminant/Horner.lean` | 129 | coefficient lists, `quadLift` |
| `Discriminant/DyadicModel.lean` | 203 | generated certificate + kernel checks |
| `Discriminant/Dyadic.lean` | 550 | realization, valuation argument, dyadic bound |
| `Discriminant/RootDiscriminant.lean` | 300 | assembly, main theorems |
| `Discriminant/RouteT.lean` | 126 | comparison with the ℚ retained field |
| `Discriminant/All.lean` | 27 | umbrella |

## Rebuild

    ./.toolchain/bin/lake build UnitDistance.Sqrt241.Discriminant.All     # ≈ 1 min after deps
    gp -q scripts/sqrt241/dyadic_certificate.gp < /dev/null               # certificate data + PARI checks
    python3 scripts/sqrt241/generate_dyadic_certificate.py                # regenerates DyadicModel.lean

(`lake build` of several targets at once runs Lean processes in parallel; build
one target at a time on the shared machine.)

## Open items

None for the stated theorem. Interface owed by the tower (either suffices):
`√β₁ ∈ K_j` (route E), or a Galois `L ⊇ K_j, R_ℚ` with `e₂(L) = 8` (route T). Possible follow-ups on request: a version of the
main theorem with hypotheses `e_p ≤ 2` at 3, 5, 241 (already the form of
`two_mul_factorization_discr_eq_of_sqrt`), or with `R := E(√β₁, √β₂)` and
`FiniteUnramified R K`.
