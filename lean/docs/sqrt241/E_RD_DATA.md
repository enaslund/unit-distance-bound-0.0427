# Root discriminant over ℚ(√241): explicit dyadic data

Reproduce: `gp -q scripts/sqrt241/dyadic_radicals.gp < /dev/null`.

## Target

For every tower field K_j (and the retained field M):

    log rd(K_j) ≤ (9/4) log 2 + (1/2) log 3615,
    i.e. rd = 2^{9/4} · 3^{1/2} · 5^{1/2} · 241^{1/2}.

For K Galois over ℚ, the p-exponent of rd(K) is v_P(𝔇_{K/ℚ})/e_P for any
P | p. The primes 3, 5 and 241 are tame with e = 2, giving exponent 1/2. At 2,
e = 8 and the different exponent must be exactly 18. The margin tolerates no
larger value: the next possible exponent is 19/8.

## The ramified dyadic directions

Kummer basis (0-based): α₀ = −1, α₁ = ε, α₂ = π₂, α₃ = π₂′, α₄ = π₃, α₅ = π₃′,
α₆ = π₅, α₇ = π₅′. π₂ has valuation 1 at the first dyadic prime 𝔭₁ (PARI's
`idealprimedec(K,2)[1]`), and π₂′ at 𝔭₂.

In the local group D at 𝔭₁ (generators x = Art(5), y = Art(−1), z = Art(−2)),
the ramified quadratic direction is the commutator [y, z]. Among the 15
functionals annihilating the relation span R₂, the one detecting it is
λ₁ = x₃x₅, a single product. At 𝔭₂ it is λ₂ = (x₀ + x₂)x₄. Each is realized by a
D₄-extension of B:

* β₁ = (−25 + 2√241) + (−139 − 9√241)·√π₂′ ∈ B(√π₂′), with
  N_{B(√π₂′)/B}(β₁) = π₃′ exactly;
* β₂ = σ(β₁) = (−25 − 2√241) + (−139 + 9√241)·√(−π₂) ∈ B(√(−π₂)), with
  norm π₃ (σ : √241 ↦ −√241, which sends π₂′ ↦ −π₂ and π₃′ ↦ π₃).

**Membership in M.** E(√β₁)/B is Galois: the class of β₁ is fixed modulo
squares, since β₁·σ_a(β₁) = π₃′ and √π₃′ ∈ E. It is a central C₂-extension of
Gal(E/B) with quadratic form x₃x₅ ∈ R₂^⊥, unramified outside S (β₁ is an
S-unit), of class 2 and exponent 4. Hence it lies in the D₃-retained field of
the cut group. Formally this still needs either the Kummer correspondence
between R₂^⊥ and such extensions, or a direct check of the cut words on √β₁.
The same holds for β₂. With R := E(√β₁, √β₂), which is Galois over ℚ, we have
R ⊆ M ⊆ K_j.

## Local numbers (PARI)

| field | degree | disc | primes above 2: (e,f) | v(𝔇) |
|---|---|---|---|---|
| F8 = B(√π₂′, √π₃′) | 8 | 2¹⁰·3²·241⁴ | (2,1),(2,1),(2,2) | |
| F16 = F8(√β₁) | 16 | 2²⁴·3⁴·241⁸ | four (2,1); one (4,2) | 3,3,3,3,6 |
| F32 = F16(√2) | 32 | 2⁶⁰·3⁸·241¹⁶ | (2,2)×4; **(8,2)** | 3,3,3,**18**,3 |

At 𝔭₁, F32 has a prime with e = 8 and v(𝔇)/e = 18/8 = **9/4**, as required.
Its local field there is ℚ₂(√−1, √5, √2, √β₁) = L₁(√β₁), where
L₁ = ℚ₂(ζ₈, √5) is the completion of E. The completion of M at 𝔭₁ is
L₁(√β₁) times an unramified quadratic extension (f = 4). The completion at 𝔭₂
is symmetric via β₂.

## Suggested proof route (Lean)

1. **rd(E).** E is unramified over E₃₂ = ℚ(ζ₈, √−3, √5, √241) at every finite
   prime: both have e = 4 at 2 and e = 2 at 3, 5 and 241. Note √2, √−3, √−5
   lie in E since π₂π₂′ = 2, π₃π₃′ = −3, π₅π₅′ = −5. E₃₂ is a compositum of
   fields with pairwise coprime discriminants, so
   |disc E₃₂| = 2⁶⁴·(3·5·241)¹⁶ and rd(E) = 2²·(3·5·241)^{1/2}. Compare
   `GenusDiscriminant.lean`, which does the same over ℚ.
   The upper bound e(E at 2) ≤ 4 follows from local degree ≤ 8
   (|ℚ₂^×/ℚ₂^{×2}| = 8, see `PadicTwoMaximalProTwo`, `PadicTwoSquareclasses`)
   together with f ≥ 2 (√5 ∈ E).
2. **Dyadic step.** v(𝔇_{E(√β₁)/E}) = 2 at the primes above 𝔭₁, via an
   explicit integral generator (compare `RetainedDyadicDifferentGenerator`,
   `RetainedDyadicDifferentNorm`). √β₁ splits at 𝔭₂; symmetrically for β₂.
3. **Unramified top.** K_j (and M) are unramified over R at all finite primes,
   since e agrees at 2, 3, 5, 241. Then rd(K_j) = rd(R) (compare
   `RelativeUnramifiedSigma.finiteUnramified_of_sigma_ramificationIdxIn_eq`,
   `RetainedDyadicDifferentComplement`).
