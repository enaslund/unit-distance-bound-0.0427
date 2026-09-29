# A tower over Q(√241) and the exponent 1.04273

Date: 2026-09-29. Status: **research result; three independent referee
reviews found no mathematical error** (see [review-20260929.md](review-20260929.md)).
The finite computations below are reproducible from
[`../certificates`](../certificates). The mathematical reductions reuse the
proofs of the [1.0418235 manuscript](../../0.0418235/README.md)
over the base field B=Q(√241) instead of Q, and §6 lists exactly what that
transfer requires. It is not yet a self-contained manuscript.

## 1. Result claimed

With the base field B=Q(√241), the construction below gives finite planar
sets U_j with |U_j|→∞ and u(U_j)/|U_j|^{1+δ}→∞ for

    δ = 0.04273   (exponent 1.04273; the current manuscript has 1.0418235).

The certified geometric lower margin at δ=0.04273, after the concentration
allowance, is ≥ 0.000176, using the rigorous analytic ceiling
C = 0.04871285 of §4. At δ=0.0427 the margin is ≥ 0.000906.

## 2. Why a base field helps: amortizing the Golod–Shafarevich constant

The manuscript's infinitude criterion over Q is P(t)=1−7t+Σ(local costs)<0.
The constant 1 is fixed. Over a totally real base B of degree m in which every
prime used by the design splits completely, the Kummer generator count and
every local block are replicated m times, while the constant and the single
reciprocity saving s_D are not:

    P_B(t) = m·P_Q(t) − (m−1)(1 − s_D(t)).

So the per-copy polynomial need only satisfy P_Q < (1−s_D)(1−1/m). The price
is the base's own root discriminant, which enters ℓ = log rd. A design model
calibrated on the manuscript (it reproduces the published design as its
optimum and the certificate margin 5.336e-6) shows that among real quadratic
B with 2 split, D=241 is best by a wide margin: it is the smallest D≡1 (mod 8)
in which 2, 3 and 5 all split. See [design-search.md](design-search.md).

## 3. The tower over B

### 3.1 Base field

B=Q(√241): class number 1, fundamental unit
ε = 4574225√241 − 71011068 of norm −1, and 2, 3, 5 split:
2=𝔭₁𝔭₂, 3=𝔮₁𝔮₂, 5=𝔯₁𝔯₂. Real places v₁ (√241↦+√241) and v₂.

Kummer basis of V = S-units/squares (S = primes above 2,3,5), dimension 8:

| i | α_i | norm |
|---|---|---|
| 0 | −1 | 1 |
| 1 | ε | −1 |
| 2 | (−6101−393√241)/2 (generator of 𝔭₁) | −2 |
| 3 | (6101−393√241)/2 (generator of 𝔭₂) | −2 |
| 4, 5 | 31−2√241, 31+2√241 (𝔮₁, 𝔮₂) | −3 |
| 6, 7 | 326−21√241, 326+21√241 (𝔯₁, 𝔯₂) | −5 |

(These are exactly the elements used by `kummer241.gp` and `census241.py`;
subscripts follow PARI's `idealprimedec` order.)

### 3.2 Group and cuts

Let 𝒢_B be the Galois group of the maximal pro-2 extension of B unramified
outside {𝔭₁,𝔭₂,𝔮₁,𝔮₂,𝔯₁,𝔯₂}, with no condition at the real places.
Impose, exactly as the manuscript does over Q:

* at 𝔭₁ and 𝔭₂ (completions Q₂): the full kernel of the local map to the
  manuscript's dyadic group D of order 32 (local field L₂, e=8, f=4,
  normalized different 9/4);
* at 𝔮ⱼ and 𝔯ⱼ: inertia squares and Frobenius squares (local groups C₂²,
  e=2, f=2), with the Frobenius lift fixing its own Kummer class;
* at the two primes above 29 (split in B) and at the inert prime (7) of norm
  49: Frobenius fourth powers.

Call the quotient G_B. Real places keep their complex conjugations c₁, c₂.

### 3.3 Complete presentation over B

As in the manuscript's Lemma `tw:complete-global-presentation`:
H¹(𝒢_B,F₂)=V has dimension 8 (h(B)=1). The map H²(𝒢_B)→Br(X_B)[2] is
injective, Pic(O_B[1/30])=0, and Br(X_B)[2] is the sum-zero hyperplane on the
8 places (6 finite, 2 real), of dimension 7. The 36 quaternion classes
(α_i,α_j) have local invariant vectors of even weight spanning a space of
rank 7, and of rank 7 on the 7 places other than 𝔭₁ (`cup241.gp`). Hence
𝒢_B has a minimal presentation with 8 generators whose 7 relators are the
local relators at the places other than 𝔭₁; the dyadic relation at 𝔭₁ lies in
their closed normal closure.

### 3.4 Elementary data and the retained quotient

Local generators have reciprocity classes as in the manuscript (dyadic
x,y,z ↔ 5,−1,−2; tame τ ↔ non-square unit, φ ↔ −π; real c ↔ −1). Their
images in V^∨=F₂⁸ are Hilbert-symbol vectors (`kummer241.gp`):

| gen | vector | gen | vector |
|---|---|---|---|
| c₁ | 10111010 | c₂ | 11000101 |
| x₁ | 00100000 | x₂ | 00010000 |
| y₁ | 11110010 | y₂ | 10000001 |
| z₁ | 10000100 | z₂ | 11111000 |
| τ(𝔮₁) | 00001000 | φ(𝔮₁) | 10100111 |
| τ(𝔮₂) | 00000100 | φ(𝔮₂) | 11101011 |
| τ(𝔯₁) | 00000010 | φ(𝔯₁) | 01100101 |
| τ(𝔯₂) | 00000001 | φ(𝔯₂) | 01011010 |
| Frob(29₁) | 00100111 | Frob(29₂) | 00011011 |
| Frob(7) | 01110000 | | |

Quadratic initials (`lie241.py`), in the free restricted Lie algebra on 8
generators (dimension 36 in degree 2): c₁², c₂², the four tame relations
B(τ,φ)+((N−1)/2)S(τ), the two Demuškin initials S(y)+B(x,y)+B(x,z), the
dyadic cuts S(x), B(x,y), B(x,z) at each 𝔭ⱼ, inertia squares and Frobenius
squares at 𝔮ⱼ,𝔯ⱼ: 22 initials of rank 21 (one dependency, removed by dropping
either Demuškin initial). Hence L₂ = 15. The cubic layer: the 21 independent
initials bracketed with the 8 generators, together with the two dyadic cubics
[[yⱼ,zⱼ],zⱼ], span rank 142 in the 168-dimensional free degree-3 layer, so
L₃ = 26 and |G_B/D₄G_B| = 2⁴⁹ (`lie241c.py`).

Verified in these layers:

* each dyadic block: x,y,z independent, and z^[2], [y,z] independent modulo
  the relations (both primes);
* each tame block: τ, φ independent;
* the C₄ caps (both 29-primes and (7)): the square of the Frobenius is
  nonzero in L₂;
* ad(c₁) has rank 7 from L₁ to L₂ (kernel ⟨c₁⟩) and rank 8 from L₂ to L₃, so
  the class of c₁ in G_B/D₄G_B has size 2¹⁵;
* the elementary images of c₁ and c₂ lie outside every decomposition group's
  elementary span.

### 3.5 Infinitude

With the manuscript's block costs (Lemma `tw:filtered-local-freeness`,
Lemma `tw:new-local-fox`, and the shared dyadic row subtracted once):

    P_B(t) = 1 − 8t + 2c₁ + 4c₂ + 2d_D − s_D + 3c₄,
    P_B(34/117) = −187433948535241/88772225460489675 < 0   (`gs241.py`).

Hence G_B is infinite. Here c₁ covers the two real places, c₂ the four
C₂²-blocks, d_D the two dyadic blocks, s_D the single dyadic row, and c₄ the
three C₄ caps.

### 3.6 The fields

Take finite Galois extensions K/B in the tower, of unbounded degree,
containing the fixed field of D₄G_B. Put F=K^{⟨c₁⟩}, with [F:Q]=d.

* K is totally imaginary, and K/F is unramified at all finite places and
  split above 2, 3, 5, 7, 29: the conjugates of c₁ avoid every inertia and
  decomposition group (elementary separation).
* rd(K)=rd(F)=λ=√241·2^{9/4}·√15 ≈ 286.0, so ℓ = (9/4)log2 + (1/2)log(3·5·241).
* Real places of F lie only over v₁, and b/d = 1/(2|cl(c₁)|) ≤ 2⁻¹⁶. Over v₂,
  c₁ acts freely because c₁ and c₂ have different elementary images. Hence
  θ = c/d = (1−b/d)/2 ≥ 1/2 − 2⁻¹⁷ = 65535/131072.
* Uniform absolute local types (e,f) of the F-primes: 2:(8,4), 3:(2,2),
  5:(2,2), 29:(1,4), 7:(1,8). All split in K/F.

## 4. Analytic ceiling

### 4.1 Reduction

The manuscript's analytic section uses only that K/F is quadratic and
unramified at finite places, that K is totally imaginary, and that
rd(F)=rd(K)=λ. The steps are:

* monotonicity of the completed L_F on [1,∞);
* (1/d)log L_F(s) ≤ (1/(2d))log ζ_K(s);
* the gamma term G(ε,θ)→0, uniformly for θ ∈ [0,1/2];
* the Tsfasman–Vlăduţ basic inequality, valid for any asymptotically exact
  family. Here φ_C=1/ℓ because √−1 ∈ E_B ⊆ K.

Proposition `an:prime-budget` is stated over Q with absolute floors per
rational prime, and argued "for a Galois field, above p". Over B its
statement, hypothesis and last proof step must be restated per prime of B,
because the two primes above a split p can have different types in
principle. The per-prime-of-B version is as follows.

* **Local contribution.** If 𝔭 has relative indices (e,f) in K (K Galois
  over B), then [K:B]/(ef) primes of K lie over 𝔭, and they contribute
  a_σ(N𝔭^f)/(2ef) to (1/[K:Q])log ζ_K(σ), with a_σ(q) = −log(1−q^{−σ}).
  Since a(Q^m) ≤ m·a(Q), this can only decrease in extensions Galois over B.
* **Floors.** For uniform lower bounds e⁰_𝔭, f⁰_𝔭 per prime of B, the
  proposition's R becomes R ≥ Σ_𝔭 log N𝔭/(2e⁰_𝔭(N𝔭^{2f⁰_𝔭}−1)). Its
  Fatou step is unchanged, and at 241 the relative index e=1 gives the
  absolute value.
* **Conclusion.** Then

      limsup (1/d) log L_F(1) ≤ Y_*(σ) + ε((ℓ−γ−log4π)/4 + R),   σ=1+ε,

  and every strictly larger constant is an eventual uniform ceiling.

### 4.2 Y_* from the genus field

The genus field E_B = B(√V) has degree 256 over B and lies in every K.
Every defining relation of G_B lies in its Frattini subgroup:

* the Koch local relators;
* the inertia squares, Frobenius squares and Frobenius fourth powers;
* the kernel of the dyadic local map to D, which lies in the local Frattini
  subgroup because D is 3-generated, like the local group of Q₂.

So G_B/Φ(G_B) = V^∨ has dimension 8 (equivalently, L₁ has no degree-one
relations), and


    (1/512) log ζ_{E_B}(σ) = (1/512)[log ζ_B(σ) + Σ_{e≠0} log L(σ,χ_e)],

where χ_e is the quadratic character of B(√α_e)/B. As an L-function over Q,
L(s,χ_e)=ζ_{B(√α_e)}(s)/ζ_B(s) has:

* degree 2 and conductor 241·N(𝔣_e);
* gamma factor Γ_R(s+a₁)Γ_R(s+a₂), with a_v=1 exactly when α_e<0 at v
  (63 of type Γ_R(s)², 128 mixed, 64 of type Γ_R(s+1)²);
* root number 1, as a quotient of Dedekind zeta functions.

Conductors, gamma types and the first 400 coefficients were checked against
PARI's independent ζ_{B(√α)}/ζ_B for 22 characters (`lcheck.gp`). The
independent analytic review extended the check to all 255 characters, with
coefficients to each row's full AFE cutoff.

Each L(301/300,χ_e) was enclosed with the manuscript's certified degree-two
AFE kernels (`nonpositive-afe.py`, unchanged). ζ_B = ζ·L(·,χ₂₄₁) was
evaluated by Hurwitz zeta in Arb (`afe241.py`):

    (1/512) log ζ_{E_B}(301/300) ∈ [0.08264460177456, 0.08264460807137].

PARI's `lfun` gives 0.0826446049229…, inside the enclosure (`yecheck.gp`).
All 255 individual values L(301/300,χ_e), computed by PARI as ζ_P/ζ_B with
`lfuncheckfeq` ≤ −125 bits, lie inside the per-row enclosures.

Refinements, all nonnegative and subtracted (`ceiling241.py`):

* the selected primes' exact tower types are finer than their E_B types:
  dyadic (4,2)→(8,4); 29: (1,2)→(1,4); (7): (1,2)→(1,4) relative. This
  subtracts 0.034453430.
* census: a prime 𝔭 with Frobenius vector v≠0 and S(v)∉R₂ has order ≥4 in
  G_B/D₃G_B, since g² ≡ S(v) mod D₃. So f≥4. Over N𝔭 ≤ 10⁶ this subtracts
  0.001629841.

  Soundness needs R₂ to be the complete quadratic relation span. It is: the
  local vectors span F₂⁸, so Ш²=0 and h²=7, and every relator of G_B has
  its initial among the 22 listed forms (§3.3–3.4).

These two refinements, about 0.036 in total, depend on the tower facts of §3:

* the complete presentation over B;
* |D|=32, with D embedded in G_B/D₃G_B;
* every K containing the fixed field of D₃G_B.

The dyadic type alone contributes 0.0338.

With ε=1/300, (ℓ−γ−log4π)/4 = 0.6369412 and R ≤ 0.0085106:

    C = 0.0487128429 (upper endpoint),   B_sel(1) = 0.0416684615,
    C − B_sel = 0.0070444.

Other tested abscissae are 1+1/1000, 1/500, 1/400, 1/200 and 1/150; all give
larger C. Of the remaining slack, about 0.005 comes from primes that split
completely in E_B, whose density is 1/256. G_B^{ab} is elementary abelian (no
Z/4 factor in L₂), so a sharper bound would need non-abelian L-functions.

## 5. Geometric margin

Propositions `geo:transfer` and `fw:transfer` need a quadratic K/F that is
unramified at finite places, has K totally imaginary and F a real place, has
uniform local types, and has the root discriminant λ. All of these hold. The
margin is computed with the manuscript's certified routines, reused unchanged:

* complex-pair profile: `mass_certificate`, `overlap_certificate` and
  `tube_certificate`, with the published Bernstein-Student witness and
  p=2/(1+δ);
* real places: the Gaussian at a_C=2pδ;
* six-shell finite windows: `local_window`, with weights re-optimized for the
  new local data (`shells241.py`). Primes 29 and 7 use truncated shells.

Results (`geom241.py`, interval lower endpoints):

| δ | J_D | μ | margin after concentration |
|---|---|---|---|
| 0.0426 | 1.35909 | 17.87 | 0.003339 |
| 0.0427 | 1.35645 | 17.87 | 0.000906 |
| 0.04273 | 1.35565 | 17.87 | 0.000176 |
| 0.0428 | 1.35380 | 17.87 | −0.001525 |

The Fourier condition (σ_D>1, log K<2log2, μ>10) holds. Because H=15.69 is
much smaller than the manuscript's H≈31.7, μ=17.87 is far smaller than the
manuscript's 26497. It is still sufficient: the sufficient condition of
`fw:fourier-condition` is σμ ≥ log M + 2log5 + 2 ≈ 5.91 here (σ=1, M=2). The δ-slope of the margin is about
−24, against −40 for the manuscript, for the same reason.

## 6. What the transfer to B assumes, to be reviewed

1. The manuscript's tower-section arguments (Fox blocks, filtered local
   freeness, shared-row subtraction, finite quotients) hold over B with
   8 generators. The complete-presentation input over B is §3.3.
2. The infinite pro-2 group gives Galois K/B of every sufficiently large
   2-power degree retaining G_B/D₄G_B. This is the same argument as over Q.
3. The analytic section holds for K Galois over B rather than over Q (§4.1).
   In particular the TV basic inequality is applied to the family {K}, and R
   is replaced by its per-prime-of-B version.
4. The AFE module's hypotheses: entire L-function, stated conductor and
   gamma factors, root number 1, and |a_n| ≤ d(n).
5. The geometric propositions use only the quadratic extension K/F and its
   local data, not a Galois structure over Q.

## 7. Reproduction

From `certificates/` (Python ≥3.11, mpmath 1.3.0, python-flint 0.9.0, PARI/GP,
a C compiler; set PYLIB if the Python packages are not installed):

```sh
gp -q < kummer241.gp          # Kummer basis and local vectors
gp -q < cup241.gp             # cup-product invariants (rank 7)
python3 lie241.py; python3 lie241c.py   # layers L2, L3, retention, ad(c1)
python3 gs241.py              # P_B(34/117) < 0
python3 lfun241.py            # 255 L-function data rows (lrows241.json)
gp -q < lcheck.gp             # conductor/gamma/coefficient checks vs PARI
python3 afe241.py 301/300     # rigorous (1/512) log zeta_{E_B}
python3 ceiling241.py afe241_301_300.json   # C = 0.04871285
python3 geom241.py 0.04273 0.04871285 shells241_0.04273.json
gcc -O2 -fopenmp -o census241 census241.c -lm && ./census241 1e9 8   # census statistics
```
