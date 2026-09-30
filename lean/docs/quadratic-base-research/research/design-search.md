# Design search: what was tried, and why Q(√241)

Date: 2026-09-29. This records the exploratory model and its conclusions,
including negative results. The model is a comparison tool, not a
certificate; the certified numbers for the chosen design are in
[construction.md](construction.md).

## 1. The model

`design-model/` contains a floating-point margin and Golod–Shafarevich model.

* **Margin** (`model.py`): the manuscript's
  M(θ) = J−δH−(1/2−δ)ℓ−C+(1−δ)log2+(1−θ)logπ+(1−2θ)J_C+θJ_D, with the
  six-shell finite functional of `sections/finite-windows.tex`. Gaussian J_C
  and J_R are computed exactly. J_D is the Gaussian value plus the published
  profile's gain (0.0119).
* **Calibration**: with the published data the model gives margin
  5.336e-6 at δ=0.0418235, matching the certificate. Its finite sum
  1.0335669225 matches the certificate to all printed digits.
* **Towers** (`design.py`, `optimize.py`, `fastopt.py`, `quadbase.py`): the
  manuscript's block costs c₁,c₂,c₂₄,c₄,d_D,s_D, and uncapped ramified primes
  with inertia C₂ (cost 2t²/(1+t)). A multiple-choice knapsack is solved by
  exact DP over discretized cost, then δ is found by bisection.
* **Model check**: over Q the optimizer returns exactly the published design
  (Σ={2,3,5,7,11,13} with types 22/24, C₄ caps at 17–31, t≈0.32) as its
  optimum, at δ=0.041713 with hard windows.

## 2. Split-real places: a large geometric gain that does not pay

If F has real places that *split* in K (K real there), the norm-one torus has
a noncompact hyperbola factor (x,1/x) at each such place: one unit direction
per degree of F, rather than one per complex place (two degrees). Redoing
Proposition `geo:mass`, the per-degree archimedean contribution is log2+J_R,
with J_R = log(p/2)−δlogπ+max_z[δlog(pz)+logK₀(z)] for a Gaussian. At
δ=0.0418235 (`model.py`):

| place type of F | per-degree contribution |
|---|---|
| split real (new) | 2.8107 |
| complex (current) | 1.9263 |
| nonsplit real | 1.6017 |

The gain is +0.884 per degree. However, real places of F in a pro-2 tower
require killing complex conjugations: a degree-one relation of cost t in place
of c₁ = t²/(1+t). This holds over Q, and linearly in the real fraction over
any base, via the weighted Schreier scaling P_U ≤ [G:U]·P_G. At the model's
shadow price of Golod–Shafarevich budget the cost exceeds the gain. The
optimizer gives δ = 0.0397 with all places split-real and 0.0404 with half,
against 0.0417 for the current signature. Record totally real towers
(rd ≈ 913) against totally complex ones (rd ≈ 82) show the same size of cost.
Odd-p towers make total reality free but have far costlier generators (tame
ramification needs N𝔮≡1 mod p, with e=p). **Conclusion: not profitable in
Golod–Shafarevich towers.**

## 3. Other variations over Q (all break-even or worse in the model)

* f=1 caps at primes with zero genus vector cost t²; the smallest such prime
  is 8089, with margin/cost ratio 3.3, at the shadow price.
* Batching an f=2 cap with a known involution of equal genus vector (cost
  ≈t³): the first eligible primes are 467 and above, ratio ≤3.
* Dyadic alternatives (e=4 local fields, uncapped Frobenius) and e=4 tame
  inertia at 3 or 5: all lose.

## 4. Amortization over a base field (the useful idea)

Over a totally real base B of degree m in which every design prime splits,
P_B = m·P_Q − (m−1)(1−s_D) (derivation in construction.md §2). If the base
were free, the optimizer gives δ ≥ 0.06. The obstacle is rd(B): fields where
many small primes split completely have large root discriminants.

* **Real quadratic bases** (2 split, D≡1 mod 8; inert primes of B modelled
  with halved generators, and caps at the Frobenius of B; `quadbase.py`).
  74 of the 108 squarefree D ≤ 2600 with 3 split were evaluated before the
  scan was stopped. D=241 gives δ_model=0.042818, far ahead of all the
  others: next are D=97 (0.041614), 1009 (0.041528), 337 (0.041524),
  1129 and 1201. All of those are below the current exponent in the model. Q(√241)
  is the smallest real quadratic field in which 2, 3 and 5 all split.
* **Bases with 2 ramified** (for example Q(√19), Q(√34)) would cost less root
  discriminant, but the dyadic prime has a 4-generator local group mapping to
  an order-16 image, which forces an extra degree-one relation. Not
  profitable in the model.
* **Cubic bases**: the smallest totally real cubic with 2, 3, 5 all split
  completely has discriminant 413449 (rd 74.5), a search of all S3/C3 cubics
  to 3·10⁶. None has 2, 3, 5, 7, 11, 13 split completely below 1.6·10⁷.
  Too costly.
* **Quartic bases**: no totally real quartic field (V4, C4, D4, A4, S4) with
  2, 3 and 5 all split completely has discriminant ≤ 2.25·10⁶ (rd ≤ 38.7).
  The search was stopped there. A quartic base would need rd(B) of roughly
  40 or less to compete, because the amortization gain is bounded by about
  0.7 Golod–Shafarevich units.

## 5. Analytic ceilings for the Q(√241) design

The margin slope is only about −24 per unit δ here, so analytic slack is
expensive.

* **Census + TV budget only** (`census241.c`): C − B_sel = middle + r(X)B_rem,
  with middle 0.00108 at X=10⁹ (0.00129 at 10¹⁰), and tail 0.0259 at 10⁹. This
  gives δ ≈ 0.0419, a small gain.
* **Genus-field L-functions** (construction.md §4): C − B_sel = 0.00704, giving
  δ = 0.04273.
* A paper-quality ceiling (slack ≈0.0004) would give δ ≈ 0.0430. It would need
  non-abelian L-functions: the abelianization of G_B is elementary abelian,
  so no larger abelian field is available.

## 6. Next directions

* **Golod–Shafarevich over a subfield proves more than over Q.** Viewed over
  Q, the tower of construction.md is ramified at {2,3,5,241}, and the
  manuscript's Q-level criterion fails for it: P ≈ +0.27 at t=0.29 (five
  generators, an uncapped block at 241). Over the base Q(√241) the same tower
  passes, with P_B(34/117) ≈ −0.0021. The natural arithmetic presentation over
  a subfield can therefore beat the induced one. Candidate next bases are
  larger subfields of this tower, for example quartic B(√α) with α ∈ V, in
  which more of the primes above 2, 3, 5 split. Each needs its own
  complete-presentation and block computation.
* **Non-abelian analytic ceiling.** G_B^{ab} is elementary abelian, so any
  improvement on E_B needs degree-4 L-functions. Adding one dihedral
  extension to E_B halves the density of completely split primes; that is
  about 64 AFEs with conductors up to about 10¹⁷. A paper-quality ceiling
  would give δ ≈ 0.0430.
* **Write-up.** A self-contained manuscript for the base Q(√241), and a Lean
  development over B, are not yet started.
