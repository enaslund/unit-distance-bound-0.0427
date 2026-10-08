"""Generate Lean polynomial definitions and linear_combination proofs for the four D4 radicands of E_W."""
import sys, time
from fractions import Fraction as Fr
import sympy as sp

s, x, y = sp.symbols("s x y")
RA = [Fr(-1), Fr(-71011068), Fr(-6101, 2), Fr(6101, 2), Fr(31), Fr(31), Fr(326), Fr(326)]
RB = [Fr(0), Fr(4574225), Fr(-393, 2), Fr(-393, 2), Fr(-2), Fr(2), Fr(-21), Fr(21)]
FORMS = {   # orbit: (r1, r2, rho, beta, u10, u01, u11)
 24: ([0,1,0,1,1,1,1,1], [1,0,0,1,1,0,0,0], (0,1),
      [-13151840112, 847184400, 0, 0, 0, 0, -31727062200, -2043719736],
      ["0","0","-1321960925/24","-85154989/24","-1955293/24","-125765/24","0","0"],
      ["0","0","-1321960925/24","-85154989/24","-1955293/24","-125765/24","0","0"],
      ["-1","0","0","0","0","0","0","0"]),
 20: ([0,1,0,0,1,1,0,0], [1,0,0,1,0,0,0,1], (1,1),
      [-1118796, 72068, -164, -4, -76752, 4944, 240, 16],
      ["519/8","-33/8","-7995/8","-515/8","75/8","-5/8","-26003/8","-1675/8"],
      ["-7/2","3/2","261039/2","16815/2","39/2","3/2","564785/2","36381/2"],
      ["345/8","-15/8","1112571/8","71667/8","165/8","5/8","2407163/8","155059/8"]),
 17: ([0,1,0,0,0,1,1,0], [1,0,0,0,1,0,0,0], (1,1),
      [-156, 10, -3850, -248, 0, 0, 0, 0],
      ["0","0","0","0","4/3","1/6","-119443/6","-3847/3"],
      ["-1","0","0","0","0","0","0","0"],
      ["0","0","0","0","4/3","1/6","-119443/6","-3847/3"]),
 7: ([0,0,0,0,1,0,1,0], [1,1,0,0,0,1,0,0], (1,1),
      [-130434, 8402, -646, 42, 0, 0, 0, 0],
      ["0","0","0","0","-198787/6","-12805/6","10326355/6","665179/6"],
      ["-1","0","0","0","0","0","0","0"],
      ["0","0","0","0","-198787/6","-12805/6","10326355/6","665179/6"]),
}
MON = [1, s, x, s*x, y, s*y, x*y, s*x*y]

def radprod(r):
    a = sp.Integer(1)
    for k in range(8):
        if r[k]:
            a = sp.expand(a * (sp.Rational(RA[k].numerator, RA[k].denominator) + sp.Rational(RB[k].numerator, RB[k].denominator) * s))
    a = sp.Poly(a, s)
    # reduce mod s^2 - 241
    q, rmd = sp.div(a, sp.Poly(s**2 - 241, s))
    c = rmd.all_coeffs()
    c = [0] * (2 - len(c)) + c
    return sp.Rational(c[1]), sp.Rational(c[0])          # A0, A1

def poly(coefs):
    return sum(sp.Rational(c) * m for c, m in zip(coefs, MON))

def lean(e):
    t = sp.sstr(sp.expand(e), order="lex")
    return t.replace("**", "^")

def reduce_check(f, G):
    if sp.expand(f) == 0:
        return [sp.Integer(0)] * 3
    Q, r = sp.reduced(sp.expand(f), G, x, y, s, order="lex")
    Q = list(Q) + [sp.Integer(0)] * (3 - len(Q))
    assert sp.expand(r) == 0, r
    return Q

def bil(rho, a, b):
    if rho == (1, 1): return (a[0]*b[1]) % 2
    if rho == (0, 1): return (a[0]*b[1] + a[1]*b[1]) % 2
    return (a[0]*b[0] + a[0]*b[1]) % 2

out = []
summary = []
X = [(1,0), (0,1), (1,1)]
for o, (r1, r2, rho, bc, u10, u01, u11) in FORMS.items():
    A0, A1 = radprod(r1); B0, B1 = radprod(r2)
    G = [s**2 - 241, x**2 - (A0 + A1*s), y**2 - (B0 + B1*s)]
    hyp = f"(hs : s ^ 2 = 241) (hx : x ^ 2 = {lean(A0 + A1*s)}) (hy : y ^ 2 = {lean(B0 + B1*s)})"
    beta = poly(bc); U = {X[0]: poly(u10), X[1]: poly(u01), X[2]: poly(u11), (0,0): sp.Integer(1)}
    def sig(k, e):
        return e.subs({x: (-1)**k[0]*x, y: (-1)**k[1]*y}, simultaneous=True)
    out.append(f"\n/-! ### Form {o}: `a = {lean(A0 + A1*s)}`, `b = {lean(B0 + B1*s)}`, rotation class {rho} -/\n")
    out.append(f"/-- The radicand `β_{o}` in the basis `1, s, x, s x, y, s y, x y, s x y`. -/")
    out.append(f"def beta{o} {{R : Type*}} [CommRing R] (s x y : R) : R :=\n  {lean(beta)}\n")
    out.append(f"theorem beta{o}_map {{R S : Type*}} [CommRing R] [CommRing S] (f : R →+* S) (s x y : R) :\n"
               f"    f (beta{o} s x y) = beta{o} (f s) (f x) (f y) := by\n  simp only [beta{o}, map_add, map_sub, map_mul, map_neg, map_ofNat, map_one, map_zero]\n")
    for k, nm in zip(X, ("10", "01", "11")):
        out.append(f"/-- `u_{nm}` with `σ_{nm}(β_{o}) = u_{nm}^2 β_{o}`. -/")
        out.append(f"def u{o}_{nm} {{R : Type*}} [Field R] (s x y : R) : R :=\n  {lean(U[k])}\n")
        out.append(f"theorem u{o}_{nm}_map {{R S : Type*}} [Field R] [Field S] (f : R →+* S) (s x y : R) :\n"
                   f"    f (u{o}_{nm} s x y) = u{o}_{nm} (f s) (f x) (f y) := by\n  simp only [u{o}_{nm}, map_add, map_sub, map_mul, map_div₀, map_neg, map_ofNat, map_one, map_zero]\n")
    names = {(1,0): "10", (0,1): "01", (1,1): "11"}
    for k in X:
        f = sig(k, beta) - U[k]**2 * beta
        Q = reduce_check(f, G)
        sx = "-x" if k[0] else "x"; sy = "-y" if k[1] else "y"
        out.append(f"theorem beta{o}_sigma_{names[k]} {{R : Type*}} [Field R] [CharZero R] (s x y : R)\n    {hyp} :\n"
                   f"    beta{o} s ({sx}) ({sy}) = u{o}_{names[k]} s x y ^ 2 * beta{o} s x y := by\n"
                   f"  simp only [beta{o}, u{o}_10, u{o}_01, u{o}_11]\n"
                   f"  linear_combination ({lean(Q[0])}) * hs + ({lean(Q[1])}) * hx + ({lean(Q[2])}) * hy\n")
    for k in X:
        for l in X:
            kl = ((k[0]+l[0]) % 2, (k[1]+l[1]) % 2)
            sign = (-1)**bil(rho, k, l)
            f = sig(k, U[l]) * U[k] - sign * U[kl]
            Q = reduce_check(f, G)
            sx = "-x" if k[0] else "x"; sy = "-y" if k[1] else "y"
            rhs = (("" if sign == 1 else "-") + (f"u{o}_{names[kl]} s x y" if kl != (0,0) else "1"))
            out.append(f"theorem u{o}_cocycle_{names[k]}_{names[l]} {{R : Type*}} [Field R] [CharZero R] (s x y : R)\n    {hyp} :\n"
                       f"    u{o}_{names[l]} s ({sx}) ({sy}) * u{o}_{names[k]} s x y = {rhs} := by\n"
                       f"  simp only [u{o}_10, u{o}_01, u{o}_11]\n"
                       f"  linear_combination ({lean(Q[0])}) * hs + ({lean(Q[1])}) * hx + ({lean(Q[2])}) * hy\n")
    # norm identity
    if o == 20:
        nB = sp.expand(beta * sig((1,0), beta) * sig((0,1), beta) * sig((1,1), beta))
        cof = [sig((1,0), beta), sig((0,1), beta), sig((1,1), beta)]
    else:
        k = (1,0)
        nB = sp.expand(beta * sig(k, beta)); cof = [sig(k, beta)]
    Qn, nr = sp.reduced(nB, G, x, y, s, order="lex")
    nr = sp.Poly(sp.expand(nr), s, x, y)
    n0 = nr.coeff_monomial(1); n1 = nr.coeff_monomial(s)
    assert sp.expand(nr.as_expr() - n0 - n1*s) == 0, nr
    m = sp.expand((n0 + n1*s) * (n0 - n1*s)).subs(s**2, 241)
    m = sp.expand(sp.expand((n0 + n1*s) * (n0 - n1*s)))
    m = sp.reduced(m, [s**2 - 241], s)[1]
    assert m.is_Integer, m
    Xpoly = sp.Mul(*cof) * (n0 - n1*s)
    f = beta * Xpoly - m
    Q = reduce_check(f, G)
    xname = f"normCofactor{o}"
    mk_m, mk_n = n0 + n1, -2 * n1
    assert sp.Rational(mk_m).q == 1 and sp.Rational(mk_n).q == 1, (mk_m, mk_n)
    out.append(f"/-- The conjugate factor of the norm of `β_{o}` (integer coefficients). -/")
    out.append(f"def normConj{o} {{R : Type*}} [CommRing R] (s x y : R) : R :=\n  " +
               " * ".join(f"({lean(c)})" for c in cof) + "\n")
    out.append(f"theorem normConj{o}_map {{R S : Type*}} [CommRing R] [CommRing S] (f : R →+* S) (s x y : R) :\n"
               f"    f (normConj{o} s x y) = normConj{o} (f s) (f x) (f y) := by\n"
               f"  simp only [normConj{o}, map_add, map_sub, map_mul, map_neg, map_ofNat, map_one, map_zero]\n")
    out.append(f"/-- `n̄ = {lean(n0 - n1*s)} = mk {mk_m} {mk_n}` in `ℤ[ω]`, `ω = (1 + s)/2`. -/")
    out.append(f"def normBarMk{o} : ℤ × ℤ := ({mk_m}, {mk_n})\n")
    out.append(f"theorem normBar{o}_eq {{R : Type*}} [Field R] [CharZero R] (s : R) :\n"
               f"    (({mk_m} : ℤ) : R) + (({mk_n} : ℤ) : R) * ((1 + s) / 2) = {lean(n0 - n1*s)} := by\n  push_cast\n  ring\n")
    out.append(f"/-- The cofactor with `β_{o} · normCofactor{o} = {m}` (`= {sp.factorint(m)}`). -/")
    out.append(f"def {xname} {{R : Type*}} [Field R] (s x y : R) : R :=\n  normConj{o} s x y * ({lean(n0 - n1*s)})\n")
    out.append(f"theorem beta{o}_mul_normCofactor {{R : Type*}} [Field R] [CharZero R] (s x y : R)\n    {hyp} :\n"
               f"    beta{o} s x y * {xname} s x y = {m} := by\n"
               f"  simp only [beta{o}, {xname}, normConj{o}]\n"
               f"  linear_combination ({lean(Q[0])}) * hs + ({lean(Q[1])}) * hx + ({lean(Q[2])}) * hy\n")
    summary.append((o, (A0, A1), (B0, B1), m, sp.factorint(m)))

hdr = '''module

public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Int.Cast.Lemmas

@[expose] public section
set_option backward.privateInPublic true

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Polynomial identities for the four D4 radicands of `E_W`

Generated by `scripts/sqrt241/generate_wide_identities.py` — do not edit by hand.

For each of the D4 forms `24, 20, 17, 7` of the space `W''` (papers/0.043171, Sections 4, 11c), with
`s² = 241`, `x² = a`, `y² = b` (`a`, `b` the products of Kummer radicands of the rows `r₁`, `r₂`):

* `betaO s x y` is the radicand `β_O` of the D4 field `B(√a, √b, √β_O)` (integral coordinates);
* `uO_k` (`k = 10, 01, 11`) satisfy `σ_k(β_O) = u_k² β_O`, where `σ_k` changes the signs of `x`, `y`
  as indicated (`betaO_sigma_k`);
* the cocycle identities `σ_k(u_l) u_k = ± u_{k+l}`, with sign `(-1)^{b(k,l)}` for the bilinear form `b`
  of the rotation class (`uO_cocycle_k_l`);
* `βO · normCofactorO = m` with `m = ±2^i 3^j` (`betaO_mul_normCofactor`), so `β_O` is an `S`-unit.

Each identity holds in every field in which the three relations hold; the proofs are
`linear_combination` with the exact quotients of the reduction by the Gröbner basis
`s² - 241, x² - a, y² - b`.
-/

namespace UnitDistance.Sqrt241.Wide
'''
src = hdr + "\n".join(out) + "\nend UnitDistance.Sqrt241.Wide\n"
open(sys.argv[1], "w").write(src)
for t in summary: print(t)
print(len(src), "bytes")
