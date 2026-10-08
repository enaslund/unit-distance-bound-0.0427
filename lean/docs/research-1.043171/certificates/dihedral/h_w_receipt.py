"""h_w_receipt.py [X]: a certified upper bound for the left side of the hypothesis H_W of the Lean theorem.

H_W concerns the field E_W = E(sqrt beta_o, o in {24, 20, 17, 7}) of degree 8192, the compositum of the genus
field E (degree 512) and the D4 fields of the space W'' = span(psi_10, psi_23, psi_19, psi_17) (README Section 11c; manuscript Section 5);
the four forms 24, 20, 17, 7 span the same space. With sigma = 4412/4411 and
ell = (9/4) log 2 + (1/2) log 3615 (the root discriminant of the tower), the left side is

    LHS = log zeta_{E_W}(sigma)/8192 + (sigma - 1) ((ell - gamma - log 4 pi)/4 + D_W),
    D_W = -zeta'_{E_W}/zeta_{E_W}(2)/8192.

* log zeta_{E_W}(sigma)/8192 is Y_W'' of dihedral_ceiling3.py (space W4x): Y_E/16 plus the certified logarithms of
  the 7*64 degree-4 and 8*16 degree-8 L-values at sigma (README Lemma 4'', manuscript Lemma dh:EW, and the zeta factorization).
* D_W = sum over primes P of B of log N(P) / (2 e (N(P)^(2f) - 1)), with (e, f) the ramification index and residue
  degree of P in E_W/B (the [E_W:B]/(e f) primes above P have norm N(P)^f, and [E_W:Q] = 2 [E_W:B]). Each term
  decreases in e and f, so lower bounds for (e, f) give an upper bound:
  - above 2, 3, 5 the types of E (dyadic (4,2), and (2,2) at 3 and 5), since E is contained in E_W;
  - at an unramified P of Frobenius vector v != 0 the exact degree f = fW(v) in {2, 4} (README Lemma 4'': f = 4 iff
    phi_1(v) = rho for one of the seven D4 forms of W''), and f >= 1 at the vector-0 primes;
  - beyond X (default 10^6) the bound sum_{n > X} log n/(n^2 - 1) <= (1 + 2/X^2)(log X + 1)/X for the primes above
    n (at most two of norm n, or one of norm n^2).
Writes h_w_receipt.json.
"""
import json
import math
import sys
from fractions import Fraction as Q
from pathlib import Path

from flint import arb, ctx

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
import contextlib  # noqa: E402
import io  # noqa: E402

with contextlib.redirect_stdout(io.StringIO()):
    import dihedral_ceiling3 as DC3  # noqa: E402
    import adaptive41 as A  # noqa: E402

ctx.prec = 256
SIGMA = Q(4412, 4411)
FORMS = (24, 20, 17, 7)


def y_w():
    DC3.SPACE = DC3.SPACES["W4x"]
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        DC3.main(Q("0.04316"), SIGMA, str(HERE / "hp" / "afe241hp_4412_4411.json"), str(HERE / "hp"),
                 str(HERE / "hp3"), [])
    return DC3.main.components["Y_W"]


def d_w(X):
    allf = json.loads((HERE / "d4all27.json").read_text())["fields"]
    fams = [allf[o] for o in DC3.SPACES["W4x"]["orbits"]]

    def fW(c):
        return 4 if any(DC3.phi1(c, f) == f["rho"] for f in fams) else 2

    def term(N, e, f):
        return arb(N).log() / (2 * e * (arb(N) ** (2 * f) - 1))

    tot = 2 * term(2, 4, 2) + 2 * term(3, 2, 2) + 2 * term(5, 2, 2)
    s = A.sieve(X)
    counts = {"f1_vector0": 0, "f2": 0, "f4": 0}
    for p in range(7, X + 1):
        if not s[p]:
            continue
        if p == 241:
            c = sum((1 << i) for i, (aa, b, den) in enumerate(A.KB)
                    if A.legendre((aa * pow(den, -1, p)) % p, p) == -1)
            prs = [(p, c)]
        elif A.legendre(241, p) == 1:
            r = A.sqrtmod(241, p)
            prs = [(p, A.code_at(p, rr)) for rr in (r, p - r)]
        elif p * p <= X:
            prs = [(p * p, sum((1 << i) for i, nm in enumerate(A.NORMS) if A.legendre(nm, p) == -1))]
        else:
            continue          # inert p with p^2 > X: in the tail
        for N, c in prs:
            f = 1 if c == 0 else fW(c)
            counts["f1_vector0" if f == 1 else ("f2" if f == 2 else "f4")] += 1
            tot += term(N, 1, f)
    tail = (1 + arb(2) / X**2) * ((arb(X).log() + 1) / X)
    return tot + tail, counts, tail


def main(X):
    Y = y_w()
    D, counts, tail = d_w(X)
    eps = arb(SIGMA.numerator - SIGMA.denominator) / SIGMA.denominator
    ell = arb(9) / 4 * arb(2).log() + arb(3615).log() / 2
    Bhalf = (ell - arb.const_euler() - (4 * arb.pi()).log()) / 4
    lhs = Y + eps * (Bhalf + D)
    rec = {"sigma": str(SIGMA), "forms": list(FORMS), "X": X,
           "normalized_log_zeta_EW_sigma": [str(Y.lower()), str(Y.upper())],
           "D_W_upper": str(D.upper()), "D_W_tail": str(tail.upper()), "prime_counts_upto_X": counts,
           "Bhalf": str(Bhalf), "LHS_upper": str(lhs.upper())}
    # fail closed: the complete enclosure must lie strictly below the threshold X_W of the Lean hypothesis
    threshold = arb(50969) / 1000000
    assert lhs < threshold, ("H_W not certified", str(lhs), str(threshold))
    rec["threshold"] = "50969/1000000"
    rec["check"] = "PASS the complete Arb enclosure of the left side is below 50969/1000000"
    (HERE / "h_w_receipt.json").write_text(json.dumps(rec, indent=1) + "\n")
    print(json.dumps(rec, indent=1))


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 10**6)
