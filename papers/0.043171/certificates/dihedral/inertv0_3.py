#!/usr/bin/env python3
"""Center bits of the five D4 fields of W' (orbits 10, 23, 24, 19, 20) at the vector-0 primes of B that are inert over Q
(norm p^2 <= XA): inertv0.py extended to E_W'.

For such a prime P = pO_B the Frobenius in Gal(M_o/B) is 1 or the central z, and the Euler factor at p of
L(s, rho_o) = zeta(K_{o,0})/zeta(Bc_o) is (1 - p^-2s)^-2, respectively (1 + p^-2s)^-2.  The factor is computed
by PARI from the prime decompositions of p in K_{o,0} and Bc_o (twist w = 0 of ddata_orb<o>.json).  Writes
inertv0_3.json: {p: {o: bit}}, and asserts bit_24 = bit_10 + bit_23 and bit_20 = bit_10 + bit_19.
"""
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent.parent.parent / "0.04273/certificates"))
from census241 import legendre, NORMS  # noqa: E402

XA = 12 * 10**6


def inert_v0_primes():
    out = []
    for p in range(7, int(XA**0.5) + 1):
        if all(p % q for q in range(2, int(p**0.5) + 1)) and p not in (29,) and legendre(241, p) == -1:
            if all(legendre(nm, p) == 1 for nm in NORMS):
                out.append(p)
    return out


def main():
    ps = inert_v0_primes()
    res = {p: {} for p in ps}
    for o in (10, 23, 24, 19, 20):
        d = json.loads((HERE / f"ddata_orb{o}.json").read_text())
        tw = d["twists"][0]
        assert tw["w"] == [0] * 8
        gp = (f'K = nfinit({tw["K"]}); Bc = nfinit(subst({d["PBc"]}, y, x));\n'
              'zl(nf, p) = prod(i = 1, #idealprimedec(nf, p), 1 - X^(idealprimedec(nf, p)[i].f));\n'
              + "".join(f'print({p}, " ", Vec(zl(K, {p}) / zl(Bc, {p}) + O(X^5)));\n' for p in ps))
        out = subprocess.run(["gp", "-q", "-s", "2000000000"], input=gp, capture_output=True, text=True).stdout
        for line in out.strip().splitlines():
            p, vec = line.split(" ", 1)
            v = [int(x) for x in vec.strip("[]").split(",")]
            if v == [1, 0, -2, 0, 1]:
                res[int(p)][o] = 0        # (1 - X^2)^2: Frobenius 1 in Gal(M_o/B)
            elif v == [1, 0, 2, 0, 1]:
                res[int(p)][o] = 1        # (1 + X^2)^2: Frobenius z
            else:
                raise AssertionError((o, p, v))
    for p in ps:
        assert res[p][24] == res[p][10] ^ res[p][23] and res[p][20] == res[p][10] ^ res[p][19], p
    (HERE / "inertv0_3.json").write_text(json.dumps({str(p): {str(o): b for o, b in r.items()} for p, r in res.items()}, indent=1) + "\n")
    off = [p for p in ps if res[p][10] or res[p][23] or res[p][19]]
    print(f"inertv0: {len(ps)} inert vector-0 primes with p^2 <= {XA}: {ps}; Frobenius off ker W' at {len(off)}; in ker W' at {[p for p in ps if p not in off]}")


if __name__ == "__main__":
    main()
