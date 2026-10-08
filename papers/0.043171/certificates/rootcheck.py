#!/usr/bin/env python3
"""Cross-check of the D4 Legendre test against the fields themselves.

For the first and last 40 rational primes p <= 1.2e7 that split completely in E (both primes of B
above p have Frobenius vector 0), predict for each of the fifteen fields M_i the number of roots mod p
of the absolute degree-16 polynomial of M_i (mtilde15.gp, written by vd4.gp): p splits completely
in F0_i, and M_i/F0_i splits at the four primes above a prime P of B exactly when beta_i is a square
at P, so the prediction is 8 * #{P above p : beta_i square at P}.  PARI's polrootsmod must agree.
"""
import json
import subprocess
import sys
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent.parent / "0.04273/certificates"))
from census241 import legendre, sqrtmod, KB  # noqa: E402

FIELDS = json.loads((HERE / "d4fields15.json").read_text())


def bits(p, rr):
    al = [((aa + b * rr) * pow(den, -1, p)) % p for (aa, b, den) in KB]
    if any(legendre(a, p) != 1 for a in al):
        return None
    q = [sqrtmod(a, p) for a in al]
    out = []
    for f in FIELDS:
        r1 = [int(c) for c in f["rows"][0]]
        r2 = [int(c) for c in f["rows"][1]]
        sa = sb = 1
        for k in range(8):
            sa = sa * q[k] % p if r1[k] else sa
            sb = sb * q[k] % p if r2[k] else sb
        bas = [1, rr, sa, rr * sa, sb, rr * sb, sa * sb, rr * sa * sb]
        val = sum((Q(c).numerator % p) * pow(Q(c).denominator, -1, p) * b for c, b in zip(f["coords"], bas)) % p
        out.append(legendre(val, p))
    return out


def main(X=12 * 10**6):
    s = bytearray([1]) * (X + 1)
    s[0:2] = b"\x00\x00"
    for i in range(2, int(X**0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    full = []
    for p in range(7, X + 1):
        if s[p] and p % 120 in (1, 49) and legendre(241, p) == 1:
            r = sqrtmod(241, p)
            b1, b2 = bits(p, r), bits(p, p - r)
            if b1 is not None and b2 is not None:
                full.append((p, b1, b2))
    sample = full[:40] + full[-40:]
    lines = ['default(breakloop, 0);', 'read("mtilde15.gp");', 'NOK = 0;']
    for p, b1, b2 in sample:
        exp = [8 * ((x == 1) + (y == 1)) for x, y in zip(b1, b2)]
        lines.append(f'if(vector(15, i, #polrootsmod(MP[i], {p})) == {exp}, NOK++, print("MISMATCH {p}"));')
    lines.append(f'print("rootcheck ", NOK, " / {len(sample)}");')
    out = subprocess.run(["gp", "-q", "-s", "2000000000"], input="\n".join(lines) + "\n", capture_output=True,
                         text=True, cwd=str(HERE)).stdout
    print(out.strip())
    assert f"rootcheck {len(sample)} / {len(sample)}" in out
    print("rootcheck: PASS", len(sample), "primes x 15 fields")


if __name__ == "__main__":
    main()
