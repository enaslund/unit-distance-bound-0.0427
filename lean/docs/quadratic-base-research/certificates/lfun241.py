"""Data for the 255 nontrivial quadratic Hecke characters chi_e of B=Q(sqrt 241) cut out by the Kummer group V.

chi_e corresponds to alpha_e = prod alpha_i^{e_i} (e in F2^8).  As an L-function over Q:
  degree 2, conductor 241 * N(f_e), gamma factor gamma_R(s+a1) gamma_R(s+a2) with a_v = [alpha_e < 0 at v],
  root number 1 (quotient of Dedekind zeta functions), coefficients from the Euler product.
"""
import json
import math
import sys
from census241 import KB, NORMS, primes_upto, legendre, sqrtmod

D = 241
VEC = json.load(open("vectors241.json")) if False else None
# local vectors from kummer241.gp (Hilbert symbols); bit i <-> Kummer basis element i
L = {
    "c1": [1, 0, 1, 1, 1, 0, 1, 0], "c2": [1, 1, 0, 0, 0, 1, 0, 1],
    "x1": [0, 0, 1, 0, 0, 0, 0, 0], "y1": [1, 1, 1, 1, 0, 0, 1, 0], "z1": [1, 0, 0, 0, 0, 1, 0, 0],
    "x2": [0, 0, 0, 1, 0, 0, 0, 0], "y2": [1, 0, 0, 0, 0, 0, 0, 1], "z2": [1, 1, 1, 1, 1, 0, 0, 0],
    "t31": [0, 0, 0, 0, 1, 0, 0, 0], "p31": [1, 0, 1, 0, 0, 1, 1, 1],
    "t32": [0, 0, 0, 0, 0, 1, 0, 0], "p32": [1, 1, 1, 0, 1, 0, 1, 1],
    "t51": [0, 0, 0, 0, 0, 0, 1, 0], "p51": [0, 1, 1, 0, 0, 1, 0, 1],
    "t52": [0, 0, 0, 0, 0, 0, 0, 1], "p52": [0, 1, 0, 1, 1, 0, 1, 0],
}


def code(v):
    return sum(b << i for i, b in enumerate(v))


LC = {k: code(v) for k, v in L.items()}


def dot(a, b):
    return bin(a & b).count("1") & 1


def local_small(e):
    """Euler data at the primes above 2,3,5: list of (p, chi or 0) and conductor norm."""
    out = []
    cond = 1
    for j in "12":  # dyadic primes (norm 2)
        xe, ye, ze = dot(LC["x" + j], e), dot(LC["y" + j], e), dot(LC["z" + j], e)
        if xe:
            cond *= 2**3
            out.append((2, 0))
        elif ye:
            cond *= 2**2
            out.append((2, 0))
        else:
            out.append((2, -1 if ze else 1))
    for p, pre in [(3, "3"), (5, "5")]:
        for j in "12":
            if dot(LC["t" + pre + j], e):
                cond *= p
                out.append((p, 0))
            else:
                out.append((p, -1 if dot(LC["p" + pre + j], e) else 1))
    return out, cond


def frob_vectors(nmax):
    """Frobenius vectors (codes) of primes of B with norm <= nmax, excluding primes above 2,3,5.
    Returns list of (p, 'split'|'inert'|'ram', [codes])."""
    res = []
    for p in primes_upto(nmax):
        if p in (2, 3, 5):
            continue
        if p == D:
            c = 0
            for i, (a, b, den) in enumerate(KB):
                x = (a * pow(den, -1, p)) % p
                if legendre(x, p) == -1:
                    c |= 1 << i
            res.append((p, "ram", [c]))
        elif legendre(D, p) == 1:
            r = sqrtmod(D, p)
            cs = []
            for rr in (r, p - r):
                c = 0
                for i, (a, b, den) in enumerate(KB):
                    x = ((a + b * rr) * pow(den, -1, p)) % p
                    if legendre(x, p) == -1:
                        c |= 1 << i
                cs.append(c)
            res.append((p, "split", cs))
        else:
            c = 0
            for i, nm in enumerate(NORMS):
                if legendre(nm, p) == -1:
                    c |= 1 << i
            res.append((p, "inert", [c]))
    return res


def kind_of(e):
    s1, s2 = dot(LC["c1"], e), dot(LC["c2"], e)
    if s1 == 0 and s2 == 0:
        return "pure0"
    if s1 == 1 and s2 == 1:
        return "pure1"
    return "quadratic"


def coefficients(e, nmax, fv):
    """Dirichlet coefficients a_n (n<=nmax) of L(s, chi_e) from the Euler product."""
    a = [0] * (nmax + 1)
    a[1] = 1
    local = {}
    small, _ = local_small(e)
    for p, chi in small:
        local.setdefault(p, []).append(("lin", chi))
    for p, typ, cs in fv:
        if typ == "split":
            local[p] = [("lin", -1 if dot(c, e) else 1) for c in cs]
        elif typ == "ram":
            local[p] = [("lin", -1 if dot(cs[0], e) else 1)]
        else:
            local[p] = [("quad", -1 if dot(cs[0], e) else 1)]
    for p in sorted(local):
        # power series of prod (1 - chi T)^-1 or (1 - chi T^2)^-1 in T = p^-s
        kmax = 0
        q = p
        while q <= nmax:
            kmax += 1
            q *= p
        ser = [1] + [0] * kmax
        for typ, chi in local[p]:
            if chi == 0:
                continue
            step = 1 if typ == "lin" else 2
            new = ser[:]
            for k in range(step, kmax + 1):
                new[k] += chi * new[k - step]
            ser = new
        # multiply into a (multiplicative extension over coprime parts)
        for n in range(nmax, 0, -1):
            if a[n] == 0 or n % p == 0:
                continue
            q = p
            k = 1
            while n * q <= nmax:
                a[n * q] += a[n] * ser[k]
                q *= p
                k += 1
    return a


if __name__ == "__main__":
    mult = 4
    _, cmax = max((local_small(e) for e in range(1, 256)), key=lambda t: t[1])
    nmax_all = int(mult * math.isqrt(D * cmax)) + 2
    fv = frob_vectors(nmax_all)
    rows = []
    for e in range(1, 256):
        _, cond = local_small(e)
        q = D * cond
        nmax = int(mult * math.isqrt(q)) + 1
        a = coefficients(e, nmax, fv)
        rows.append({"label": f"e={e}", "kind": kind_of(e), "conductor": q, "N": nmax, "coefficients": a})
    kinds = {}
    for r in rows:
        kinds[r["kind"]] = kinds.get(r["kind"], 0) + 1
    print("kinds", kinds, "max conductor", max(r["conductor"] for r in rows), "max N", max(r["N"] for r in rows))
    json.dump({"rows": rows}, open("lrows241.json", "w"))
