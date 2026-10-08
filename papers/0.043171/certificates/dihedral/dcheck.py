#!/usr/bin/env python3
"""Validation of one D4 family: (1) the coefficients of all 64 twists agree with PARI's Dirichlet series
zeta(K_w)/zeta(Bc) (dirzetak) up to NCHK; (2) for the listed twists, PARI's lfun with the same
coefficients, conductor, gamma factor and root number satisfies the functional equation (lfuncheckfeq)
and its value at SIGMA lies in the certified enclosure.  Usage: dcheck.py ORBIT NCHK [k1,k2,... [SIGMA]]"""
import json
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import dcoeffs as DC  # noqa: E402


def gp(cmd):
    return subprocess.run(["gp", "-q", "-s", "4000000000"], input=cmd, capture_output=True, text=True,
                          cwd=str(HERE)).stdout


def main(orbit, nchk, sel, sigma="301/300"):
    data = DC.load(orbit)
    p, q = sigma.split("/")
    suffix = "" if sigma == "301/300" else f"_{p}_{q}"
    afe = {r["k"]: r for r in json.loads((HERE / f"dafe_orb{orbit}{suffix}.json").read_text())}
    spf = DC.spf_sieve(10**6 - 1)
    for k, tw in enumerate(data["twists"]):
        _, _, a = DC.coefficients(data, tw, spf, M=nchk)
        out = gp(f'K = {tw["K"]}; Bc = subst({data["PBc"]}, y, x); print(dirdiv(dirzetak(nfinit(K), {nchk}), dirzetak(nfinit(Bc), {nchk})));')
        q = [int(x) for x in out.strip().strip("[]").split(",")]
        assert q[:nchk] == a[1:nchk + 1], (orbit, k)
    print(f"dcheck: orbit {orbit}: coefficients of all 64 twists agree with PARI up to {nchk}")
    for k in sel:
        tw = data["twists"][k]
        _, _, b = DC.coefficients(data, tw, spf, M=10**6 - 1)
        (HERE / f"coef_tmp_{orbit}_{k}.gp").write_text("A = [" + ",".join(map(str, b[1:])) + "];\n")
        out = gp(f'default(realprecision, 38); read("coef_tmp_{orbit}_{k}.gp"); '
                 f'L = lfuncreate([A, 0, [0,0,1,1], 1, {tw["Q"]}, 1]); print(lfuncheckfeq(L), " ", lfun(L, {sigma}));').split()
        (HERE / f"coef_tmp_{orbit}_{k}.gp").unlink()
        lo = float(afe[k]["L"][0].strip("[").split()[0])
        hi = float(afe[k]["L"][1].strip("[").split()[0])
        val = float(out[1])
        assert int(out[0]) <= -30 and lo - 1e-9 <= val <= hi + 1e-9, (k, out, lo, hi)
        print(f"dcheck: orbit {orbit} twist {k}: Q {tw['Q']} checkfeq {out[0]}, PARI L({sigma}) = {val:.12f} in [{lo:.12f}, {hi:.12f}]")


if __name__ == "__main__":
    main(int(sys.argv[1]), int(sys.argv[2]), [int(x) for x in sys.argv[3].split(",")] if len(sys.argv) > 3 else [],
         sys.argv[4] if len(sys.argv) > 4 else "301/300")
