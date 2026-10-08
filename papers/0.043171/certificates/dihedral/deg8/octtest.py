#!/usr/bin/env python3
"""End-to-end test of the degree-8 L-functions at s = 19/10, where the Euler product converges absolutely: the AFE
value (gkernel 'octic', octcoef.c moments, conductor and root number 1 from export8.gp) must agree with

    log L(19/10) = sum_{p <= PSMALL} -log P_p(p^-1.9)            (PARI Euler factors)
                 + sum over central sides P of q in (PSMALL, N_max]: -4 log(1 - sign(P) q^-1.9)   (octcoef.c)
                 + O(eta),  eta = 2.01 * 2 * PSMALL^-2.8 / 2.8 (non-central and inert q: factors (1 -+ q^-3.8)^-2)
                          + 8.1 * 1.25506 * 1.9 N_max^-0.9 / (0.9 log N_max)          (q > N_max, |a_q| <= 8)
A disagreement would expose a wrong conductor, gamma factor, root number or coefficient rule.
Usage: octtest.py MOMENTS META EXPORT_JSON
"""
import json
import math
import sys
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import gkernel as GK  # noqa: E402
import leval as LE  # noqa: E402
from flint import arb, ctx  # noqa: E402


def main(momf, metaf, export):
    ctx.prec = 256
    s = Q(19, 10)
    mom = LE.read_moments(momf)
    meta = json.loads(Path(metaf).read_text())
    ex = json.loads(Path(export).read_text())
    assert mom["eul"] is not None and not mom["exc"]
    PS, NMAX = meta["PSMALL"], meta["NMAX"]
    tab = GK.HTable("octic")
    kern = GK.Kernel(tab, s)
    sA = arb(19) / 10
    eta = 2.01 * 2 * PS ** -2.8 / 2.8 + 8.1 * 1.25506 * 1.9 * NMAX ** -0.9 / (0.9 * math.log(NMAX))
    worst = 0.0
    for k, tw in enumerate(meta["twists"]):
        G = meta["groups"][tw["group"]]
        du = (LE.eps_t(G["t"], GK.TYPES["octic"]["kappa"], tw["Q"]) + 2 * LE.U) * (1 + 1e-9)
        balls, absums = LE.moment_balls(mom["tw"][k]["cells"], tab.pts, mom["D"], mom["nth"], du)
        logE = LE.logE_octic(ex["twists"][k], PS, NMAX, mom["tw"][k]["rk"], mom["exc"])
        L_afe = GK.evaluate_moments(kern, tw["Q"], balls, absums, G["N"], logE, LE.BETAS8)
        lg = arb(0)
        for p in sorted(int(q) for q in ex["twists"][k]["small"] if int(q) <= PS):
            P = ex["twists"][k]["small"][str(p)]
            x = arb(p) ** (-sA)
            lg += -(sum((c * x ** j for j, c in enumerate(P)), arb(0))).log()
        lg += arb(mom["eul"][k]) + arb(0, abs(mom["eul"][k]) * 1e-12 + 1e-15 + eta)
        L_eul = lg.exp()
        rel = float(abs(L_afe.mid() - L_eul.mid()) / L_eul.mid())
        worst = max(worst, rel)
        ok = L_afe.overlaps(L_eul)
        print(f"twist {k:2d} w {tw['w']} Q {tw['Q']:.3e}: AFE {L_afe.str(14, radius=False)} (rad {float(L_afe.rad()):.1e})"
              f"  Euler {L_eul.str(14, radius=False)} (rad {float(L_eul.rad()):.1e})  rel diff {rel:.2e}  {'OK' if ok else 'DISAGREE'}")
        assert ok
    print(f"octtest: all 16 twists agree at s = 19/10; max relative difference of midpoints {worst:.2e}")


if __name__ == "__main__":
    main(*sys.argv[1:])
