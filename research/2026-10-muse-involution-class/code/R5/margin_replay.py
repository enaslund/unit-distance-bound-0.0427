"""R5 margin replay at theta*_new = 1/2 - 2^-18 (N_iota >= 2^16).

Exact rational interval arithmetic (stdlib fractions) on C62's checked
enclosures at delta = 0.043172 (Gaussian profiles; R4 owns witness
recovery, not duplicated here):
  M(theta*_new) = M(theta*) + slope * 2^-18,  theta* = 65535/131072.
Cross-checks M(1/2) = M(theta*) + slope * 2^-17 against C62's table,
compares theta*_new against C62 zeros, and certifies uniform inf > 0
on [theta*_new, 1/2) per tier (affine, slope_lo > 0, both ends > 0).

Usage: .venv/bin/python research/2026-10-muse-involution-class/code/R5/margin_replay.py
"""
from fractions import Fraction as F

D = lambda s: F(s)  # exact decimal -> Fraction
theta_star = F(65535, 131072)
theta_new = F(1, 2) - F(1, 2**18)
d18 = F(1, 2**18)
d17 = F(1, 2**17)
print("theta* =", float(theta_star), " theta*_new =", float(theta_new))
assert theta_new - theta_star == d18

tiers = {
    "certified": (D("-1.32962595959847075e-05"), D("-1.32962595959484946e-05"),
                  D("-8.52982440210e-06"), D("-8.52982440206e-06")),
    "middle": (D("-1.9562595959847075e-06"), D("-1.9562595959484946e-06"),
               D("2.81017559790e-06"), D("2.81017559794e-06")),
    "estimated": (D("-6.962595959847075e-07"), D("-6.962595959484946e-07"),
                  D("4.07017559790e-06"), D("4.07017559794e-06")),
}
slope = (D("0.62474619373310090"), D("0.62474619373310098"))
print("slope_lo > 0:", slope[0] > 0)
zeros = {
    "middle": (D("0.49999550189240666"), D("0.49999550189240672")),
    "estimated": (D("0.49999348507339658"), D("0.49999348507339664")),
}
for name, (mlo, mhi, hlo, hhi) in tiers.items():
    Mnew = (mlo + slope[0] * d18, mhi + slope[1] * d18)
    Mh = (mlo + slope[0] * d17, mhi + slope[1] * d17)
    print("== %s ==" % name)
    print("  M(theta*_new) in [%.6e, %.6e]"
          % (float(Mnew[0]), float(Mnew[1])))
    print("  M(1/2) recomputed in [%.6e, %.6e] vs C62 [%.6e, %.6e] "
          "consistent: %s"
          % (float(Mh[0]), float(Mh[1]), float(hlo), float(hhi),
             Mh[0] <= hhi and hlo <= Mh[1]))
    print("  left end > 0: %s; right end > 0: %s; uniform inf > 0: %s"
          % (Mnew[0] > 0, hlo > 0, Mnew[0] > 0 and hlo > 0))
    if name in zeros:
        zlo, zhi = zeros[name]
        print("  theta*_new - zero_hi = %.3e (>0: %s)"
              % (float(theta_new - zhi), theta_new > zhi))
print("inputs: C in {0.0422764, 0.04226506, 0.0422638} (README 11c), "
      "delta=0.043172, Gaussian profiles (C62/C86)")
print("DONE")
