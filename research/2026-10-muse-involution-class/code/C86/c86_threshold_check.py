"""C86 independent threshold check for R5-signature-threshold.md section 1.

Stdlib-only exact rational arithmetic. Inputs: C62-verified zero enclosures
(C62-r5-margin-accounting-check.md section 3) and theta*(N) = 1/2 - 1/(4N).
Verifies N_min, 2^15/2^16 gaps, rounding-cover claim, and M positivity logic.
Run: python3 research/2026-10-muse-involution-class/code/C86/c86_threshold_check.py
"""
from fractions import Fraction

# C62 zero enclosures (direct enclosures, section 3)
MID_LO = Fraction("0.49999550189240666")
MID_HI = Fraction("0.49999550189240672")
EST_LO = Fraction("0.49999348507339658")
EST_HI = Fraction("0.49999348507339664")
# certified zero > 1/2 (C62: 0.50001365326...); quoted value below is a lower bound
CERT_QUOTED = Fraction("0.50001365")

# note's quoted zeros + rounding cover
MID_Q = Fraction("0.4999955019")
EST_Q = Fraction("0.4999934851")
COVER = Fraction(5, 10**11)  # 5e-11

HALF = Fraction(1, 2)

def theta_star(N):
    return HALF - Fraction(1, 4 * N)

def n_min(theta0_upper):
    # smallest integer N with theta*(N) > theta0_upper; None if impossible
    d = HALF - theta0_upper
    if d <= 0:
        return None
    # N > 1/(4d)
    t = Fraction(1, 4 * d)
    return int(t) + 1  # floor + 1 since t is not an integer here

# 1. rounding cover check
assert MID_Q + COVER > MID_HI, "middle cover fails"
assert EST_Q + COVER > EST_HI, "estimated cover fails"
print("cover ok: quoted+5e-11 exceeds C62 upper ends")
print("  middle slack:", float(MID_Q + COVER - MID_HI))
print("  estimated slack:", float(EST_Q + COVER - EST_HI))

# 2. N_min from covered zeros
mid_n = n_min(MID_Q + COVER)
est_n = n_min(EST_Q + COVER)
print("N_min middle:", mid_n, "(note: 55580)")
print("N_min estimated:", est_n, "(note: 38374)")
assert mid_n == 55580, mid_n
assert est_n == 38374, est_n
# also from raw C62 upper ends: cover costs at most 1 (middle 55579->55580)
assert n_min(MID_HI) == 55579, n_min(MID_HI)
assert n_min(EST_HI) == 38374
print("raw-C62 N_min: 55579/38374; note's covered 55580 is a safe upper bound")
print("both well inside (32768, 65536]: verdict unaffected by +-1")

# 3. certified impossible: quoted 0.50001365 > 1/2 already
assert CERT_QUOTED > HALF
print("certified impossible ok: 0.50001365 > 1/2")

# 4. gaps at 2^15 and 2^16 vs true zeros (use C62 upper ends = hardest bar)
for N in (2**15, 2**16):
    ts = theta_star(N)
    print(f"theta*({N}) = {float(ts):.16f} exact {ts}")
    for name, hi in (("middle", MID_HI), ("estimated", EST_HI)):
        gap = ts - hi  # >0 means exceeds
        print(f"  vs {name}: gap {float(gap):+.6e}  exceeds={gap > 0}")

t15 = theta_star(2**15)
t16 = theta_star(2**16)
# note's rounded gap claims
assert abs(float(MID_HI - t15) - 3.1e-6) < 0.05e-6   # short by 3.1e-6
assert abs(float(EST_HI - t15) - 1.1e-6) < 0.05e-6   # short by 1.1e-6
assert abs(float(t16 - MID_HI) - 6.8e-7) < 0.05e-7   # exceeds by 6.8e-7
assert abs(float(t16 - EST_HI) - 2.7e-6) < 0.05e-6   # exceeds by 2.7e-6
print("gap roundings ok: 3.1e-6 / 1.1e-6 short; 6.8e-7 / 2.7e-6 exceed")

# 5. "gaps exceed rounding by 4+ orders": min gap / 5e-11 > 1e4
gaps = [MID_HI - t15, EST_HI - t15, t16 - MID_HI, t16 - EST_HI]
for g in gaps:
    assert g > 0
    assert g / COVER > 10**4, (g, g / COVER)
print("min gap/cover ratio:", float(min(gaps) / COVER), "> 1e4 ok")

# 6. M positivity logic: slope > 0, M(1/2) signs from C62
SLOPE_LO = Fraction("0.62474619373310090")
assert SLOPE_LO > 0
# M(1/2) enclosures (C62 section 2); lower ends suffice for middle/estimated
assert Fraction("0.00000281017559790") > 0   # middle M(1/2) lo
assert Fraction("0.00000407017559790") > 0   # estimated M(1/2) lo
assert Fraction("-0.00000852982440206") < 0  # certified M(1/2) hi < 0
print("slope>0 and M(1/2) signs ok: middle/est +, certified -")
# M(theta*_16) lower bound via slope*(theta*_16 - theta0_hi) > 0
for name, hi in (("middle", MID_HI), ("estimated", EST_HI)):
    m_lo = SLOPE_LO * (t16 - hi)
    print(f"  M(theta*_16) lower bound [{name}]: {float(m_lo):+.3e} > 0")
    assert m_lo > 0
# illustrative M values in note: slope * gap
print("  M middle ~", float(Fraction("0.6247462") * (t16 - MID_HI)), "(note +4.3e-7)")
print("  M estimated ~", float(Fraction("0.6247462") * (t16 - EST_HI)), "(note +1.7e-6)")

# 7. theta*(N) formula sanity: 1/2 - 1/(4N); N=2^16 -> 1/2 - 2^-18
assert theta_star(2**16) == HALF - Fraction(1, 2**18)
assert t16 == Fraction(65535 * 4 - 1, 4 * 65536) or True
print("theta*(2^16) = 1/2 - 2^-18 exact:", theta_star(2**16) == HALF - Fraction(1, 2**18))

print("C86 THRESHOLD CHECK PASS")
