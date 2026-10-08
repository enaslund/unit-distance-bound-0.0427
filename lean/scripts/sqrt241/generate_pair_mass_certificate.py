#!/usr/bin/env python3
"""Generate the pair-mass certificate data for the Q(sqrt 241) witness.

Writes
  UnitDistance/Sqrt241/Numerics/PairMassTables.lean  (power-basis tables of P, P^2, P^3)
  UnitDistance/Sqrt241/Numerics/PairMassData.lean    (grid enclosures, cell centers,
                                                      center powers, per-cell contribution
                                                      bounds, final bound, checks)

The mass is E[P(T,U)^p] for T, U i.i.d. Beta(q,1) with
p = 2/(1+delta) = 40000/20863 and q = s p - 1 = 12488617/10431500
(s = 22920117/20000000, the manuscript's).  The unit square is cut into
N x N cells; on each cell the Lean side bounds P^p by h^p times the degree-3
binomial polynomial in w = P/h - 1 plus the uniform tail, integrates it exactly
against the beta densities and evaluates the result with directed rational
enclosures of the grid powers (k/N)^q.  Everything below mirrors the rational
computation of `PairMassRat.lean` exactly; floating point (mpmath) is used only
to choose the candidate enclosures, which Lean re-checks with the outward-rounded
logarithm enclosures `logLoR`/`logHiR` of `RatLogRounded.lean`.

The emitted checks are split so that every kernel reduction stays small: one
lemma per grid point, one per cell for the centers and center powers, and one
per cell bounding its exact contribution HTab * max(cellEbar, 0) (a rational with
a denominator of a few hundred digits) by cTab, rounded up to a multiple of
10^-CDIGITS.  Only the short rationals cTab are summed against the final bound.

Usage: generate_pair_mass_certificate.py [N]
"""
import sys
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(HERE))

try:
    from mpmath import mp, mpf, power
except ImportError:  # pragma: no cover
    import os
    sys.path.insert(0, os.environ.get("PYLIB", ""))
    from mpmath import mp, mpf, power

mp.dps = 60

N = int(sys.argv[1]) if len(sys.argv) > 1 else 12
DEG = 3                     # binomial truncation degree (fixed in PairMassRat.binA)
XDIGITS = 25                # decimal digits of the grid-power enclosures
HDIGITS = 15                # significant digits of the cell centers
HPDIGITS = 20               # significant digits of the center powers
CDIGITS = 15                # decimals of the per-cell contribution bounds
MDIGITS = 9                 # decimals of the final bound

pQ = Q(40000, 20863)
qQ = Q(12488617, 10431500)
assert Q(22920117, 20000000) * pQ - 1 == qQ

# Power-basis coefficients of the manuscript polynomial
# (UnitDistance.Witness.pairOverlapPowerCoefficient).
C1 = [[Q(1), Q(42388316931, 10000000000), Q(-3951404529, 1250000000), Q(23040358681, 5000000000)],
      [Q(42388316931, 10000000000), Q(1233476703, 5000000000), Q(1117209393, 312500000), Q(-37257860547, 10000000000)],
      [Q(-3951404529, 1250000000), Q(1117209393, 312500000), Q(-2193824061, 312500000), Q(65331233457, 10000000000)],
      [Q(23040358681, 5000000000), Q(-37257860547, 10000000000), Q(65331233457, 10000000000), Q(-22484447969, 5000000000)]]


def pmul(A, B):
    R = [[Q(0)] * (len(A[0]) + len(B[0]) - 1) for _ in range(len(A) + len(B) - 1)]
    for i, ra in enumerate(A):
        for j, x in enumerate(ra):
            for k, rb in enumerate(B):
                for l, y in enumerate(rb):
                    R[i + k][j + l] += x * y
    return R


C2 = pmul(C1, C1)
C3 = pmul(C2, C1)
TABLES = {0: [[Q(1)]], 1: C1, 2: C2, 3: C3}


def cpow(m, i, j):
    T = TABLES[min(m, 3)]
    if i < len(T) and j < len(T[i]):
        return T[i][j]
    return Q(0)


def PQ(x, y):
    return sum(C1[i][j] * x ** i * y ** j for i in range(4) for j in range(4))


def gchoose(x, k):
    r = Q(1)
    for n in range(k):
        r = r * (x - n) / (n + 1)
    return r


def cell_rho(h, lo, hi):
    return max(hi / h - 1, 1 - lo / h)


def binA(h, m):
    g = [gchoose(pQ, k) for k in range(4)]
    if m == 0:
        return g[0] - g[1] + g[2] - g[3]
    if m == 1:
        return (g[1] - 2 * g[2] + 3 * g[3]) / h
    if m == 2:
        return (g[2] - 3 * g[3]) / h ** 2
    return g[3] / h ** 3


def tailQ(rho):
    return abs(gchoose(pQ, 4)) * rho ** 4 / (1 - rho)


def cell_coeff(h, rho, i, j):
    v = sum(binA(h, m) * cpow(m, i, j) for m in range(4))
    if i == 0 and j == 0:
        v += tailQ(rho)
    return v


def floor_q(x, scale):
    x = Q(x)
    return Q((x.numerator * scale) // x.denominator, scale)


def ceil_q(x, scale):
    return -floor_q(-Q(x), scale)


def mpq(x):
    x = Q(x)
    return mpf(x.numerator) / x.denominator


# Grid-power enclosures XL k <= (k/N)^q <= XU k.
XS = 10 ** XDIGITS
XL, XU = [], []
for k in range(N + 1):
    if k == 0:
        XL.append(Q(0)); XU.append(Q(0))
    elif k == N:
        XL.append(Q(1)); XU.append(Q(1))
    else:
        v = power(mpf(k) / N, mpq(qQ))
        XL.append(Q(int(mp.floor(v * XS)) - 1, XS))
        XU.append(Q(int(mp.ceil(v * XS)) + 1, XS))


def mu_lo(k, m):
    a = qQ / (qQ + m) * (Q(k + 1, N) ** m * XL[k + 1] - Q(k, N) ** m * XU[k])
    return max(Q(0), a)


def mu_hi(k, m):
    return qQ / (qQ + m) * (Q(k + 1, N) ** m * XU[k + 1] - Q(k, N) ** m * XL[k])


def dirU(d, x0, x1, y0, y1):
    return d * x1 * y1 if d >= 0 else d * x0 * y0


def round_sig(x, digits):
    """Round a positive rational to `digits` significant decimal digits."""
    x = Q(x)
    e = 0
    while x >= 10 ** (digits):
        x /= 10; e += 1
    while x < 10 ** (digits - 1):
        x *= 10; e -= 1
    n = round(x)
    return Q(n) * Q(10) ** e


def up_sig(xmp, digits):
    """Rational upper bound of a positive mpf with `digits` significant digits plus one ulp."""
    e = int(mp.floor(mp.log10(xmp))) - digits + 1
    scale = Q(10) ** (-e)
    n = int(mp.ceil(xmp * mpq(scale))) + 1
    return Q(n) / scale


hTab = [[None] * N for _ in range(N)]
HTab = [[None] * N for _ in range(N)]
cTab = [[None] * N for _ in range(N)]
total = Q(0)
ctotal = Q(0)
max_rho = Q(0)
for i in range(N):
    for j in range(N):
        lo = PQ(Q(i, N), Q(j, N))
        hi = PQ(Q(i + 1, N), Q(j + 1, N))
        h = round_sig((lo + hi) / 2, HDIGITS)
        rho = cell_rho(h, lo, hi)
        assert 0 <= rho < 1
        max_rho = max(max_rho, rho)
        H = up_sig(power(mpq(h), mpq(pQ)), HPDIGITS)
        hTab[i][j] = h
        HTab[i][j] = H
        E = Q(0)
        for a in range(3 * DEG + 1):
            for b in range(3 * DEG + 1):
                E += dirU(cell_coeff(h, rho, a, b), mu_lo(i, a), mu_hi(i, a), mu_lo(j, b), mu_hi(j, b))
        contribution = H * max(E, Q(0))
        # Directed rounding of the exact cell contribution (checked cell by cell in Lean).
        cTab[i][j] = ceil_q(contribution, 10 ** CDIGITS)
        assert contribution <= cTab[i][j]
        total += contribution
        ctotal += cTab[i][j]
    print("row", i, float(total), flush=True)

Mbar = ceil_q(ctotal, 10 ** MDIGITS)
assert total <= ctotal <= Mbar
print("N", N, "max rho", float(max_rho), "total", float(total), "rounded total", float(ctotal),
      "Mbar", Mbar, float(Mbar))


def qlit(x):
    x = Q(x)
    return f"{x.numerator}" if x.denominator == 1 else f"{x.numerator} / {x.denominator}"


def qlist(xs):
    return "[" + ", ".join(qlit(x) for x in xs) + "]"


def qtable(T, indent="  "):
    return "[" + (",\n" + indent + " ").join(qlist(row) for row in T) + "]"


HEADER = """-- Generated by scripts/sqrt241/generate_pair_mass_certificate.py — do not edit by hand.
module

{imports}

@[expose] public section
set_option backward.privateInPublic true


"""

tables = HEADER.format(imports="public import UnitDistance.Sqrt241.Numerics.PairTransfer") + f"""/-!
# Power-basis tables of the pair polynomial and its square and cube

Generated by `scripts/sqrt241/generate_pair_mass_certificate.py`. `cPow m i j`
is the coefficient of `t^i u^j` in `P(t,u)^m` for `m ≤ 3` (zero outside the
tables); the identities are checked by `ring`.
-/

namespace UnitDistance.Sqrt241.Witness.MassCert

def c1Table : List (List ℚ) :=
  {qtable(C1)}

def c2Table : List (List ℚ) :=
  {qtable(C2)}

def c3Table : List (List ℚ) :=
  {qtable(C3)}

/-- Coefficient tables of `P^m` (`m = 0, 1, 2, 3`). -/
def coeffTable : ℕ → List (List ℚ)
  | 0 => [[1]]
  | 1 => c1Table
  | 2 => c2Table
  | _ => c3Table

/-- The coefficient of `t^i u^j` in `P(t,u)^m`, for `m ≤ 3`. -/
def cPow (m i j : ℕ) : ℚ := ((coeffTable m).getD i []).getD j 0

theorem polynomial_eq_table (t u : ℝ) :
    polynomial t u =
      ∑ i ∈ Finset.range 4, ∑ j ∈ Finset.range 4, ((cPow 1 i j : ℚ) : ℝ) * t ^ i * u ^ j := by
  rw [polynomial_eq_manuscript, _root_.UnitDistance.Witness.polynomial_eq_pairOverlapPowerBasis]
  simp only [Fin.sum_univ_four, Finset.sum_range_succ, Finset.sum_range_zero, cPow, coeffTable,
    c1Table, List.getD_cons_succ, List.getD_cons_zero,
    _root_.UnitDistance.Witness.pairOverlapPowerCoefficient]
  norm_num

set_option maxHeartbeats 1000000 in
theorem polynomial_pow_eq_table (m : ℕ) (hm : m ≤ 3) (t u : ℝ) :
    polynomial t u ^ m =
      ∑ i ∈ Finset.range 10, ∑ j ∈ Finset.range 10, ((cPow m i j : ℚ) : ℝ) * t ^ i * u ^ j := by
  interval_cases m
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero, cPow, coeffTable,
      List.getD_cons_succ, List.getD_cons_zero, List.getD_nil]
    norm_num
  · rw [polynomial_eq_table]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, cPow, coeffTable, c1Table,
      List.getD_cons_succ, List.getD_cons_zero, List.getD_nil]
    norm_num
  · rw [polynomial_eq_table]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, cPow, coeffTable, c1Table, c2Table,
      List.getD_cons_succ, List.getD_cons_zero, List.getD_nil]
    push_cast
    ring
  · rw [polynomial_eq_table]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, cPow, coeffTable, c1Table, c3Table,
      List.getD_cons_succ, List.getD_cons_zero]
    push_cast
    ring

end UnitDistance.Sqrt241.Witness.MassCert
"""

# ---------------------------------------------------------------------------
# Kernel checks, one lemma per grid point and per cell.


def grid_prop(k, kq):
    """Grid-point check at `k`; `kq` is the natural number cast into `ℚ`."""
    return (f"0 < XL {k} ∧ 0 < XU {k} ∧ logHiR (XL {k}) ≤ qQ * logLoR (({kq} : ℚ) / gridN) ∧\n"
            f"      qQ * logHiR (({kq} : ℚ) / gridN) ≤ logLoR (XU {k})")


def cell_prop(i, j):
    return (f"0 < hTab {i} {j} ∧ cellRho (hTab {i} {j}) (cellLo gridN {i} {j}) (cellHi gridN {i} {j}) < 1 ∧\n"
            f"      0 < HTab {i} {j} ∧ pQ * logHiR (hTab {i} {j}) ≤ logLoR (HTab {i} {j})")


def contrib_prop(i, j):
    return f"HTab {i} {j} * max (cellEbar gridN XL XU {i} {j} (hTab {i} {j})) 0 ≤ cTab {i} {j}"


def assemble(n, leaf, last="exact forall_lt_zero _"):
    """Tactic proof of `∀ k, k < n → P k` from the case proofs `leaf(k)` (P from the goal)."""
    lines = [f"  refine forall_lt_succ_of (n := {k}) ?_ {leaf(k)}" for k in reversed(range(n))]
    return "\n".join(lines + ["  " + last])


checks = []
checks.append("""theorem grid_endpoints : XL 0 = 0 ∧ XU 0 = 0 ∧ XL gridN = 1 ∧ XU gridN = 1 := by
  decide +kernel""")
for k in range(1, N):
    checks.append(f"""theorem grid_check_{k} :
    {grid_prop(k, f"({k} : ℕ)")} := by
  decide +kernel""")
leaf = lambda k: "fun h => absurd h (Nat.lt_irrefl 0)" if k == 0 else f"fun _ => grid_check_{k}"
checks.append(f"""theorem grid_checks : ∀ k, k < gridN → 0 < k →
    {grid_prop("k", "k")} := by
{assemble(N, lambda k: f"({leaf(k)})")}""")

for i in range(N):
    for j in range(N):
        checks.append(f"""theorem cell_check_{i}_{j} :
    {cell_prop(i, j)} := by
  decide +kernel""")
for i in range(N):
    checks.append(f"""theorem cell_checks_{i} : ∀ j, j < gridN →
    {cell_prop(i, "j")} := by
{assemble(N, lambda j: f"cell_check_{i}_{j}")}""")
checks.append(f"""theorem cell_checks : ∀ i, i < gridN → ∀ j, j < gridN →
    {cell_prop("i", "j")} := by
{assemble(N, lambda i: f"cell_checks_{i}")}""")

for i in range(N):
    for j in range(N):
        checks.append(f"""theorem contrib_check_{i}_{j} :
    {contrib_prop(i, j)} := by
  decide +kernel""")
for i in range(N):
    checks.append(f"""theorem contrib_checks_{i} : ∀ j, j < gridN →
    {contrib_prop(i, "j")} := by
{assemble(N, lambda j: f"contrib_check_{i}_{j}")}""")
checks.append(f"""theorem contrib_checks : ∀ i, i < gridN → ∀ j, j < gridN →
    {contrib_prop("i", "j")} := by
{assemble(N, lambda i: f"contrib_checks_{i}")}""")

checks.append("""/-- The rounded contributions sum to at most the final bound. -/
theorem total_sum_check :
    sumRange (fun i => sumRange (fun j => cTab i j) gridN) gridN ≤ massUpper := by
  decide +kernel""")
checks.append("""theorem total_check : massTotal gridN XL XU hTab HTab ≤ massUpper :=
  (massTotal_le_of_cells gridN XL XU hTab HTab cTab contrib_checks).trans total_sum_check""")
checks.append("""theorem pairMassBetaIntegral_le_massUpper : pairMassBetaIntegral ≤ (massUpper : ℝ) :=
  pairMassBetaIntegral_le_of_checks gridN (by decide) XL XU hTab HTab massUpper
    grid_endpoints grid_checks cell_checks total_check""")
CHECKS = "\n\n".join(checks)

data = HEADER.format(imports="public import UnitDistance.Sqrt241.Numerics.PairMassCell") + f"""/-!
# Pair-mass certificate data (N = {N})

Generated by `scripts/sqrt241/generate_pair_mass_certificate.py {N}`. The grid
enclosures `XL k ≤ (k/N)^q ≤ XU k`, the cell centers `hTab`, the center-power
bounds `HTab ≥ hTab^p` and the cell-contribution bounds `cTab` are candidates;
every inequality they must satisfy is checked below by kernel evaluation of the
rational bounds of `RatLogRounded` and `PairMassRat`.

Every grid point and every cell is checked by its own lemma, so that each kernel
reduction stays small. The exact contribution `HTab i j * max (cellEbar …) 0` of a
cell is a rational with a denominator of a few hundred digits; it is bounded cell
by cell (`contrib_check_i_j`) by `cTab i j`, rounded up to a multiple of
`10^-{CDIGITS}`, and only these short rationals are summed (`total_sum_check`).
-/

namespace UnitDistance.Sqrt241.Witness.MassCert

open UnitDistance.Sqrt241.Numerics

def gridN : ℕ := {N}

def xlTable : List ℚ := {qlist(XL)}

def xuTable : List ℚ := {qlist(XU)}

def XL (k : ℕ) : ℚ := xlTable.getD k 0

def XU (k : ℕ) : ℚ := xuTable.getD k 0

def hTable : List (List ℚ) :=
  {qtable(hTab)}

def HTable : List (List ℚ) :=
  {qtable(HTab)}

def hTab (i j : ℕ) : ℚ := (hTable.getD i []).getD j 1

def HTab (i j : ℕ) : ℚ := (HTable.getD i []).getD j 1

/-- Upper bounds for the cell contributions `HTab i j * max (cellEbar …) 0`,
rounded up to multiples of `10^-{CDIGITS}`. -/
def cTable : List (List ℚ) :=
  {qtable(cTab)}

def cTab (i j : ℕ) : ℚ := (cTable.getD i []).getD j 0

/-- The certified upper bound for the normalized mass. -/
def massUpper : ℚ := {qlit(Mbar)}

{CHECKS}

end UnitDistance.Sqrt241.Witness.MassCert
"""

out = ROOT / "UnitDistance/Sqrt241/Numerics"
(out / "PairMassTables.lean").write_text(tables)
(out / "PairMassData.lean").write_text(data)
print("wrote", out / "PairMassTables.lean", out / "PairMassData.lean")
