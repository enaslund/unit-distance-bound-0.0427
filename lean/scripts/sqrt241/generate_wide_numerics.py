#!/usr/bin/env python3
"""Generate UnitDistance/Sqrt241/Analytic/WideNumerics.lean (version 2, work item W4).

Directed rational enclosures, at sigma_W = 1 + 1/4411, of the Euler factors
a(q) = -log(1 - q^-sigma_W) entering the E_W -> M drops of the version-2 bridge, and of the
debit weights w(q) = log q/(q^2-1) at 2:

  dyadic (p = 2):    a(2^2)/32 + a(2^4)/64 - a(2^4)/32
  one (p in C1):     a(p^2)/4 - a(p^4)/4
  two (p in C2):     a(p^2)/2 - a(p^4)/4
  debit at 2:        w(2^2)/32 - w(2^4)/64

C1 = wideCensusOne, C2 = wideCensusTwo (Analytic/WideTypes.lean).  The script only
proposes rational candidates; every inequality is re-proved in Lean by `norm_num` from
the generic lemmas of `Analytic.NumericsBasic` and `Analytic.WideNumericsBasic`.  It checks
in exact rational arithmetic that

  sum of the drop lower bounds + (1/4411) * (debit drop lower bound) >= TARGET = 8469/1000000

and prints the certified value and the slack.

    python3 scripts/sqrt241/generate_wide_numerics.py
"""
from fractions import Fraction as F
from pathlib import Path
import math

ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "UnitDistance/Sqrt241/Analytic/WideNumerics.lean"

LOG2 = (F(69314718055994530941, 10**20), F(69314718055994530942, 10**20))
C1 = [47, 59, 61, 67, 83, 97, 113, 181, 223, 229, 257, 277, 281, 331, 337, 347, 401, 457,
      487, 509, 523, 541, 563, 607, 617, 673, 683, 691, 719, 733, 739, 773, 787, 821, 823,
      857, 877, 881, 883, 887, 937, 967]
C2 = [151, 191, 233, 421, 569, 743, 839, 991]
DEN = 4411
EPS = F(1, DEN)
TARGET = F(8469, 1000000)

ENTRIES = [(2, "dyadic")] + sorted([(p, "one") for p in C1] + [(p, "two") for p in C2])
LOGPRIMES = sorted(C1 + C2)


def floor_to(q, d):
    return F((q.numerator * d) // q.denominator, d)


def ceil_to(q, d):
    return F(-((-q.numerator * d) // q.denominator), d)


def lit(q):
    q = F(q)
    if q.denominator == 1:
        return f"({q.numerator} : ℝ)"
    return f"({q.numerator} : ℝ) / {q.denominator}"


def qlit(q):
    q = F(q)
    if q.denominator == 1:
        return f"({q.numerator} : ℚ)"
    return f"({q.numerator} : ℚ) / {q.denominator}"


def log_ratio(r, n):
    x = (r - 1) / (r + 1)
    s = sum(x ** (2 * i + 1) / (2 * i + 1) for i in range(n))
    return 2 * s, 2 * (s + x ** (2 * n + 1) / (1 - x * x))


LOGDEN = 10**24
logs = {2: LOG2}
logproofs = {}
for p in LOGPRIMES:
    m = round(math.log2(p))
    if p >= 2**m:
        r, form = F(p, 2**m), "mul"
    else:
        r, form = F(2**m, p), "div"
    n = 1
    while True:
        lo, hi = log_ratio(r, n)
        if hi - lo < F(1, 10**22):
            break
        n += 1
    lor, hir = floor_to(lo, LOGDEN), ceil_to(hi, LOGDEN)
    if form == "mul":
        lp, hp = m * LOG2[0] + lor, m * LOG2[1] + hir
    else:
        lp, hp = m * LOG2[0] - hir, m * LOG2[1] - lor
    assert lp < hp and abs(float(lp) - math.log(p)) < 1e-12 and abs(float(hp) - math.log(p)) < 1e-12
    logs[p] = (lp, hp)
    logproofs[p] = (m, r, form, n, lor, hir)


def exp_lower(t):
    return 1 - t + t**2 / 2 - t**3 / 6 - 5 * t**4 / 96


def exp_upper(t):
    return 1 - t + t**2 / 2 - t**3 / 6 + 5 * t**4 / 96


YDEN = 10**30
VDEN = 10**25


def series(Y, N):
    return sum(Y ** (i + 1) / (i + 1) for i in range(N))


def a_lower(p, k):
    hi = logs[p][1]
    t = k * hi / DEN
    assert 0 <= t <= 1
    Y = floor_to(exp_lower(t) / p**k, YDEN)
    N = 1
    while Y ** (N + 1) / (1 - Y) > F(1, 10**24):
        N += 1
    L = floor_to(series(Y, N), VDEN)
    return dict(p=p, k=k, hi=hi, Y=Y, N=N, L=L)


def a_upper(p, k):
    lo = logs[p][0]
    t = k * lo / DEN
    assert 0 <= t <= 1
    Y = ceil_to(exp_upper(t) / p**k, YDEN)
    N = 1
    while Y ** (N + 1) / (1 - Y) > F(1, 10**24):
        N += 1
    U = ceil_to(series(Y, N) + Y ** (N + 1) / (1 - Y), VDEN)
    return dict(p=p, k=k, lo=lo, Y=Y, N=N, U=U)


def w_lower(p, k):
    return floor_to(k * logs[p][0] / (F(p) ** (2 * k) - 1), VDEN)


def w_upper(p, k):
    return ceil_to(k * logs[p][1] / (F(p) ** (2 * k) - 1), VDEN)


# (lower exponents with divisors, upper exponents with divisors) of each kind
KIND = {
    "dyadic": ([(2, 32), (4, 64)], [(4, 32)]),
    "one": ([(2, 4)], [(4, 4)]),
    "two": ([(2, 2)], [(4, 4)]),
}

alow, aup = {}, {}
for p, kind in ENTRIES:
    lows, ups = KIND[kind]
    for k, _ in lows:
        alow[(p, k)] = a_lower(p, k)
    for k, _ in ups:
        aup[(p, k)] = a_upper(p, k)

drops = []
for p, kind in ENTRIES:
    lows, ups = KIND[kind]
    val = sum(alow[(p, k)]["L"] / d for k, d in lows) - sum(aup[(p, k)]["U"] / d for k, d in ups)
    drops.append(floor_to(val, VDEN))
wl22, wu24 = w_lower(2, 2), w_upper(2, 4)
debit = floor_to(wl22 / 32 - wu24 / 64, VDEN)
total = sum(drops) + EPS * debit
print("entries:", len(ENTRIES))
print("certified sum of drops:", float(sum(drops)), " debit drop x eps:", float(EPS * debit))
print("certified correction total:", float(total), " target", float(TARGET), " slack", float(total - TARGET))
assert total >= TARGET

lines = []
w = lines.append
w("-- Generated by scripts/sqrt241/generate_wide_numerics.py — do not edit by hand.")
w("module\n\npublic import UnitDistance.Sqrt241.Analytic.WideCorrections\n\n@[expose] public section")
w("set_option backward.privateInPublic true\n\n")
w("/-!\n# Generated enclosures of the `E_W → M` drops at `σ_W = 1 + 1/4411`\n")
w("Generated by `scripts/sqrt241/generate_wide_numerics.py`; do not edit.")
w("Every rational endpoint is re-proved by `norm_num` from the generic lemmas of")
w("`Analytic.NumericsBasic` and `Analytic.WideNumericsBasic`.  The data `widePrimes`,")
w("`wideKinds`, `wideLower` list the 51 correction primes (2 and the census primes")
w("of `wideCensusOne` and `wideCensusTwo`), their kinds and certified lower bounds of")
w("their drops; `wide_corrections_ge` is the numerical input of `Analytic.WideBridge`.")
w(f"Certified value of the corrections: {float(total):.13f}; slack over {TARGET} is {float(total - TARGET):.3e}.\n-/\n")
w("noncomputable section\n")
w("namespace UnitDistance.Sqrt241.Analytic.WideNumerics\n")
w("open UnitDistance.NumberFieldAnalysis UnitDistance.Sqrt241.Analytic\n")

for p in LOGPRIMES:
    m, r, form, n, lor, hir = logproofs[p]
    lp, hp = logs[p]
    fn = "log_bounds_mul_two_pow" if form == "mul" else "log_bounds_div_two_pow"
    w(f"theorem log{p}_bounds :\n    {lit(lp)} ≤ Real.log ({p} : ℝ) ∧ Real.log ({p} : ℝ) ≤ {lit(hp)} := by")
    w(f"  have hr := UnitDistance.log_enclosure ({lit(r)}) {n} (by norm_num) ({lit(lor)}) ({lit(hir)})")
    w("    (by norm_num [Finset.sum_range_succ]) (by norm_num [Finset.sum_range_succ])")
    w(f"  have h := {fn} {p} {m} ({lit(r)}) (by norm_num) (by norm_num) log_two_bounds hr")
    w("  norm_num only [Nat.cast_ofNat] at h")
    w("  constructor <;> linarith [h.1, h.2]\n")

for p in [2] + LOGPRIMES:
    lp, hp = logs[p]
    src = "log_two_bounds" if p == 2 else f"log{p}_bounds"
    w(f"theorem log_nat{p}_bounds :\n    {lit(lp)} ≤ Real.log (({p} : ℕ) : ℝ) ∧ Real.log (({p} : ℕ) : ℝ) ≤ {lit(hp)} := by")
    w(f"  have h := {src}")
    w("  norm_num only [Nat.cast_ofNat] at h ⊢")
    w("  exact h\n")


def logref(p, side):
    return f"log_nat{p}_bounds." + ("2" if side == "hi" else "1")


for (p, k), d in alow.items():
    w(f"theorem a_lower_{p}_{k} : {lit(d['L'])} ≤ primeEulerLog ({p} ^ {k}) sigmaW :=")
    w(f"  primeEulerLogW_pow_lower (p := {p}) (k := {k}) (hi := {lit(d['hi'])}) (Y := {lit(d['Y'])})")
    w(f"    (hp := by norm_num) (hk := by norm_num) (N := {d['N']}) (hlog := {logref(p, 'hi')})")
    w("    (h0 := by norm_num) (h1 := by norm_num) (hY0 := by norm_num)")
    w("    (hY := by norm_num [expNegLower]) (hL := by norm_num [Finset.sum_range_succ])\n")

for (p, k), d in aup.items():
    w(f"theorem a_upper_{p}_{k} : primeEulerLog ({p} ^ {k}) sigmaW ≤ {lit(d['U'])} :=")
    w(f"  primeEulerLogW_pow_upper (p := {p}) (k := {k}) (lo := {lit(d['lo'])}) (Y := {lit(d['Y'])})")
    w(f"    (hp := by norm_num) (N := {d['N']}) (hlog := {logref(p, 'lo')})")
    w("    (h0 := by norm_num) (h1 := by norm_num) (hY1 := by norm_num)")
    w("    (hY := by norm_num [expNegUpper]) (hU := by norm_num [Finset.sum_range_succ])\n")

kindname = {"dyadic": ".dyadic", "one": ".one", "two": ".two"}
for (p, kind), r in zip(ENTRIES, drops):
    lows, ups = KIND[kind]
    hyps = [f"a_lower_{p}_{k}" for k, _ in lows] + [f"a_upper_{p}_{k}" for k, _ in ups]
    w(f"theorem drop_ge_{p} : (({qlit(r)} : ℚ) : ℝ) ≤ lowerDropW {kindname[kind]} eulerWeightW {p} := by")
    w(f"  rw [show (({qlit(r)} : ℚ) : ℝ) = {lit(r)} by norm_num]")
    w("  unfold lowerDropW kindLower kindUpper eulerWeightW")
    w(f"  linarith [{', '.join(hyps)}]\n")

n = len(ENTRIES)
w(f"/-- The {n} correction primes of the version-2 bridge. -/")
w(f"def widePrimes : Fin {n} → Nat.Primes :=\n  ![" +
  ",\n    ".join(f"⟨{p}, by norm_num⟩" for p, _ in ENTRIES) + "]\n")
w("/-- Their kinds. -/")
w(f"def wideKinds : Fin {n} → WideKind :=\n  ![" +
  ", ".join(kindname[k] for _, k in ENTRIES) + "]\n")
w("/-- Certified lower bounds of their drops at `σ_W`. -/")
w(f"def wideLower : Fin {n} → ℚ :=\n  ![" + ",\n    ".join(qlit(r) for r in drops) + "]\n")
w("theorem widePrimes_injective : Function.Injective widePrimes := by\n  decide\n")
w("theorem wideKinds_spec : ∀ i, (wideKinds i = .dyadic → (widePrimes i).val = 2) ∧")
w("    (wideKinds i = .one → (widePrimes i).val ∈ wideCensusOne) ∧")
w("    (wideKinds i = .two → (widePrimes i).val ∈ wideCensusTwo) := by\n  decide +kernel\n")
w("theorem wideLower_le (i : Fin " + str(n) + ") :\n    (wideLower i : ℝ) ≤ lowerDropW (wideKinds i) eulerWeightW (widePrimes i).val := by")
w("  fin_cases i")
w("  exacts [" + ", ".join(f"drop_ge_{p}" for p, _ in ENTRIES) + "]\n")
w(f"theorem wideLower_sum : (∑ i, wideLower i) = {qlit(sum(drops))} := by")
w("  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, wideLower, Matrix.cons_val_zero,")
w("    Matrix.cons_val_succ]")
w("  norm_num\n")
w(f"theorem w_lower_2_2 : {lit(wl22)} ≤ primeDebitWeight (((2 ^ 2 : ℕ) : ℝ)) :=")
w(f"  primeDebitWeight_pow_lower (p := 2) (k := 2) (lo := {lit(logs[2][0])}) (hp := by norm_num)")
w("    (hk := by norm_num) (hlog := log_nat2_bounds.1) (hL := by norm_num)\n")
w(f"theorem w_upper_2_4 : primeDebitWeight (((2 ^ 4 : ℕ) : ℝ)) ≤ {lit(wu24)} :=")
w(f"  primeDebitWeight_pow_upper (p := 2) (k := 4) (hi := {lit(logs[2][1])}) (hp := by norm_num)")
w("    (hk := by norm_num) (hlog := log_nat2_bounds.2) (hU := by norm_num)\n")
w(f"/-- The certified corrections of the version-2 bridge exceed `{TARGET}`. -/")
w("theorem wide_corrections_ge :")
w(f"    ({TARGET.numerator} : ℝ) / {TARGET.denominator} ≤ (∑ i, (wideLower i : ℝ)) +")
w("      (1 / 4411 : ℝ) * (primeDebitWeight (((2 ^ 2 : ℕ) : ℝ)) / 32 -")
w("        primeDebitWeight (((2 ^ 4 : ℕ) : ℝ)) / 64) := by")
w("  have hs : (∑ i, (wideLower i : ℝ)) = ((∑ i, wideLower i : ℚ) : ℝ) :=")
w("    (Rat.cast_sum Finset.univ wideLower).symm")
w(f"  rw [hs, wideLower_sum, show (({qlit(sum(drops))} : ℚ) : ℝ) = {lit(sum(drops))} by norm_num]")
w("  linarith [w_lower_2_2, w_upper_2_4]\n")
w("end UnitDistance.Sqrt241.Analytic.WideNumerics")
OUT.write_text("\n".join(lines) + "\n")
print("wrote", OUT, len(lines), "lines")
