"""ce_values_digits.py: the endpoints used in the proof of Lemma ce:values, with all digits.

The replay (reproduce_w3.py, step 6: signed3.py W4 certify) certifies the bound of Lemma ce:values from
the upper end of the combination sum_j c_j Y_cor(sigma_j) - sum T_c(N p) + b_TV (2 kappa_inf - T_sel);
its record prints the two partial sums only to a few digits. This program repeats the same Arb
computation, with the routines of signed.py and the data of witness_0.043171.json, and prints the
upper end of sum_j c_j Y_cor(sigma_j), the lower end of the census sum sum T_c(N p), the upper end of
b_TV (2 kappa_inf - T_sel), and the upper end of the total, with all digits. Writes
ce_values_digits.json. Run from this directory (about four minutes).
"""
import json
import sys
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
import signed3  # noqa: E402  (sets up dihedral_ceiling3 and signed)

DC3, S = signed3.DC3, signed3.S
from flint import arb  # noqa: E402


def main():
    w = json.loads((HERE / "witness_0.043171.json").read_text())
    dih = w["dihedral"]
    DC3.SPACE = DC3.SPACES[dih["space"]]
    params = dih["signed"]
    keep = [(Q(s), Q(c)) for s, c in zip(params["sigmas"], params["c"]) if Q(c) != 0]
    sigs = [s for s, _ in keep]
    cs = [c for _, c in keep]
    bA = S.A(Q(params["b"]))
    total = arb(0)
    for c, E in zip([S.A(c) for c in cs], S.exact_parts(Q(w["delta"]), sigs)):
        total += c * E
    tau = S.census_tau(cs, sigs, dih["prefixes"])
    Br = S.B_r()
    out = {"sum_c_Ycor_upper": str(total.upper()), "sum_c_Ycor_lower": str(total.lower()),
           "census_sum_lower": str(tau.lower()), "census_sum_upper": str(tau.upper()),
           "two_kappa_minus_Tsel": str(Br), "bTV_term_upper": str((bA * Br).upper()),
           "total_upper": str((total - tau + bA * Br).upper())}
    (HERE / "ce_values_digits.json").write_text(json.dumps(out, indent=1) + "\n")
    print(json.dumps(out, indent=1))


if __name__ == "__main__":
    main()
