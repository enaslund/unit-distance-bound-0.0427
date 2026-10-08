#!/usr/bin/env python3
"""Exact local functional of a shell profile with general (non-product) weights.

Definition fw:shell-profile (papers/0.04273/sections/finite-windows.tex) allows any finitely
supported nonnegative weights w = (w_ij)_{i,j>=0} with w_00 > 0; the profile is

    g = sum_{i,j} w_ij 1_{S_i x varpi^{-k} S_j},     S_0 = O,  S_i = B_i \\ B_{i-1}  (i >= 1).

Lemma fw:shell-lemma gives A(g) = Q^k A' and Z(g) = Q^k Z' with

    A' = sum_{i,j} m_i m_j w_ij^p,                      p = 2/(1+delta),
    Z' = sum w_ij G_{(i,j),(i',j')} w_i'j',
    G_{(i,j),(i',j')} = (k+1) m_i m_j [i=i'][j=j'] + m_j Delta_{ii'} [j=j'] + m_i Delta_{jj'} [i=i'],
    Delta_{ii'} = m_min(i,i') (i != i'),  Delta_00 = 0,  Delta_ii = i m_i - Q^{i-1} (i >= 1),

so log F_delta(g) = log Z(g) - (1+delta) log A(g) = k log Q + log Z' - (1+delta)(k log Q + log A').
Row index i = shell of the first coordinate, column index j = shell of varpi^k times the second.

local_window_general returns (log_functional, gain, record) exactly like
finite_windows.local_window, where gain = log F_delta(g) - log F_delta(unweighted) =
log(Z'/(k+1)) - (1+delta) log A'.  The overlap Z' is an exact rational, checked against an
independent expansion into indicators of products of balls (mixed second differences of w and
Lemma fw:gram-lemma).  Logarithms and p-th powers use mpmath interval arithmetic, as in
finite_windows.py.

If W is an exact symmetric product W = x x^T with x_0 = 1 (the case local_window handles), the
mass is evaluated as (sum_i m_i x_i^p)^2 by the same interval operations as local_window, so the
returned intervals are identical to local_window's; the general double sum is still evaluated and
must intersect.
"""
from fractions import Fraction as Q

from mpmath import iv

from interval_core import I, qi, lower, upper
from profile_certificate import interval_strings


def shell_masses(norm, n):
    return [1] + [norm**j - norm**(j - 1) for j in range(1, n)]


def shell_delta(norm, n):
    m = shell_masses(norm, n)
    return [[m[min(i, j)] if i != j else (i * m[i] - norm**(i - 1) if i else 0)
             for j in range(n)] for i in range(n)]


def normalize_matrix(W):
    W = [[Q(v) for v in row] for row in W]
    assert W and W[0], "empty weight matrix"
    n2 = len(W[0])
    assert all(len(row) == n2 for row in W), "weight matrix must be rectangular"
    return W


def check_conditions(W):
    """The hypotheses of Definition fw:shell-profile: finitely many (here: a finite matrix of)
    nonnegative weights with w_00 > 0.  No monotonicity, symmetry or product structure is needed."""
    assert all(v >= 0 for row in W for v in row), "weights must be nonnegative"
    assert W[0][0] > 0, "w_00 must be positive"


def shell_overlap(norm, k, W):
    """Z' = Z(g)/Q^k by the shell kernel of Lemma fw:shell-lemma (exact rational)."""
    n1, n2 = len(W), len(W[0])
    m1, m2 = shell_masses(norm, n1), shell_masses(norm, n2)
    D1, D2 = shell_delta(norm, n1), shell_delta(norm, n2)
    second = sum((m1[i] * m2[j] * W[i][j]**2 for i in range(n1) for j in range(n2)), Q(0))
    # transitions in the first coordinate (same second shell j)
    first_transition = sum((m2[j] * sum((D1[i][i2] * W[i][j] * W[i2][j]
                                         for i in range(n1) for i2 in range(n1)), Q(0))
                            for j in range(n2)), Q(0))
    # transitions in the second coordinate (same first shell i)
    second_transition = sum((m1[i] * sum((D2[j][j2] * W[i][j] * W[i][j2]
                                          for j in range(n2) for j2 in range(n2)), Q(0))
                             for i in range(n1)), Q(0))
    overlap = (k + 1) * second + first_transition + second_transition
    return overlap, second, first_transition, second_transition


def rectangle_overlap(norm, k, W):
    """Z' via balls: g = sum_{a,b} D_ab 1_{B_a x B_{b+k}}, D the mixed second difference of w,
    and <1_{B_a x B_{b+k}}, 1_{B_c x B_{d+k}}> = Q^{k+min(a,c)+min(b,d)} (k+max(a,c)+max(b,d)+1)."""
    n1, n2 = len(W), len(W[0])

    def w(i, j):
        return W[i][j] if i < n1 and j < n2 else Q(0)

    D = [[w(a, b) - w(a + 1, b) - w(a, b + 1) + w(a + 1, b + 1) for b in range(n2)] for a in range(n1)]
    cells = [(a, b, D[a][b]) for a in range(n1) for b in range(n2) if D[a][b] != 0]
    total = Q(0)
    for a, b, x in cells:
        for c, d, y in cells:
            total += x * y * norm**(min(a, c) + min(b, d)) * (k + max(a, c) + max(b, d) + 1)
    return total


def symmetric_product_vector(W):
    """x if W = x x^T exactly with x_0 = 1, else None."""
    n = len(W)
    if len(W[0]) != n or W[0][0] != 1:
        return None
    x = W[0]
    for i in range(n):
        for j in range(n):
            if W[i][j] != x[i] * x[j]:
                return None
    return x


def general_mass(norm, W, p):
    """A' = sum m_i m_j w_ij^p as an interval (zero weights contribute 0)."""
    n1, n2 = len(W), len(W[0])
    m1, m2 = shell_masses(norm, n1), shell_masses(norm, n2)
    mass = I(0)
    for i in range(n1):
        for j in range(n2):
            if W[i][j] > 0:
                mass += m1[i] * m2[j] * iv.exp(qi(p) * iv.log(qi(W[i][j])))
    return mass


def local_window_general(norm, k, W, delta, factor_products=True):
    assert isinstance(norm, int) and norm >= 2
    assert isinstance(k, int) and k >= 0
    assert 0 < delta < 1
    W = normalize_matrix(W)
    check_conditions(W)
    overlap, second, t1, t2 = shell_overlap(norm, k, W)
    rect = rectangle_overlap(norm, k, W)
    assert overlap == rect and overlap > 0, "shell kernel and ball expansion disagree"
    # Lemma fw:shell-lemma lower bound Z' >= (k+1) w_00^2
    assert overlap >= (k + 1) * W[0][0]**2
    p = 2 / (1 + delta)
    mass_general = general_mass(norm, W, p)
    assert lower(mass_general) > 0
    log_norm = iv.log(norm)
    x = symmetric_product_vector(W) if factor_products else None
    if x is not None:
        # identical interval operations to finite_windows.local_window
        n = len(x)
        masses = shell_masses(norm, n)
        first_mass = sum((masses[i] * iv.exp(qi(p) * iv.log(qi(x[i]))) for i in range(n)), I(0))
        assert lower(first_mass) > 0
        sq = first_mass * first_mass
        # the general double sum must be consistent with the factorized mass
        assert not (upper(sq) < lower(mass_general) or upper(mass_general) < lower(sq))
        log_mass = k * log_norm + 2 * iv.log(first_mass)
        log_overlap = k * log_norm + iv.log(qi(overlap))
        log_functional = log_overlap - qi(1 + delta) * log_mass
        gain = iv.log(qi(overlap / Q(k + 1))) - 2 * qi(1 + delta) * iv.log(first_mass)
        mass_path = "product (identical to finite_windows.local_window)"
    else:
        log_mass = k * log_norm + iv.log(mass_general)
        log_overlap = k * log_norm + iv.log(qi(overlap))
        log_functional = log_overlap - qi(1 + delta) * log_mass
        gain = iv.log(qi(overlap / Q(k + 1))) - qi(1 + delta) * iv.log(mass_general)
        mass_path = "general double sum"
    if len(W) * len(W[0]) > 1:
        assert lower(gain) > 0, "general weights do not improve on the unweighted shell profile"
    return log_functional, gain, {
        'Q': norm, 'k': k, 'weight_matrix': [[str(v) for v in row] for row in W],
        'shape': [len(W), len(W[0])],
        'mass_path': mass_path,
        'second_moment_exact': str(second),
        'first_coordinate_transition_exact': str(t1),
        'second_coordinate_transition_exact': str(t2),
        'overlap_over_Q_to_k_exact': str(overlap),
        'rectangle_expansion_matches': True,
        'log_mass': interval_strings(log_mass),
        'log_overlap': interval_strings(log_overlap),
        'log_functional': interval_strings(log_functional),
        'gain_over_hard_rectangle': interval_strings(gain),
        'period_log_volume': interval_strings(k * log_norm),
    }


def product_matrix(weights):
    x = [Q(v) for v in weights]
    return [[a * b for b in x] for a in x]
