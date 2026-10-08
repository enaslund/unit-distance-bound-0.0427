#!/usr/bin/env python3
"""geom241.margin with general (non-product) shell weights at chosen finite places.

shells = {"ks": {prime: k}, "finite_profiles": {prime: profile}}, where a profile is either
  * a list of weights (product profile w_ij = x_i x_j, handled by finite_windows.local_window), or
  * a matrix (list of rows) of weights w_ij (handled by general_windows.local_window_general).
geom241.margin is called unchanged; only its module-level name local_window is replaced, for the
duration of the call, by a dispatcher, and restored afterwards (also on error).  geom241.EF is set
to the given EF for the call and restored afterwards.
"""
import finite_windows
import geom241
from general_windows import local_window_general


def is_matrix(profile):
    return bool(profile) and isinstance(profile[0], (list, tuple))


def local_window_dispatch(norm, k, weights, delta):
    if is_matrix(weights):
        return local_window_general(norm, k, weights, delta)
    return finite_windows.local_window(norm, k, weights, delta)


def margin_general(delta, C, shells, s=None, a=None, bern=None, verbose=False, EF=None):
    saved_lw, saved_ef = geom241.local_window, geom241.EF
    geom241.local_window = local_window_dispatch
    if EF is not None:
        geom241.EF = dict(EF)
    try:
        return geom241.margin(delta, C, shells, s=s, a=a, bern=bern, verbose=verbose)
    finally:
        geom241.local_window, geom241.EF = saved_lw, saved_ef


def finite_sum(delta, shells, EF):
    """sum_r log F_{delta,r}/(e_r f_r) alone (the only weight-dependent term of the margin), as in geom241.margin."""
    from fractions import Fraction as Q
    from interval_core import I
    delta = Q(delta)
    total = I(0)
    parts = {}
    for key, k in shells["ks"].items():
        prime = int(key)
        e, f = EF[prime]
        val, gain, rec = local_window_dispatch(prime**f, int(k), shells["finite_profiles"][key], delta)
        total += val / (e * f)
        parts[key] = (val / (e * f), gain / (e * f), rec)
    return total, parts
