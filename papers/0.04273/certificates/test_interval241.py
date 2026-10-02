"""Regression checks for interval endpoints, serialization and strict inequalities.

Run from this directory: python3 -m unittest -v test_interval241
Requires the same dependencies and PYLIB setup as reproduce241.py.
"""
import json
import unittest
from fractions import Fraction

import env241  # noqa: F401
from flint import arb, ctx
from interval241 import logderiv_tail_bound, outward_float_bounds, require_strict_upper_bound


class IntervalCertificateTests(unittest.TestCase):
    def setUp(self):
        self.previous_precision = ctx.prec
        ctx.prec = 256

    def tearDown(self):
        ctx.prec = self.previous_precision

    def assert_serialized_enclosure(self, value):
        encoded = json.dumps(outward_float_bounds(value))
        # Check both Python's float interpretation and exact decimal endpoints
        # (as read by the independent PARI consistency check).
        for parse_float in (float, str):
            lo, hi = json.loads(encoded, parse_float=parse_float)
            self.assertTrue(arb(lo) <= value.lower())
            self.assertTrue(value.upper() <= arb(hi))

    def test_outward_json_round_trip(self):
        for value in (arb(0), arb(1), arb(1) / 10, -arb(1) / 10,
                      arb.pi(), arb('[1.25 +/- 0.001]')):
            with self.subTest(value=str(value)):
                self.assert_serialized_enclosure(value)

    def test_base_field_values_do_not_collapse_to_incorrect_points(self):
        from afe241 import zeta_B
        for value in zeta_B(arb(301) / 300):
            # These are the two diagnostic fields that used to be exported
            # as zero-width intervals excluding their actual values.
            lo, hi = outward_float_bounds(value)
            self.assertLess(lo, hi)
            self.assert_serialized_enclosure(value)

    def test_strict_bound_uses_the_radius(self):
        require_strict_upper_bound('[0.04871284 +/- 0.000000001]', '0.04871285')
        for value in ('[0.04871284 +/- 0.00000002]', '0.04871285', '0.04871286'):
            with self.subTest(value=value), self.assertRaises(ValueError):
                require_strict_upper_bound(value, '0.04871285')

    def test_tail_bound_dominates_finite_partial_sums(self):
        for cutoff in (2, 10, 100):
            partial = sum((arb(n).log() / (n*n - 1)
                           for n in range(cutoff + 1, 10000)), arb(0))
            self.assertTrue(partial < logderiv_tail_bound(cutoff))
        for cutoff in (0, 1, 2.5):
            with self.subTest(cutoff=cutoff), self.assertRaises(ValueError):
                logderiv_tail_bound(cutoff)


class ProfileIntervalTests(unittest.TestCase):
    def test_mass_and_digamma_boxes_preserve_exact_endpoints(self):
        # Load the active entry point so this also checks both archived
        # call sites use its corrected constructor.
        import geom241
        from mpmath import mp, iv

        def exact(t):
            sign, mantissa, exponent, _ = t
            return (-1 if sign else 1) * Fraction(mantissa) * Fraction(2)**exponent

        previous_mp, previous_iv = mp.dps, iv.dps
        try:
            for mp_precision, iv_precision in ((80, 80), (160, 80), (80, 160)):
                mp.dps, iv.dps = mp_precision, iv_precision
                for x in (mp.mpf(0), mp.mpf(1)/3, mp.mpf(1)/7, mp.mpf(1)/3 * mp.mpf('1e-50')):
                    for module in (geom241.interval_core, geom241.profile_certificate):
                        with self.subTest(module=module.__name__, mp=mp_precision,
                                          iv=iv_precision, endpoint=str(x)):
                            result = module.box(-x, x)
                            self.assertLessEqual(exact(result._mpi_[0]), exact((-x)._mpf_))
                            self.assertGreaterEqual(exact(result._mpi_[1]), exact(x._mpf_))
        finally:
            mp.dps, iv.dps = previous_mp, previous_iv


if __name__ == '__main__':
    unittest.main()
