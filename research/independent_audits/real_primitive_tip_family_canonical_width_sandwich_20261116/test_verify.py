#!/usr/bin/env python3
"""Adversarial finite-arithmetic checks for the new sandwich premises."""
import unittest
from fractions import Fraction as Q
import verify as s


class SandwichAuditTests(unittest.TestCase):
    def test_kkl_marking_and_distinct_maps(self):
        m = s.check_marking()
        self.assertEqual(m["source_crossing_spans"], [3, 3])
        self.assertEqual(m["source_avoiding_span"], 7)
        self.assertEqual(m["cover_avoiding_span"], 5)
        self.assertEqual(m["cover_crossing_endpoints"], [[3, 1], [9, 7]])
        self.assertTrue(m["covering_is_not_immersion"])

    def test_reject_source_shortcuts_and_wrong_bases(self):
        self.assertEqual(s.cyclic_span((3, 17), 20), 7)
        self.assertEqual(s.cyclic_span((3, 1), 20), 3)
        self.assertEqual(s.cyclic_span((0, 1), 20), 2)
        with self.assertRaises(AssertionError):
            s.cyclic_span((0, 0), 20)
        with self.assertRaises(AssertionError):
            s.cyclic_span((20, 1), 20)
        old = s.BLOCKS
        try:
            s.BLOCKS = ((18, 19, 0, 1, 2), (3, 4), (5,), (6,),
                        (7, 8, 9), (10,), (11, 12, 13), (14,), (15,),
                        (16, 17, 17))
            with self.assertRaises(AssertionError):
                s.check_marking()
        finally:
            s.BLOCKS = old

    def test_interval_padding_covers_error_in_both_directions(self):
        zero = s.v.Iv.point(0)
        e = Q(1, 4**13)
        band = s.pad(zero, e)
        self.assertLessEqual(band.low(), -e)
        self.assertGreaterEqual(band.high(), e)
        with self.assertRaises(AssertionError):
            s.pad(zero, -e)

    def test_large_p_model_guard_and_tail_bounds(self):
        _, u = s.v.isolate_model()
        with self.assertRaises(AssertionError):
            s.model_plane_envelope(12, u)
        for p in (13, 14, 15, 17):
            upper = s.model_plane_envelope(p, u)
            self.assertGreater(upper.low(), Q(1, 2))
            self.assertLess(upper.high(), Q(1))
        self.assertLess(s.model_plane_envelope(17, u).high(), Q(78, 100))
        self.assertGreater(s.LIMIT_RADIAL_LOW-Q(7_000_000,4**17), Q(26,100))
        # A common false shortcut: the rate by itself is not enough at p=13.
        self.assertLess(s.LIMIT_RADIAL_LOW-Q(7_000_000,4**13), Q(26,100))

    def test_one_new_finite_high_period_root(self):
        c, x = s.certify_tip(13)
        self.assertTrue(x[13].positive())
        self.assertLess(c.high(), Q(-2)+Q(16,4**13))
        self.assertGreater(c.low(), Q(-2)+Q(14,4**13))


if __name__ == "__main__":
    unittest.main()
