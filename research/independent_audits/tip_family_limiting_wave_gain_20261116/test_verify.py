#!/usr/bin/env python3
"""Adversarial interval/marking regression tests for the new-only gain audit."""
from __future__ import annotations

import sys
import unittest
from fractions import Fraction as F
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import verify as a


class LimitingGainTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tau, cls.orbit = a.v.isolate_model()
        cls.x = {j: -cls.orbit[j] for j in (1, 2, 3, 4, 5)}
        cls.alpha = -(a.ONE - (a.ONE - a.I.point(4) * cls.tau).sqrt()) / a.TWO

    def test_strict_tail_rational_direction(self):
        self.assertEqual(2 / F(63, 50) - 1 / F(2, 3), F(11, 126))
        self.assertGreater(a.TAIL_GAIN_FLOOR, 0)
        # Equality of paired serial rectangles gives zero, not gain.
        parent, child = F(1, 2), F(1)
        self.assertEqual(2 / child - 1 / parent, 0)

    def test_parent_crossed_electrodes_rejected(self):
        x = self.x
        with self.assertRaises(AssertionError):
            a.parent_angle_data(x[1], x[2], x[3], x[5])

    def test_source_misordered_electrodes_rejected(self):
        x = self.x
        with self.assertRaises(AssertionError):
            a.child_halfstrip_width(x[1], x[2], x[5], x[4],
                                    a.I.point(2))

    def test_source_and_target_not_the_same_slit(self):
        x = self.x
        self.assertTrue(x[2].negative() and x[1].positive())
        self.assertTrue((-x[1]).lt(x[2]))  # source extends farther left
        self.assertTrue(x[2].lt(x[5]) and x[5].lt(x[3]))

    def test_left_tip_semidisk_not_allowed_to_hit_tip_seam(self):
        x = self.x
        with self.assertRaises(AssertionError):
            a.parent_semidisk_width(x[1], x[2], x[5], x[3],
                                    F(1, 1))
        with self.assertRaises(AssertionError):
            a.parent_semidisk_width(x[1], x[2], x[5], x[3],
                                    F(3, 1))

    def test_all_p_error_not_before_p13(self):
        with self.assertRaises(AssertionError):
            a.model_positive_boxes(12, self.orbit)

    def test_disk_competitor_and_strip_not_confused(self):
        x = self.x
        w_disk = a.parent_semidisk_width(
            x[1], x[2], x[5], x[3])
        w_strip = a.parent_halfstrip_width(
            x[1], x[2], x[5], x[3])
        self.assertTrue(w_disk.lt(w_strip))
        self.assertTrue(w_disk.gt(a.I.point(F(2, 3))))

    def test_full_certificate(self):
        result = a.certify()
        self.assertGreater(result["limit_defect_lower"].low(), F(696, 1000))
        self.assertLess(result["limit_defect_upper"].high(), F(793, 1000))
        self.assertGreater(result["all_p_parent_disk_lower"].low(), F(2, 3))


if __name__ == "__main__":
    unittest.main()
