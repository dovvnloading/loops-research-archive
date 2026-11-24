#!/usr/bin/env python3
"""Regression tests for the versioned Wave-gain correction and its composition."""
from __future__ import annotations

import importlib.util
import sys
import unittest
from unittest.mock import patch
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent


def load_subject(name, filename):
    spec = importlib.util.spec_from_file_location(name, HERE / filename)
    if spec is None or spec.loader is None:
        raise RuntimeError("Cannot import correction test subject")
    subject = importlib.util.module_from_spec(spec)
    sys.modules[name] = subject
    spec.loader.exec_module(subject)
    return subject


a = load_subject("tip_wave_gain_correction_test_subject", "verify.py")
runner = load_subject("tip_wave_gain_correction_runner_test_subject", "verify_all_periods.py")


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
                                    F(22, 7))

    def test_all_p_error_not_before_p13(self):
        with self.assertRaises(AssertionError):
            a.model_positive_boxes(12, self.orbit)

    def test_parent_boxes_include_the_upstream_proved_cut_bounds(self):
        # The upstream child envelope independently uses the same physical
        # cut estimate.  Capture those inputs rather than duplicating its
        # formula: a parent certificate may not silently use smaller errors.
        for p in (13, 14, 64):
            with self.subTest(period=p):
                with patch.object(a.gain, "coarse_child_plane") as envelope:
                    a.gain.model_child_envelope(p, self.orbit)
                parent = a.model_positive_boxes(p, self.orbit)
                for j, required in zip((1, 2, 5, 3), envelope.call_args.args):
                    self.assertLessEqual(parent[j].low(), required.low())
                    self.assertGreaterEqual(parent[j].high(), required.high())

    def test_period13_uses_an_actual_root_not_the_insufficient_tail_box(self):
        full = a.model_positive_boxes(13, self.orbit)
        broad_width = a.parent_semidisk_width(
            full[1], full[2], full[5], full[3])
        self.assertLess(broad_width.low(), a.PARENT_TAIL_FLOOR)
        actual = a.certified_period13_boxes()
        for j in actual:
            self.assertLessEqual(full[j].low(), actual[j].low())
            self.assertGreaterEqual(full[j].high(), actual[j].high())
        actual_width = a.parent_semidisk_width(
            actual[1], actual[2], actual[5], actual[3])
        self.assertGreater(actual_width.low(), a.PARENT_TAIL_FLOOR)
        a.disk_cutoff_certificate(actual)

    def test_corrected_period14_box_proves_the_uniform_tail_floor(self):
        full = a.model_positive_boxes(14, self.orbit)
        width = a.parent_semidisk_width(full[1], full[2], full[5], full[3])
        self.assertGreater(width.low(), a.PARENT_TAIL_FLOOR)

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

    def test_all_periods_composes_corrected_tail_without_historical_aggregates(self):
        # The failure being prevented is concrete: the old finite aggregate
        # always calls the defective historical tail.  This test checks the
        # replacement entrypoint while avoiding a duplicate expensive finite
        # arithmetic run (the runner executes that arithmetic separately).
        tail = object()
        fail_legacy = AssertionError("historical aggregate must not run")
        with patch.object(runner.corrected, "certify", return_value=tail) as current, \
             patch.object(runner.finite, "certify", side_effect=fail_legacy), \
             patch.object(runner.finite.lim, "certify", side_effect=fail_legacy), \
             patch.object(runner.finite.v, "checked_packet",
                          side_effect=lambda row: (row["p"], None, None)) as packets, \
             patch.object(runner.finite, "finite_case",
                          side_effect=lambda p, c, orbit: {"p": p}) as cases:
            result = runner.certify()
        current.assert_called_once_with()
        self.assertIs(result["tail"], tail)
        self.assertEqual([row["p"] for row in result["finite"]], list(range(3, 13)))
        self.assertEqual(packets.call_count, 10)
        self.assertEqual([call.args[0] for call in cases.call_args_list], list(range(3, 13)))


if __name__ == "__main__":
    unittest.main()
