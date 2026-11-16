#!/usr/bin/env python3
"""Adversarial gate, homotopy/deck, reciprocal, and source-metric tests."""
from __future__ import annotations

import importlib.util
import json
import sys
import unittest
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("finite_wave_gain_test_subject", HERE/"verify.py")
assert spec is not None and spec.loader is not None
a = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = a
spec.loader.exec_module(a)


class FiniteWaveGainHostileTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        old = json.loads(a.gain.s.OLD.read_text())
        cls.cases = {row["p"]: a.v.checked_packet(row) for row in old["periods"]}

    def physical_chart(self, p):
        _, _, orbit = self.cases[p]
        return a.physical_positive_chart(p, orbit)

    def test_rational_defect_margins_and_directions(self):
        for p in (3, 4, 5, 12):
            p0, c, x = self.cases[p]
            out = a.finite_case(p0, c, x)
            self.assertEqual(out["proved_D_gt"], str(a.GAIN_FLOORS[p]))
            self.assertGreater(2/a.CHILD_CEILINGS[p]-1/a.PARENT_FLOORS[p],
                               a.GAIN_FLOORS[p])
            # The defect is TWO child inverses minus ONE parent inverse.
            self.assertLess(1/a.CHILD_CEILINGS[p]-1/a.PARENT_FLOORS[p], 0)

    def test_wrong_physical_scale_is_rejected(self):
        _, _, orbit = self.cases[3]
        x = orbit.copy()
        x[1] = -x[1]
        with self.assertRaises(AssertionError):
            a.physical_positive_chart(3, x)

    def test_inverted_target_cuts_rejected(self):
        x, _ = self.physical_chart(3)
        bad = dict(x)
        bad[2], bad[5] = bad[5], bad[2]
        with self.assertRaises(AssertionError):
            a.circular_segment_width(bad, F(83,100), F(31,10))

    def test_segment_below_last_electrode_rejected(self):
        x, _ = self.physical_chart(3)
        with self.assertRaises(AssertionError):
            a.circular_segment_width(x, F(83,100), F(1))

    def test_segment_deck_seam_rejected(self):
        x, _ = self.physical_chart(3)
        with self.assertRaises(AssertionError):
            a.circular_segment_width(x, F(83,100), F(4))

    def test_segment_negative_height_rejected(self):
        x, _ = self.physical_chart(4)
        with self.assertRaises(AssertionError):
            a.circular_segment_width(x, F(-1,10), F(31,10))

    def test_wrongly_overextended_disk_rejected(self):
        x, rad = self.physical_chart(3)
        with self.assertRaises(AssertionError):
            a.verify_full_target_disk(x, rad, F(1))

    def test_semidisk_electrode_and_deck_rejected(self):
        x, _ = self.physical_chart(5)
        with self.assertRaises(AssertionError):
            a.lim.parent_semidisk_width(x[1], x[2], x[5], x[3], F(1))
        with self.assertRaises(AssertionError):
            a.lim.parent_semidisk_width(x[1], x[2], x[5], x[3], F(4))

    def test_source_exclusion_does_not_fabricate_energy(self):
        _, c, orbit = self.cases[3]
        p=3
        alpha = a.v.alpha_interval(p, c, orbit)
        xp, x2, x5, x4 = [orbit[j*p] for j in (1,2,5,4)]
        with self.assertRaises(AssertionError):
            a.strict_child_domain_cap(p, a.I.point(F(1,100)),
                                       x2, x5, x4, alpha)
        cap, plane = a.strict_child_domain_cap(p, xp, x2, x5, x4, alpha)
        self.assertTrue(cap.lt(plane))
        self.assertGreater(cap.low(), 0)

    def test_period_specific_missing_box_gate(self):
        # Regression for the original incorrect fixed 2<s<3 exclusion:
        # p=12 needs 7<s<8, while p=3 can use 2<s<3.
        expected = {3: 2, 4: 2, 5: 2, 6: 3, 7: 4,
                    8: 4, 9: 5, 10: 6, 11: 6, 12: 7}
        for p, start in expected.items():
            _, _, x = self.cases[p]
            self.assertEqual(a.source_missing_box_start(p, x[p]), start)
        with self.assertRaises(AssertionError):
            a.source_missing_box_start(12, a.I.point(F(1, 10**15)))

    def test_child_order_reversal_rejected(self):
        p,c,orbit = self.cases[4]
        alpha=a.v.alpha_interval(p,c,orbit)
        xp,x2,x5,x4=[orbit[j*p] for j in (1,2,5,4)]
        with self.assertRaises(AssertionError):
            a.strict_child_domain_cap(p,xp,x5,x2,x4,alpha)

    def test_no_all_p_box_in_finite_packet(self):
        _, _, orbit = self.cases[5]
        with self.assertRaises(AssertionError):
            a.lim.model_positive_boxes(5, orbit)

    def test_immersion_not_cover(self):
        self.assertEqual(a.gain.s.BLOCKS[0], (18,19,0,1,2))
        self.assertEqual(a.gain.s.BLOCKS[1], (3,4))
        self.assertEqual(a.gain.s.BLOCKS[9], (16,17))
        self.assertEqual([j%10 for j in (1,17,18,19)], [1,7,8,9])
        self.assertNotEqual((18,19,0,1,2), (0,10))


if __name__ == "__main__":
    unittest.main()
