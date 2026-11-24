"""Adversarial finite checks; never mutate predecessor files."""
from __future__ import annotations

import copy
import unittest
from fractions import Fraction as F

import verify as audit


def synthetic_rows() -> list[dict]:
    rows = []
    for p, (floor, ceiling, gain) in audit.FLOORS.items():
        rows.append({
            "p": p,
            "construction": ("right-circular-segment" if p < 5
                             else "right-semidisk"),
            "proved_parent_gt": str(floor),
            "proved_child_lt": str(ceiling),
            "proved_D_gt": str(gain),
            "parent_competitor_strict_1e-6": [700000, 700001],
            "child_actual_upper_strict_1e-6": [900000, 900001],
            "child_plane_upper_strict_1e-6": [950000, 950001],
            "defect_strict_lower_1e-6": [500000, 500001],
        })
    return rows


class MarkingTests(unittest.TestCase):
    def test_correct_discrete_tables(self):
        audit.check_marking()
        self.assertEqual([audit.span(20, *x)
                          for x in (*audit.CROSSING, audit.AVOIDING)],
                         [3, 3, 7])

    def test_wraparound_and_endpoints(self):
        self.assertEqual(audit.span(10, 9, 1), 3)
        self.assertEqual(audit.span(20, 19, 17), 3)
        self.assertEqual(audit.span(20, 3, 17), 7)
        for args in [(10, 0, 0), (10, -1, 2), (10, 2, 10),
                     (2, 0, 1), (20, 3.0, 17)]:
            with self.subTest(args=args), self.assertRaises(AssertionError):
                audit.span(*args)

    def test_reject_attachment_mutation(self):
        bad = dict(audit.BLOCKS)
        bad[0] = (18, 19, 0, 1, 3)
        with self.assertRaises(AssertionError):
            audit.check_marking(bad)

    def test_reject_covering_as_immersion(self):
        bad = {i: (i, i + 10) for i in range(10)}
        with self.assertRaises(AssertionError):
            audit.check_marking(bad)

    def test_reject_missing_ideal_atom(self):
        bad = dict(audit.BLOCKS)
        bad.pop(9)
        with self.assertRaises(AssertionError):
            audit.check_marking(bad)


class RationalImplicationTests(unittest.TestCase):
    def test_rational_tail_not_decimal(self):
        self.assertEqual(audit.check_tail_floor(), F(40, 819))
        self.assertGreater(F(40, 819), F(1, 100))

    def test_tightened_or_wrong_tail_rejected(self):
        for parent, child in [(F(2, 3), F(3, 2)),
                              (F(2, 3), F(63, 50)),
                              (F(3, 4), F(63, 50)),
                              (F(0), F(63, 50))]:
            with self.subTest(parent=parent, child=child):
                with self.assertRaises(AssertionError):
                    audit.check_tail_floor(parent, child)

    def test_finite_report_strict_success(self):
        audit.check_finite_report(synthetic_rows())

    def test_reject_12_13_gap(self):
        rows = synthetic_rows()
        rows[-1]["p"] = 13
        with self.assertRaises(AssertionError):
            audit.check_finite_report(rows)

    def test_reject_duplicate_period(self):
        rows = synthetic_rows()
        rows[1]["p"] = 3
        with self.assertRaises(AssertionError):
            audit.check_finite_report(rows)

    def test_reject_unembedded_p3_parent(self):
        rows = synthetic_rows()
        rows[0]["construction"] = "right-semidisk"
        with self.assertRaises(AssertionError):
            audit.check_finite_report(rows)

    def test_reject_wrong_reciprocal_sign_or_cap(self):
        rows = synthetic_rows()
        rows[0]["proved_child_lt"] = "99/100"
        with self.assertRaises(AssertionError):
            audit.check_finite_report(rows)
        rows = synthetic_rows()
        rows[0]["parent_competitor_strict_1e-6"] = [489999, 490000]
        with self.assertRaises(AssertionError):
            audit.check_finite_report(rows)

    def test_reject_non_strict_interval(self):
        rows = synthetic_rows()
        rows[1]["defect_strict_lower_1e-6"] = [70000, 70000]
        with self.assertRaises(AssertionError):
            audit.check_finite_report(rows)

    def test_reject_failure_of_positive_gain(self):
        rows = synthetic_rows()
        rows[2]["defect_strict_lower_1e-6"] = [1000, 1001]
        with self.assertRaises(AssertionError):
            audit.check_finite_report(rows)


if __name__ == "__main__":
    unittest.main()
