"""Hostile tests for exact geometric exclusions; never a q_gamma evaluator."""
from __future__ import annotations

import importlib.util
import json
import sys
import unittest
from fractions import Fraction as F
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("tip_buffered_under_test",
                                              HERE / "verify.py")
assert spec is not None and spec.loader is not None
v = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = v
spec.loader.exec_module(v)


class BufferedWadTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        # Run the complete selected-packet and all-p upstream proof replay once.
        cls.report = v.certify()

    def test_periods_and_exhaustive_endpoint_type_reduction(self):
        rows = self.report["p3_to_p12"]
        self.assertEqual([r["p"] for r in rows], list(range(3, 13)))
        for row in rows:
            self.assertEqual(row["all_outer_incident_q_strictly_less_than_2"],
                             row["p"] >= 11)
            self.assertEqual(row["candidate_endpoint_types_remaining"],
                             6 if row["p"] >= 11 else 10)
            self.assertTrue(row["inner_three_collars_verified"])
            self.assertGreater(F(row["outer_cyclic_hyperbolic_length_strict_upper"]), 0)
        self.assertTrue(self.report["tail_all_p_ge_13"]
                        ["all_outer_incident_q_strictly_less_than_2"])
        self.assertEqual(self.report["tail_all_p_ge_13"]
                         ["candidate_endpoint_types_remaining"], 6)

    def test_algebraic_threshold_and_bad_length_cutoffs(self):
        v.elliptic_threshold_finite_logic()
        v.check_cyclic_exclusion(F(349, 100), F(7, 2))
        v.check_cyclic_exclusion(F(299, 100), F(3))
        for upper, limit in ((F(7, 2), F(7, 2)), (F(4), F(7, 2)),
                             (F(3), F(3)), (F(0), F(3)),
                             (F(299, 100), F(4))):
            with self.subTest(upper=upper, limit=limit):
                with self.assertRaises(AssertionError):
                    v.check_cyclic_exclusion(upper, limit)

    def test_reject_false_carrier_and_k0_collar(self):
        finite = v.load_verifier("tip_family_finite_p_wave_gain_20261116",
                                 "tip_buffered_finite_negative")
        prior = json.loads(v.OLD.read_text())
        p, xi, R = v.chart_for_finite(finite, prior["periods"][0])
        self.assertEqual(p, 3)
        with self.assertRaises(AssertionError):
            v.ellipse_check(xi, R, "outer", F(10000))
        # The earlier one-hole t=21 capacity ellipse invades K2:
        # it is NOT an embedded K0 collar on the three-hole surface.
        with self.assertRaises(AssertionError):
            v.ellipse_check(xi, R, "K0", F(21))
        v.ellipse_check(xi, R, "K0", F(11))
        v.ellipse_check(xi, R, "outer", F(23, 10))

    def test_reject_bad_marking_and_nonpositive_t(self):
        finite = v.load_verifier("tip_family_finite_p_wave_gain_20261116",
                                 "tip_buffered_finite_wrong_marking")
        prior = json.loads(v.OLD.read_text())
        _, xi, R = v.chart_for_finite(finite, prior["periods"][0])
        mutated = dict(xi)
        mutated[2], mutated[5] = mutated[5], mutated[2]
        with self.assertRaises(AssertionError):
            v.check_order(mutated)
        for t in (F(1), F(-1)):
            with self.assertRaises(AssertionError):
                v.ellipse_check(xi, R, "outer", t)
        with self.assertRaises(AssertionError):
            v.ellipse_check(xi, R, "nonexistent", F(2))

    def test_tail_elliptic_premises_and_no_positive_claim(self):
        self.assertLess(
            F(self.report["tail_all_p_ge_13"]
              ["outer_cyclic_hyperbolic_length_strict_upper"]), F(3))
        for row in self.report["p3_to_p12"]:
            if row["p"] >= 11:
                self.assertLess(
                    F(row["outer_cyclic_hyperbolic_length_strict_upper"]),
                    F(7, 2))
        self.assertEqual(F(self.report["uniform_p_ge_11_canonical_norm_strict_upper"]),
                         F(619, 200))
        self.assertFalse(self.report["all_classes_enumerated"])
        self.assertFalse(self.report["any_inner_q_two_sided_certified"])
        self.assertFalse(self.report["any_positive_canonical_weight_certified"])
        self.assertEqual(self.report["numerical_only"], [])


if __name__ == "__main__":
    unittest.main()
