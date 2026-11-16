"""Adversarial mutation tests for the additive three-return certificate."""
import copy
import json
import unittest

import verify


class ThreeReturnProofTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.raw = verify.FINITE.read_bytes()
        cls.data = json.loads(cls.raw)

    def test_all_ten_original_brackets_and_analytic_bound(self):
        self.assertEqual(len(verify.check_all_finite(self.data)), 10)
        self.assertTrue(verify.check_large_model()["H_three_return_Rouche_margin_gt_1/8"])
        self.assertEqual(self.raw, verify.FINITE.read_bytes(), "source was modified")

    def test_wrong_root_rejected(self):
        row = copy.deepcopy(self.data["periods"][6])  # p=9, wrong-root hazard
        row["parameter_bracket"]["lower_numerator"] += 10**25
        row["parameter_bracket"]["upper_numerator"] += 10**25
        with self.assertRaises(AssertionError):
            verify.check_finite_row(row)

    def test_broken_adjacent_bracket_rejected(self):
        row = copy.deepcopy(self.data["periods"][0])
        row["parameter_bracket"]["upper_numerator"] += 1
        with self.assertRaisesRegex(AssertionError, "adjacent"):
            verify.check_finite_row(row)

    def test_missing_or_repeated_period_rejected(self):
        data = copy.deepcopy(self.data)
        data["periods"][3] = data["periods"][2]
        with self.assertRaisesRegex(AssertionError, "missing, repeated"):
            verify.check_all_finite(data)

    def test_missing_degree_two_certificate_rejected(self):
        row = copy.deepcopy(self.data["periods"][2])
        row["central_degree_two_Rouche_margin_lower_2^-64"] = "0"
        with self.assertRaisesRegex(AssertionError, "prior original"):
            verify.check_finite_row(row)

    def test_avoiding_seven_not_three(self):
        data = copy.deepcopy(self.data)
        data["source_avoiding_short_arc_atoms"] = 3
        with self.assertRaisesRegex(AssertionError, "short-arc correction"):
            verify.check_all_finite(data)


if __name__ == "__main__":
    unittest.main()
