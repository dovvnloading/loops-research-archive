"""Adversarial regression checks for universal tip lemmas (pure standard library)."""
import sys
import unittest
from fractions import Fraction as Q
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parent))
import verify as v


class AllPeriodProofChecks(unittest.TestCase):
    def test_boundary_constants(self):
        self.assertIn('Rouche_margin_lower_at_13', v.verify_universal_constants())

    def test_strict_normalized_cuts(self):
        self.assertEqual(v.verify_model_and_cut_order()['strict_source_cut_count'], '12')

    def test_whole_kneading_window_exclusion(self):
        self.assertEqual(v.verify_whole_kneading_window()['wrong_kneading_windows'], '3')

    def test_adversarial_other_root_wrong_sign(self):
        u, _ = v.model(Q('-1.894'), Q('-1.892'))
        self.assertLess(u[5].hi, 0)  # -1.89291 is a real root, wrong return sign.

    def test_p13_adjacent_root_and_falsified_shift(self):
        v.verify_period13_bracket()
        wrong_left = v.P13_at(v.N13+1)[0]
        wrong_right = v.P13_at(v.N13+2)[0]
        self.assertLess(wrong_left.hi, 0)
        self.assertLess(wrong_right.hi, 0)


if __name__ == '__main__':
    unittest.main()
