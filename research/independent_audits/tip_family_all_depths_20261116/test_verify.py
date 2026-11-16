"""Adversarial arithmetic and chart checks for the *single* depth-three packet."""
import unittest
from fractions import Fraction as Q

from verify import (SEED, CHART, S, BLOCKS, Interval, check_marked_tables,
                    gap, iterate, plane_sandwich_upper, verify)


class DepthThreeTests(unittest.TestCase):
    def test_strict_case(self):
        p = verify()
        self.assertGreater(p['rouche1'], Q(1,25))
        self.assertGreater(p['rouche2'], Q(0))
        self.assertGreater(p['rouche3'], Q(0))
        self.assertGreater(p['normalized_third'], Q(1,8))
        self.assertGreater(p['radial_width_lower'], Q(1,4))
        self.assertLess(p['plane_width_upper'], Q(31,40))
        self.assertLess(p['radial_width_lower'], p['plane_width_upper'])

    def test_rational_intervals_do_not_use_round_to_nearest(self):
        a = Interval.point(Q(1,3))
        b = Interval.point(Q(-7,5))
        v = a*b
        expected = Q(-7,15)
        self.assertLessEqual(Q(v.lo,S), expected)
        self.assertGreaterEqual(Q(v.hi,S), expected)
        self.assertEqual(Interval.hull(Q(-1,3),Q(2,7)).square().lo, 0)
        with self.assertRaisesRegex(AssertionError, 'divide by zero'):
            _ = a/Interval.hull(-1,1)

    def test_seed_is_locator_not_assumed_root(self):
        # An exact seed perturbation much larger than the rational chart must fail.
        with self.assertRaisesRegex(AssertionError, 'no isolated depth-three tip'):
            verify(seed=str(Q(SEED)+Q(1,10**20)))

    def test_wrong_rough_chart(self):
        with self.assertRaises(AssertionError):
            verify(chart=Q(1,10**4))

    def test_missing_tuning_kneading_or_wrong_tip(self):
        # A different P_27 root near the parent is not the selected nested tip.
        centre = '-1.786440067359078678693913478552859411239007999152440269'
        with self.assertRaises(AssertionError):
            verify(seed=centre,chart=Q(1,10**35))

    def test_cover_vs_immersion_mutation(self):
        wrong=list(BLOCKS)
        wrong[1],wrong[2] = wrong[2],wrong[1]
        with self.assertRaisesRegex(AssertionError, 'immersion target partition'):
            check_marked_tables(tuple(wrong))

    def test_rouche_would_fail_on_small_disk(self):
        s=Q(SEED)
        x,_,a=iterate(Interval.hull(s-CHART,s+CHART),162)
        self.assertLess(gap(x,a,27,Q(1,10000)),0)

    def test_upper_bound_uses_actual_two_cuts(self):
        y=[Interval.point(0) for _ in range(7)]
        with self.assertRaises(AssertionError):
            plane_sandwich_upper(y)


if __name__ == '__main__':
    unittest.main()

# End of depth-three adversarial tests.
