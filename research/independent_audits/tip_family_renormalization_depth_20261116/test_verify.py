"""Adversarial checks: mutations must not turn into positive certificates."""
import unittest
from fractions import Fraction as Q
from verify import (I, BLOCKS, SEEDS, MATRIX, proper_atom_tables, rouche_gap,
                    orbit, verify_case, qplane_bounds, log_bounds)


class DepthAuditTests(unittest.TestCase):
    def test_all_nine_strict_enclosures(self):
        for p1 in (3, 4, 5):
            for p2 in (3, 4, 5):
                with self.subTest(p1=p1, p2=p2):
                    r = verify_case(p1, p2)
                    self.assertGreater(r['rouche1'], Q(1, 1000))
                    self.assertGreater(r['rouche2'], Q(1, 10000))
                    self.assertGreater(r['rouche3_normalized_lower'], Q(1, 8))
                    self.assertGreater(r['radial'][0], Q(1, 4))
                    self.assertLess(r['qplane'][1], Q(31, 40))
                    self.assertLess(r['radial'][1], r['qplane'][0])

    def test_seeds_not_treated_as_exact_roots(self):
        with self.assertRaises(AssertionError):
            verify_case(3, 3, seed='-1.7864415279')
        with self.assertRaises(AssertionError):
            verify_case(5, 5, seed=str(Q(SEEDS[5, 5])+Q(1, 10**12)))

    def test_false_period_three_centre_or_wrong_branch(self):
        # The adjacent wrong branch must not be accepted just because P_n=0.
        with self.assertRaises(AssertionError):
            verify_case(3, 3, seed='-1.78651054454432475738526')

    def test_pulled_blocks_are_not_covering(self):
        proper_atom_tables()
        mutated=list(BLOCKS)
        mutated[0]=(18, 19, 0, 1)
        with self.assertRaises(AssertionError):
            proper_atom_tables(tuple(mutated))
        mutated=list(BLOCKS)
        mutated[4]=(7, 8, 11)
        with self.assertRaises(AssertionError):
            proper_atom_tables(tuple(mutated))

    def test_non_exact_interval_sqrt_and_zero_division(self):
        i=I.hull(Q(-1, 100), Q(1, 100))
        self.assertEqual(i.square().lo, 0)
        self.assertGreater(i.square().hi, 0)
        with self.assertRaises(AssertionError):
            i.reciprocal()
        with self.assertRaises(AssertionError):
            log_bounds(Q(99, 100))

    def test_boundary_margin_fails_if_radius_wrong(self):
        c=I.hull(Q(SEEDS[3, 3])-Q(1,10**80),Q(SEEDS[3,3])+Q(1,10**80))
        x,_,a=orbit(c,6*3*3)
        self.assertLess(rouche_gap(x,a,9,Q(1,10000)),0)

    def test_no_unsupported_chart(self):
        with self.assertRaises(AssertionError):
            verify_case(6, 3)


if __name__ == '__main__':
    unittest.main()
