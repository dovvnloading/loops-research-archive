#!/usr/bin/env python3
"""Adversarial regression tests: disallow unjustified gain and typed-map errors."""
import unittest
from fractions import Fraction as F
import verify as g


class CanonicalGainTests(unittest.TestCase):
    def test_parallel_serial_and_round_equality_coefficients(self):
        # A rectangle of width L and heights h1,h2 gives W=L/(h1+h2),
        # W1=L/h1, W2=L/h2, with reciprocal equality.
        L, h1, h2 = F(7,3),F(5,4),F(2,3)
        parent=L/(h1+h2)
        c1,c2=L/h1,L/h2
        self.assertEqual(1/c1+1/c2-1/parent,0)
        # A positive third serial slab gives strict *loss*, never gain.
        h3=F(1,11)
        self.assertLess(1/c1+1/c2-1/(L/(h1+h2+h3)),0)
        self.assertGreater(c1+c2,c1)  # disjoint parallel conductances add

    def test_bound_direction_and_sign_not_assumed(self):
        lo,hi=g.defect_bounds(F(1,4),F(3,4),F(6,5))
        self.assertLess(lo,0)
        self.assertGreater(hi,0)
        with self.assertRaises(AssertionError):
            g.defect_bounds(F(0),F(1),F(3))
        with self.assertRaises(AssertionError):
            g.defect_bounds(F(2),F(1),F(3))
        with self.assertRaises(AssertionError):
            g.defect_bounds(F(1,4),F(3,4),F(1,4))

    def test_wrong_cross_ratio_rejected(self):
        i=g.v.Iv.point
        with self.assertRaises(AssertionError):
            g.child_crossratio(i(1),i(3),i(2),i(4))
        with self.assertRaises(AssertionError):
            g.child_crossratio(i(1),i(1),i(2),i(4))

    def test_source_cut_and_identity_immersion_not_cover(self):
        blocks=g.s.BLOCKS
        self.assertEqual(blocks[0],(18,19,0,1,2))
        self.assertEqual(blocks[1],(3,4))
        self.assertEqual(blocks[9],(16,17))
        self.assertEqual([3%10,1%10],[3,1])
        self.assertEqual([19%10,17%10],[9,7])
        self.assertEqual(g.s.cyclic_span((3,17),20),7)
        self.assertEqual(g.s.cyclic_span((3,7),10),5)
        # The cover table cannot be used to test source eligibility:
        self.assertNotEqual(19%10,19)
        self.assertEqual(g.s.check_marking()["source_crossing_spans"],[3,3])

    def test_model_rejects_unproved_low_periods(self):
        _,u=g.v.isolate_model()
        with self.assertRaises(AssertionError):
            g.model_child_envelope(12,u)
        with self.assertRaises(AssertionError):
            g.pad(g.v.ZERO,F(-1))
        cap=g.model_child_envelope(13,u)
        self.assertLess(cap.high(),g.TAIL_CHILD_CAP)
        self.assertGreater(cap.low(),F(1))

    def test_all_defect_intervals_explicitly_straddle_zero(self):
        self.assertEqual(sorted(g.DEFECT_3_TO_12),list(range(3,13)))
        self.assertTrue(all(a<0<b for a,b in g.DEFECT_3_TO_12.values()))
        self.assertLess(g.TAIL_DEFECT[0],0)
        self.assertGreater(g.TAIL_DEFECT[1],0)


if __name__ == "__main__":
    unittest.main()
