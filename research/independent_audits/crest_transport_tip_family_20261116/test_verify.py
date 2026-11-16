"""Negative controls for the full-radius exact crest transport checker."""
import unittest
from fractions import Fraction as F
import verify as v

class CrestTransportAdversarial(unittest.TestCase):
    def test_interval_square_and_multiplication(self):
        a=v.I.hull(F(-1),F(2))
        self.assertEqual(a.square().low(),0)
        b=v.I.hull(F(-3),F(4))
        self.assertLessEqual((a*b).low(),F(-6))
        self.assertGreaterEqual((a*b).high(),F(8))

    def test_pi_and_log_outwardness(self):
        lower,upper=v.pi_bounds()
        self.assertLess(lower,upper)
        for q in [F(4,3),F(3,2),F(7,4)]:
            lo,hi=v.log_interval(q)
            self.assertLess(lo,hi)
        self.assertLess(v.atan_interval(F(1,5))[0],v.atan_interval(F(1,5))[1])

    def test_shifted_tip_root_is_rejected(self):
        original=v.PARAMETER[3]
        try:
            v.PARAMETER[3]=original+1
            with self.assertRaises(AssertionError):v.parameter(3)
        finally:v.PARAMETER[3]=original

    def test_broken_immersion_blocks_are_rejected(self):
        original=v.BLOCKS[0][0]
        try:
            v.BLOCKS[0][0]=17
            c,x=v.parameter(3);alpha=v.alpha_root(c,3,x)
            with self.assertRaises(AssertionError):v.actions_from_physical_cuts(c,3,x,alpha)
        finally:v.BLOCKS[0][0]=original

    def test_wrong_large_radius_rejected(self):
        original=v.COLLARS[8]
        try:
            v.COLLARS[8]=(F(1,16),F(1,15))
            with self.assertRaises(AssertionError):v.run(8,64)
        finally:v.COLLARS[8]=original

    def test_nonmonotone_false_gate_rejected(self):
        c,x=v.parameter(3)
        with self.assertRaises(AssertionError):
            v.monotonicity(v.I.point(0),v.I.point(F(1,50)),c,3)

    def test_full_p3_certificate_recovers_stronger_than_half(self):
        out=v.run(3,512)
        self.assertGreater(F(out['certified_ratio_lower']),F(1,2))
        self.assertLess(F(out['certified_ratio_lower']),F(out['certified_ratio_upper']))

if __name__=='__main__':unittest.main()
