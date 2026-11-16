"""Adversarial tests of rational ellipses, unchanged tip, and no-WAD-claim contract."""
import copy
import json
import unittest
from fractions import Fraction as Q
from verify import (TIP, PARENT, orbit, certify, rect_interval, ellipses,
                    pi_range, log_range, require)


class CollarGuards(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tip = json.loads(TIP.read_text())
        cls.parent = json.loads(PARENT.read_text())
        cls.x = orbit(cls.tip)

    def test_certified_auxiliary_only(self):
        d = certify(self.tip,self.parent)
        self.assertFalse(d['canonical_WAD']['quadrilateral_enclosures_certified'])
        self.assertIsNone(d['canonical_WAD']['support'])
        self.assertIsNone(d['canonical_WAD']['total_weight_certified_bounds'])
        self.assertFalse(d['transfer']['scalar_upper_and_lower_inequality_decided'])
        self.assertFalse(d['transfer']['no_positive_constants_possible_proved'])
        self.assertEqual(set(d['certified_auxiliary_target_slit_outer_condenser_bounds']),{'K0','K1','K2'})

    def test_parameter_change_rejected(self):
        s=copy.deepcopy(self.tip)
        s['source_parameter']['lower_numerator']+=1
        with self.assertRaises(AssertionError):
            orbit(s)

    def test_earlier_audit_change_rejected(self):
        p=copy.deepcopy(self.parent)
        p['geometry']['canonical_small_julia_sets']='K0=[x9,x3]'
        with self.assertRaises(AssertionError):
            certify(self.tip,p)

    def test_too_large_inner_ellipses_rejected(self):
        for name,ends,t in [('K0',(9,18),22),('K1',(12,3),50),('K2',(6,15),26)]:
            with self.subTest(name=name):
                m,a=rect_interval(*[self.x[i] for i in ends])
                with self.assertRaises(AssertionError):
                    ellipses(m,a,t,500)

    def test_too_small_outer_ellipses_rejected(self):
        for name,ends,tin,tout in [('K0',(9,18),20,21),('K1',(12,3),49,300),('K2',(6,15),25,80)]:
            with self.subTest(name=name):
                m,a=rect_interval(*[self.x[i] for i in ends])
                with self.assertRaises(AssertionError):
                    ellipses(m,a,tin,tout)

    def test_transcendental_gaps_are_exact(self):
        p0,p1=pi_range()
        self.assertTrue(log_range(24)[0] > p1)
        self.assertTrue(log_range(22)[1] < p0)
        self.assertTrue(p0 < p1)


if __name__=='__main__':
    unittest.main()
