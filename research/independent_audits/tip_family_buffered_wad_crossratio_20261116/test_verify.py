"""Hostile exact-arithmetic regressions for physical/ideal cross-ratio separation."""
import importlib.util
import sys
import unittest
from fractions import Fraction as Q
from pathlib import Path

PATH=Path(__file__).with_name('verify.py')
spec=importlib.util.spec_from_file_location('crossratio_under_test', PATH)
assert spec is not None and spec.loader is not None
v=importlib.util.module_from_spec(spec)
sys.modules[spec.name]=v
spec.loader.exec_module(v)


class SyntheticInterval:
    def __init__(self,lo,hi):
        self.lo=Q(lo); self.hi=Q(hi)
    def low(self): return self.lo
    def high(self): return self.hi


class ExactArithmeticTests(unittest.TestCase):
    def test_threshold_algebraic_not_double(self):
        self.assertEqual(v.threshold_sign(Q(26,27)), -1)
        self.assertEqual(v.threshold_sign(Q(99,100)),1)
        with self.assertRaises(AssertionError): v.threshold_sign(Q(0))
        with self.assertRaises(AssertionError): v.threshold_sign(Q(1))
        with self.assertRaises(AssertionError): v.threshold_sign(0.975)

    def test_integer_sqrt_outward_and_AGM(self):
        self.assertEqual(v.sqrt_bounds(Q(1,4)),(Q(1,2),Q(1,2)))
        a,b=v.sqrt_bounds(Q(2))
        self.assertLess(a*a, Q(2)); self.assertGreater(b*b, Q(2))
        self.assertLessEqual(b-a,Q(1,1<<v.BITS))
        aglo,aghi=v.agm_bounds(Q(1,2),Q(1,2))
        self.assertLess(aglo,aghi)
        elo,ehi=v.elliptic_E_bounds(Q(1,2))
        self.assertLess(elo,1);self.assertGreater(ehi,1)
        with self.assertRaises(AssertionError):v.elliptic_E_bounds(Q(1))
        with self.assertRaises(AssertionError):v.agm_bounds(Q(-1),Q(1,2))
        with self.assertRaises(AssertionError):v.sqrt_bounds(Q(-1))

    def test_cancellation_identity_radius_monotonicity(self):
        a,b,c,d=map(Q,(-8,-4,3,7))
        s1=v.halfdisk_crossratio(a,b,c,d,Q(10))
        s2=v.halfdisk_crossratio(a,b,c,d,Q(20))
        s3=v.halfdisk_crossratio(a,b,c,d,None)
        self.assertTrue(0<s1<s2<s3<1)
        self.assertEqual(s1,v.standard_crossratio(*[v.t_halfdisk(x,Q(10)) for x in (a,b,c,d)]))
        with self.assertRaises(AssertionError):v.halfdisk_crossratio(a,b,c,d,Q(7))
        with self.assertRaises(AssertionError):v.standard_crossratio(b,a,c,d)
        with self.assertRaises(AssertionError):v.t_halfdisk(Q(10),Q(10))

    def test_corner_monotonicity_strict(self):
        xi={2:SyntheticInterval(-8,-Q(79,10)),
            5:SyntheticInterval(-5,-Q(49,10)),
            3:SyntheticInterval(-1,-Q(9,10)),
            6:SyntheticInterval(1,Q(11,10)),
            4:SyntheticInterval(5,Q(51,10)),
            1:SyntheticInterval(8,Q(81,10))}
        for pair in v.PAIRS:
            result=v.physical_pair_interval(xi,Q(10),Q(11),pair)
            sl,sh=map(Q,result['physical_halfdisk_crossratio_strict_bracket'])
            el,eh=map(Q,result['physical_halfdisk_elliptic_width_strict_bracket'])
            self.assertTrue(0<sl<sh<1)
            self.assertTrue(0<el<eh<2)
            self.assertEqual(v.threshold_sign(sh),-1)
        # Move slit through its neighbor: must reject, not silently reorder.
        xi[3]=SyntheticInterval(-6,-Q(59,10))
        with self.assertRaises(AssertionError):
            v.physical_pair_interval(xi,Q(10),Q(11),('K2','K0'))
        with self.assertRaises(AssertionError):
            v.physical_pair_interval(xi,Q(1),None,('K0','K1'))

    def test_strict_grid_enclosures(self):
        self.assertEqual(v.strict_floor(Q(3,2),1000),Q(1499,1000))
        self.assertEqual(v.strict_ceil(Q(3,2),1000),Q(1501,1000))
        self.assertLess(v.strict_floor(Q(1,3),1000),Q(1,3))
        with self.assertRaises(AssertionError):v.strict_floor(Q(0),1000)


class PinnedPhysicalChartTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.proof=v.certify()

    def test_exactly_these_periods_and_six_types(self):
        self.assertEqual([r['p'] for r in self.proof['finite_p3_to_p12']],list(range(3,13)))
        self.assertEqual(len(self.proof['all_six_inner_type_q_strict_upper']),6)
        self.assertEqual(self.proof['support_cardinality_upper_KKL'],10)
        self.assertFalse(self.proof['effective_deck_word_exclusion'])
        self.assertFalse(self.proof['uniformization_of_actual_four_hole_surface'])

    def test_crossratios_not_pretended_actual_lift_endpoints(self):
        for row in self.proof['finite_p3_to_p12']+[self.proof['all_p_ge_13']]:
            self.assertEqual(set(row['pair_comparison_domains']),
                             {'K2-K0','K0-K1','K2-K1'})
            for pair,d in row['pair_comparison_domains'].items():
                self.assertTrue(d['comparison_upper_is_NOT_true_q_upper'])
                self.assertFalse(d['ideal_lift_endpoints_certified'])
                self.assertFalse(d['q_greater_than_two_certified'])
                l,h=map(Q,d['physical_halfdisk_crossratio_strict_bracket'])
                self.assertTrue(0<l<h<1)
                self.assertEqual(v.threshold_sign(h),-1)
                ql,qh=map(Q,d['physical_halfdisk_elliptic_width_strict_bracket'])
                self.assertTrue(0<ql<qh<2)
                self.assertGreater(Q(d['true_q_strict_upper_from_prior_all_class_cap']),2)
            self.assertGreater(Q(row['canonical_norm_nonnegative_strict_upper']),0)
        self.assertTrue(self.proof['all_p_ge_13']['outer_incident_excluded'])
        self.assertEqual(self.proof['numerical_only'],[])
        self.assertFalse(self.proof['any_positive_canonical_weight_certified'])
        self.assertFalse(self.proof['norm_vanishing_certified'])


if __name__=='__main__':
    unittest.main()
