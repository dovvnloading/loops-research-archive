"""Adversarial regressions: quantitative inner bounds must not claim support."""
from __future__ import annotations

import importlib.util
import json
import sys
import unittest
from fractions import Fraction as F
from pathlib import Path

PATH = Path(__file__).with_name('verify.py')
spec = importlib.util.spec_from_file_location('wad_inner_under_test', PATH)
assert spec is not None and spec.loader is not None
v = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = v
spec.loader.exec_module(v)


class InnerBufferedWadTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.proof = v.certify()

    def test_three_upper_side_classes_each_period(self):
        entries = self.proof['finite_p3_to_p12']
        self.assertEqual([row['p'] for row in entries], list(range(3,13)))
        for row in entries + [self.proof['all_p_ge_13']]:
            lower = row['three_direct_inner_classes']
            self.assertEqual(set(lower), {'K2-K0', 'K0-K1', 'K2-K1'})
            for data in lower.values():
                self.assertGreater(F(data['certified_direct_class_q_strict_lower']), 0)
                self.assertLess(F(data['certified_direct_class_q_strict_lower']), 2)
                self.assertFalse(data['buffered_weight_positive_certified'])

    def test_every_inner_type_upper_and_returning_count(self):
        self.assertEqual(v.type_caps(), {
            'K0-K0': str(F(2)+v.old.INNER_B['K0']/2),
            'K0-K1': '5/2', 'K0-K2': '57/20',
            'K1-K1': '5/2', 'K1-K2': '5/2', 'K2-K2': '57/20',
        })
        self.assertEqual(self.proof['support_cardinality_upper_by_KKL'], 10)
        self.assertFalse(self.proof['support_classes_effectively_enumerated'])
        self.assertFalse(self.proof['any_inner_q_shown_greater_than_2'])
        self.assertFalse(self.proof['any_positive_canonical_weight_certified'])
        self.assertFalse(self.proof['norm_vanishing_certified'])

    def test_replay_all_p_physical_collars_and_norms(self):
        for row in self.proof['finite_p3_to_p12']:
            self.assertGreater(F(row['canonical_norm_nonnegative_strict_upper']), 0)
            self.assertEqual(row['outer_incident_excluded'], row['p']>=11)
            if row['p']>=11:
                self.assertEqual(F(row['canonical_norm_nonnegative_strict_upper']), F(619,200))
        self.assertEqual(F(self.proof['all_p_ge_13']
                          ['canonical_norm_nonnegative_strict_upper']),F(619,200))
        self.assertTrue(self.proof['all_p_ge_13']['outer_incident_excluded'])
        self.assertEqual(self.proof['numerical_only'], [])

    def test_false_sqrt_and_elliptic_cutoff_rejected(self):
        self.assertLess(v.sqrt_floor(F(2))**2, F(2))
        with self.assertRaises(AssertionError):
            v.sqrt_floor(F(-1))
        with self.assertRaises(AssertionError):
            v.agm_lower(F(0))
        quad = v.old.load_verifier('canonical_wad_quadrilateral_moduli_20261116',
                                   'wad_inner_bad_quad')
        for t,r,cap in ((F(2),F(1,62),F(351,100)),
                        (F(11),F(1,62),F(3)),
                        (F(49),F(1,2),F(5,2))):
            with self.subTest(t=t,r=r,cap=cap),self.assertRaises(AssertionError):
                v.prove_q_cap(quad, 'K0', t,r,cap)

    def test_bad_surface_or_crossratio_rejected(self):
        finite=v.old.load_verifier('tip_family_finite_p_wave_gain_20261116',
                                    'wad_inner_negative_finite')
        packets=json.loads(v.old.OLD.read_text())['periods']
        _,xi,R=v.old.chart_for_finite(finite, packets[0])
        v.direct_subquadrilaterals(xi,R.low())
        with self.assertRaises(AssertionError):
            v.direct_subquadrilaterals(xi,F(1,1000000))
        fake=dict(xi)
        fake[2],fake[5]=fake[5],fake[2]
        with self.assertRaises(AssertionError):
            v.direct_subquadrilaterals(fake,R.low())
        with self.assertRaises(AssertionError):
            v.strict_root_fourth_floor(F(0))

    def test_strict_rational_rounding(self):
        self.assertEqual(v.strict_ceiling(F(3,2),1000),F(1501,1000))
        self.assertGreater(v.strict_ceiling(F(1,3)), F(1,3))
        for n in (1,2,15):
            s=F(n,100)**4+F(1,10**20)
            self.assertLess(v.strict_root_fourth_floor(s)**4,s)


if __name__=='__main__':
    unittest.main()
