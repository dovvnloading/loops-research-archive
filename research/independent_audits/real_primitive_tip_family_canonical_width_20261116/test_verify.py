#!/usr/bin/env python3
"""Mutation and interval containment tests; no floating-point proof oracles."""
import copy
import json
import unittest
import verify as v


class CanonicalWidthAuditTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.rows = json.loads(v.OLD.read_text())['periods']

    def test_exact_interval_arithmetic_outward_and_guard(self):
        a = v.Iv.hull(v.Q(1,3),v.Q(2,3))
        b = v.Iv.hull(v.Q(2,7),v.Q(3,7))
        prod=a*b
        self.assertLessEqual(prod.low(), v.Q(2,21))
        self.assertGreaterEqual(prod.high(), v.Q(2,7))
        self.assertTrue(v.Iv.point(2).sqrt().inside(1,2))
        with self.assertRaises(AssertionError):
            (a-b).reciprocal()

    def test_all_finite_brackets_rechecked(self):
        for row in self.rows:
            with self.subTest(p=row['p']):
                p,c,x=v.checked_packet(row)
                self.assertEqual(p,row['p'])
                self.assertTrue((x[6*p]+x[3*p]).lo <= 0 <= (x[6*p]+x[3*p]).hi)

    def test_reject_shifted_dyadic_seed_and_wrong_itinerary(self):
        row=copy.deepcopy(self.rows[-1])
        row['parameter_bracket']['lower_numerator'] += 4
        row['parameter_bracket']['upper_numerator'] += 4
        with self.assertRaises(AssertionError):
            v.checked_packet(row)
        row=copy.deepcopy(self.rows[2])
        row['parameter_bracket']['upper_numerator'] += 1
        with self.assertRaises(AssertionError):
            v.checked_packet(row)

    def test_model_root_and_full_lift_are_distinct(self):
        tau,u=v.isolate_model()
        self.assertTrue(tau.inside(v.MODEL_LO,v.MODEL_HI))
        pi=v.pi_interval()
        inf,_,_,_=v.infinite_envelope_for_cuts(-u[1],-u[2],-u[5],-u[3])
        self.assertTrue(inf.inside(v.Q(7,10),v.Q(4,5)))
        self.assertTrue(v.certify_large_p(tau,u)['from_period']==13)
        self.assertTrue(pi.inside(v.Q(314159,100000),v.Q(314160,100000)))

    def test_reject_elliptic_or_log_outside_analytic_range(self):
        with self.assertRaises(AssertionError):
            v.elliptic_factor(v.Iv.point(1))
        with self.assertRaises(AssertionError):
            v.log_iv(v.Iv.point(v.Q(1,2)))
        with self.assertRaises(AssertionError):
            v.arccos_pos(v.Iv.point(0))

    def test_committed_read_only_exact_output(self):
        expected=json.loads(v.RESULT.read_text())
        got=v.run(json.loads(v.OLD.read_text()))
        self.assertEqual(expected,got)
        self.assertTrue(all(row['NOT_a_canonical_width_certificate'] for row in got['finite']))


if __name__=='__main__':
    unittest.main()
