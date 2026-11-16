"""Hostile regression tests for exact collars and explicitly nonclosing q claims."""
import copy
import json
import unittest
from fractions import Fraction as Q

from verify import (TIP, INCIDENCE, PREVIOUS, OUTPUT, COLLARS, LOCAL_UPPER,
                    NORM_UPPER, certify, orbit, log_range, pi_range)


class PeripheralCertificateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tip = json.loads(TIP.read_text())
        cls.incidence = json.loads(INCIDENCE.read_text())
        cls.previous = json.loads(PREVIOUS.read_text())

    def test_only_supported_claims_and_manifest(self):
        result = certify(self.tip, self.incidence, self.previous)
        self.assertEqual(result, json.loads(OUTPUT.read_text()))
        self.assertFalse(result["every_individual_q_gamma_certified"])
        self.assertFalse(result["positive_support_classified"])
        self.assertFalse(result["exhaustive_other_classes_q_le_2_proved"])
        self.assertIsNone(result["positive_support_list"])
        self.assertEqual(result["total_canonical_norm_strict_bracket"], ["0", "687/100"])
        self.assertEqual(len(result["uniform_endpoint_pair_brackets"]), 10)
        self.assertTrue(all(not row["positive_canonical_weight_certified"]
                            for row in result["uniform_endpoint_pair_brackets"]))
        self.assertEqual(result["numerical_only"], [])
        self.assertEqual(sum(LOCAL_UPPER.values(), Q(0))/2, Q(13733, 2000))
        self.assertLess(Q(13733,2000), NORM_UPPER)

    def test_nontrivial_self_endpoint_factor_two(self):
        r = certify(self.tip,self.incidence,self.previous)
        table = {tuple(x["boundary_pair"]): Q(x["uniform_q_gamma_strict_bracket"][1])
                 for x in r["uniform_endpoint_pair_brackets"]}
        self.assertEqual(table[("outer","outer")], 2+LOCAL_UPPER["outer"]/2)
        self.assertEqual(table[("K1","K1")], 2+LOCAL_UPPER["K1"]/2)
        self.assertEqual(table[("K0","K1")], 2+min(LOCAL_UPPER["K0"],LOCAL_UPPER["K1"]))
        self.assertTrue(all(hi > 2 for hi in table.values()))

    def test_exact_pi_and_log_interval(self):
        p0,p1 = pi_range()
        self.assertLess(Q(333,106),p0)
        self.assertLess(p1,Q(22,7))
        for _,_,t in COLLARS.values():
            a,b = log_range(t)
            self.assertTrue(Q(0)<a<b)
            self.assertLess(2*p1/a,LOCAL_UPPER[next(
                name for name, item in COLLARS.items() if item[2] == t)])

    def test_physical_parameter_mutation_rejected(self):
        p = copy.deepcopy(self.tip)
        p["source_parameter"]["lower_numerator"] += 1
        with self.assertRaises(AssertionError):
            orbit(p)

    def test_wrong_canonical_marking_rejected(self):
        d = copy.deepcopy(self.incidence)
        d["canonical_definition"]["minimal_marking"] = "ten target tree atoms"
        with self.assertRaises(AssertionError):
            certify(self.tip,d,self.previous)

    def test_wrong_parent_claim_rejected(self):
        d = copy.deepcopy(self.previous)
        d["canonical_WAD"]["quadrilateral_enclosures_certified"] = True
        with self.assertRaises(AssertionError):
            certify(self.tip,self.incidence,d)

    def test_too_large_ellipses_rejected(self):
        for name,t in [("outer",Q(12,5)),("K0",Q(12)),("K1",Q(50)),("K2",Q(26))]:
            with self.subTest(name=name):
                corrupted = dict(COLLARS)
                i,j,_ = corrupted[name]
                corrupted[name] = (i,j,t)
                with self.assertRaises(AssertionError):
                    certify(self.tip,self.incidence,self.previous,collars=corrupted)

    def test_bad_or_missing_peripheral_component_rejected(self):
        corrupted = dict(COLLARS)
        corrupted["outer"] = (9,18,Q(23,10))
        with self.assertRaises(AssertionError):
            certify(self.tip,self.incidence,self.previous,collars=corrupted)
        corrupted = dict(COLLARS)
        corrupted.pop("outer")
        with self.assertRaises(AssertionError):
            certify(self.tip,self.incidence,self.previous,collars=corrupted)

    def test_optimistic_bound_rejected(self):
        low = dict(LOCAL_UPPER)
        low["K0"] = Q(13,5)  # 2.6 is below exact 2*pi/log(11).
        with self.assertRaises(AssertionError):
            certify(self.tip,self.incidence,self.previous,uppers=low)

    def test_no_false_q_certificate_possible_in_checked_results(self):
        r = certify(self.tip,self.incidence,self.previous)
        r["every_individual_q_gamma_certified"] = True
        r["uniform_endpoint_pair_brackets"][0]["positive_canonical_weight_certified"] = True
        self.assertNotEqual(r, json.loads(OUTPUT.read_text()))


if __name__ == "__main__":
    unittest.main()
