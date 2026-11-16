"""Adversarial regression tests for the independent finite p=3..12 interval audit."""
from __future__ import annotations

import json
import unittest
from fractions import Fraction as Q
from pathlib import Path
from unittest.mock import patch

import verify as v


class TestIndependentFamily(unittest.TestCase):
    def test_frozen_ten_periods(self):
        actual=v.run()
        self.assertEqual([r["p"] for r in actual["periods"]],list(range(3,13)))
        self.assertEqual(actual,json.loads((Path(v.__file__).parent/"results.json").read_text()))
        self.assertTrue(all(r["central_degree_two_Rouche_margin_lower_2^-64"]
                            for r in actual["periods"]))

    def test_wrong_p9_root_with_same_polynomial_identity(self):
        # Different nearby solution of x_6p+x_3p=0, *wrong* signed itinerary.
        with patch.dict(v.SEEDS,{9:"-1.999943523397210093135378488190474023646670845911870358281125308870885043661441912535"}):
            with self.assertRaises(AssertionError):
                v.native(9)

    def test_bad_locator_rejected(self):
        with patch.dict(v.SEEDS,{5:"-1.98552"}):
            with self.assertRaises(AssertionError):
                v.native(5)

    def test_false_matrix_entry_rejected(self):
        old=v.EXPECTED_MATRIX[0][2]
        try:
            v.EXPECTED_MATRIX[0][2]=0
            with self.assertRaisesRegex(AssertionError,"edge matrix"):
                v.native(3)
        finally:
            v.EXPECTED_MATRIX[0][2]=old

    def test_false_immersion_block_rejected(self):
        old=v.EXPECTED_BLOCKS[0][0]
        try:
            v.EXPECTED_BLOCKS[0][0]=17
            with self.assertRaisesRegex(AssertionError,"immersion cyclic block"):
                v.native(4)
        finally:
            v.EXPECTED_BLOCKS[0][0]=old

    def test_seven_atom_avoiding_arc_not_three(self):
        self.assertEqual(v.arc(3,17,20),[17,18,19,0,1,2,3])
        self.assertEqual(v.arc(3,7,10),[3,4,5,6,7])
        self.assertEqual([len(v.arc(*pair,20)) for pair in [(3,1),(19,17),(3,17)]],[3,3,7])

    def test_small_domain_loses_rouche_margin(self):
        _,_,c,_=v.isolate_parameter(3)
        with self.assertRaisesRegex(AssertionError,"Rouch"):
            v.rouche(3,c,Q(1,64))


if __name__=="__main__":
    unittest.main()
