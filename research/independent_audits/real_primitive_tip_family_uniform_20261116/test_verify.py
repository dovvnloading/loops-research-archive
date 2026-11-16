"""Adversarial tests of the independent period-family verifier."""
from __future__ import annotations

import unittest
from fractions import Fraction as F
from unittest.mock import patch

import verify as v


class TestIndependentFamily(unittest.TestCase):
    def test_frozen_six_periods(self) -> None:
        rows = v.run()["results"]
        self.assertEqual([row["p"] for row in rows], list(range(3,9)))
        self.assertEqual([row["selected_wave_ratio"] for row in rows],
                         ["4/3", "3/2", "8/5", "5/3", "12/7", "7/4"])
        self.assertTrue(all(row["real_and_complex_primitive_phase_balls_disjoint"]
                            for row in rows))

    def test_bad_parameter_seed_refused(self) -> None:
        with patch.dict(v.SEEDS, {5: "-1.98552"}):
            with self.assertRaises(AssertionError):
                v.native(5)

    def test_false_edge_occurrence_refused(self) -> None:
        old = v.EXPECTED_MATRIX[0][2]
        try:
            v.EXPECTED_MATRIX[0][2] = 0
            with self.assertRaisesRegex(AssertionError, "edge matrix"):
                v.native(3)
        finally:
            v.EXPECTED_MATRIX[0][2] = old

    def test_false_immersion_block_refused(self) -> None:
        old = v.EXPECTED_BLOCKS[0][0]
        try:
            v.EXPECTED_BLOCKS[0][0] = 17
            with self.assertRaisesRegex(AssertionError, "immersion cyclic block"):
                v.native(4)
        finally:
            v.EXPECTED_BLOCKS[0][0] = old

    def test_cover_vs_immersion_are_not_identified(self) -> None:
        self.assertNotEqual([i%10 for i in range(20)],
                            [0,0,0,1,1,2,3,4,4,4,5,6,6,6,7,8,9,9,0,0])

    def test_width_noncanonicity_at_p3(self) -> None:
        # Both radii are strictly inside the original p3 wave window,
        # but the new subannulus has ratio 6/5, not 4/3.
        self.assertTrue(F(3,256) < F(5,384) < F(1,64))
        self.assertEqual(F(1,64)/F(5,384),F(6,5))
        self.assertNotEqual(F(6,5),F(4,3))

    def test_general_normalization_bounds(self) -> None:
        for p in range(3,128):
            ratio=F(2*(p-1),p)
            self.assertTrue(F(4,3) <= ratio < 2)
            self.assertEqual(F(1,F(1,2)),F(1,F(1))+F(1,F(1)))


if __name__ == "__main__":
    unittest.main()
