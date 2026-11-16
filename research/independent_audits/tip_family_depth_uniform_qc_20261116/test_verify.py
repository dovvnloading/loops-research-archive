"""Hostile finite checks: no analytic transport is assumed or fabricated."""
import unittest
from fractions import Fraction as Q

from verify import (
    BLOCKS, COVER, CREST_P3_REFERENCE, EDGE_CUT_IMAGES, EDGE_SIDES, MATRIX, PAIRS,
    VerificationError, crest_ratio_bounds, level_bounds, marked_table_check,
    qc_image_bounds, quick_checks, reference_bounds, shortest_inclusive_span,
)


class DepthUniformQCAuditTests(unittest.TestCase):
    def test_positive_standalone_finite_checks(self):
        quick_checks()
        self.assertEqual(marked_table_check()["edge_matrix"], MATRIX)
        self.assertEqual(marked_table_check()["source_spans"], (3, 3, 7))
        self.assertEqual(marked_table_check()["target_spans"], (3, 3, 5))

    def test_cover_and_immersion_are_distinct(self):
        # The two degree-two cover preimages of I0 are S0,S10;
        # the immersion preimage of I0 is instead S18,S19,S0,S1,S2.
        self.assertNotEqual(tuple(s for s in range(20) if COVER[s] == 0),
                            BLOCKS[0])
        wrong_cover = tuple(next(i for i, b in enumerate(BLOCKS) if s in b)
                            for s in range(20))
        with self.assertRaisesRegex(VerificationError, "covering push changed"):
            marked_table_check(cover=wrong_cover)

    def test_partition_and_attachment_mutations(self):
        wrong = list(BLOCKS)
        wrong[1], wrong[2] = wrong[2], wrong[1]
        with self.assertRaisesRegex(VerificationError, "immersion/attachment changed"):
            marked_table_check(blocks=tuple(wrong))
        wrong = list(BLOCKS)
        wrong[0] = (18, 19, 0, 1, 1)
        with self.assertRaisesRegex(VerificationError, "partition"):
            marked_table_check(blocks=tuple(wrong))
        wrong = list(BLOCKS)
        wrong[0] = (18, 0, 19, 1, 2)
        with self.assertRaisesRegex(VerificationError, "consecutive"):
            marked_table_check(blocks=tuple(wrong))

    def test_two_opposite_accesses_are_one_old_edge(self):
        self.assertEqual(marked_table_check()["opposite_accesses"], EDGE_SIDES)
        with self.assertRaisesRegex(VerificationError, "old edge sides changed"):
            marked_table_check(edge_sides=((1, "E0"), (9, "E1")))
        with self.assertRaisesRegex(VerificationError, "old edge sides changed"):
            marked_table_check(edge_sides=((1, "E0"), (1, "E0")))

    def test_proper_spans_not_all_three_and_not_short(self):
        self.assertEqual(shortest_inclusive_span(3, 17, 20), 7)
        self.assertEqual(shortest_inclusive_span(COVER[3], COVER[17], 10), 5)
        with self.assertRaisesRegex(VerificationError, "endpoint pairs changed"):
            marked_table_check(pairs=PAIRS[:-1] + ((3, 1),))
        with self.assertRaisesRegex(VerificationError, "invalid atom"):
            shortest_inclusive_span(3, 20, 20)

    def test_marked_old_edge_map_mutation(self):
        with self.assertRaisesRegex(VerificationError, "old-edge images changed"):
            marked_table_check(cut_images=(2, 4, 4, 2, 0))
        self.assertEqual(EDGE_CUT_IMAGES, (2, 4, 4, 3, 0))

    def test_no_depth_compounding(self):
        for period in (3, 4, 12, 13, 17, 100000):
            for k in (Q(1), Q(5, 4), Q(4)):
                self.assertEqual(level_bounds(1, period, k),
                                 level_bounds(1000000, period, k))
                low, high = level_bounds(123, period, k)
                self.assertGreater(low, 0)
                self.assertGreater(high, low)
        self.assertEqual(reference_bounds(12), (Q(1, 4), Q(39, 50)))
        self.assertEqual(reference_bounds(13), (Q(13, 50), Q(39, 50)))

    def test_026_not_available_at_small_reference_periods(self):
        low, high = level_bounds(3, 3, Q(1))
        self.assertEqual(low, Q(1, 4))
        self.assertEqual(high, Q(39, 50))
        self.assertNotEqual(low, Q(13, 50))

    def test_ratio_is_two_dilatations_not_one(self):
        for K in (Q(1), Q(3, 2), Q(2), Q(7)):
            lo, hi = crest_ratio_bounds(*CREST_P3_REFERENCE, K)
            self.assertEqual(lo, Q(5676, 10000) / (K*K))
            self.assertEqual(hi, Q(5684, 10000) * (K*K))
        self.assertEqual(qc_image_bounds(Q(1, 4), Q(3, 4), Q(2)),
                         (Q(1, 8), Q(3, 2)))

    def test_reject_invalid_parameters_instead_of_float_rounding(self):
        bad_calls = [
            lambda: level_bounds(0, 13, 1),
            lambda: level_bounds(True, 13, 1),
            lambda: level_bounds(1, 2, 1),
            lambda: level_bounds(1, 13, Q(99, 100)),
            lambda: level_bounds(1, 13, float(2)),
            lambda: level_bounds(1, 13, True),
            lambda: qc_image_bounds(0, 1, 1),
            lambda: qc_image_bounds(1, 1, 1),
            lambda: crest_ratio_bounds(0, 1, 1),
            lambda: crest_ratio_bounds(1, 2, 0),
        ]
        for func in bad_calls:
            with self.subTest(func=func), self.assertRaises(VerificationError):
                func()


if __name__ == "__main__":
    unittest.main()
