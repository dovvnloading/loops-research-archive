#!/usr/bin/env python3
"""Adversarial in-memory tests: fail closed on typed, chart and boundary drift."""
import copy
from fractions import Fraction as F
import unittest

import verify_chain as v


def good_common():
    return {
        "target_cuts": copy.deepcopy(v.TARGET_CUTS),
        "source_cuts": copy.deepcopy(v.SOURCE_CUTS),
        "target_atoms": 10, "source_atoms": 20, "outer_component_atom": 1,
        "covering_f_star": copy.deepcopy(v.COVER),
        "immersion_iota_pullback_blocks": copy.deepcopy(v.BLOCKS),
        "attached_source_sides": copy.deepcopy(v.ATTACHED),
        "proper_crossing_pairs": copy.deepcopy(v.CROSSING),
        "proper_avoiding_pair": copy.deepcopy(v.AVOIDING),
        "cover_pushed_crossing_pairs": copy.deepcopy(v.PUSHED_CROSSING),
        "cover_pushed_avoiding_pair": copy.deepcopy(v.PUSHED_AVOIDING),
        "old_edge_matrix_output_rows_input_cols": copy.deepcopy(v.MATRIX),
        "target_zero_edge_atoms": copy.deepcopy(v.TARGET_ZERO),
        "parent_crest": 0, "child_crests": [2, 8],
        "perron_root": "(1+sqrt(5))/2",
        "harmonic_width_coefficients": {"parent": "1/2", "each_child": "1"},
    }


class HostileChainTests(unittest.TestCase):
    def test_valid_typed_model(self):
        v.verify_common(good_common())

    def test_covering_not_immersion(self):
        damaged = good_common()
        damaged["covering_f_star"] = [next(i for i, b in enumerate(v.BLOCKS)
                                         if s in b) for s in range(20)]
        with self.assertRaisesRegex(AssertionError, "covering"):
            v.verify_common(damaged)

    def test_duplicated_immersion_atom(self):
        damaged = good_common()
        damaged["immersion_iota_pullback_blocks"][9][-1] = 16
        with self.assertRaisesRegex(AssertionError, "immersion"):
            v.verify_common(damaged)

    def test_wrong_return_index(self):
        self.assertEqual([v.substitute_cut(s, 3) for s in v.TARGET_CUTS],
                         ["x15", "x9", "x18", "alpha", "x12"])
        self.assertEqual([v.substitute_cut(s, 4) for s in v.SOURCE_CUTS],
                         ["-x16", "x8", "x20", "-alpha", "x12", "x24",
                          "alpha", "-x20", "-x8", "x16"])

    def test_inclusive_avoiding_source_arc_is_seven_not_three(self):
        self.assertEqual([v.spans(20, *pair)
                          for pair in v.CROSSING + [v.AVOIDING]], [3, 3, 7])
        self.assertEqual([v.spans(10, *pair)
                          for pair in v.PUSHED_CROSSING + [v.PUSHED_AVOIDING]],
                         [3, 3, 5])
        self.assertNotEqual(v.spans(20, 3, 17), 3)

    def test_mutated_pushed_endpoint(self):
        damaged = good_common()
        damaged["cover_pushed_avoiding_pair"] = [3, 3]
        with self.assertRaisesRegex(AssertionError, "covering-pushed"):
            v.verify_common(damaged)

    def test_dyadic_adjacent_brackets_and_256_bit_seam(self):
        a = {"parameter_bracket": {"denominator_power_of_two": 256,
                                   "lower_numerator": -1000,
                                   "upper_numerator": -999}}
        b = {"parameter_bracket_2pow256": [-1000, -999]}
        self.assertEqual(v.interval_from_bracket(a, "parameter_bracket"),
                         v.interval_from_bracket(b, "parameter_bracket_2pow256"))
        b["parameter_bracket_2pow256"][1] += 1
        with self.assertRaisesRegex(AssertionError, "adjacent"):
            v.interval_from_bracket(b, "parameter_bracket_2pow256")

    def test_period12_period13_must_not_be_missing(self):
        rows = [{"p": p} for p in range(3, 13)]
        self.assertEqual(len(v.period_rows(rows, 3, 12, "finite")), 10)
        with self.assertRaisesRegex(AssertionError, "missing"):
            v.period_rows(rows[:-1], 3, 12, "finite")
        rows = [{"p": p} for p in range(3, 17)]
        with self.assertRaisesRegex(AssertionError, "missing"):
            v.period_rows([r for r in rows if r["p"] != 13],
                          3, 16, "crest")

    def test_matrix_is_derived_not_doubled(self):
        self.assertEqual(v.edge_occurrences(), v.MATRIX)
        power = v.MATRIX
        for _ in range(3):
            power = v.matmul(power, v.MATRIX)
        self.assertTrue(all(n > 0 for row in power for n in row))

    def test_strict_bracket_overlap_does_not_accept_touching(self):
        self.assertTrue(v.intervals_overlap((F(0), F(2)), (F(1), F(3))))
        self.assertFalse(v.intervals_overlap((F(0), F(1)), (F(1), F(2))))
        self.assertNotEqual(v.SOURCE_ZERO, v.COVER_ZERO)


if __name__ == "__main__":
    unittest.main()
