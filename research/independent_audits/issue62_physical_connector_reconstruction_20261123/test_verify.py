#!/usr/bin/env python3
"""Targeted controls for source preservation, path order, and cut ties."""

from fractions import Fraction as F
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

_spec = importlib.util.spec_from_file_location(
    "issue62_physical_connector_verify", Path(__file__).with_name("verify.py")
)
v = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(v)


class ConnectorReconstructionTests(unittest.TestCase):
    def test_complete_historical_cohort(self):
        result = v.build_manifest(v.DEFAULT_REPO)
        self.assertEqual(result["counts"]["source_rows"], 88)
        self.assertEqual(result["counts"]["in_H"], 8)
        self.assertEqual(result["counts"]["outside_H"], 80)
        self.assertTrue(all(r["prior_membership_agrees"] for r in result["rows"]))

    def test_noncommutative_crossing_order(self):
        crossings = v.direct_crossings(v.MIDPOINTS[2], F(3, 14))
        measured = tuple(c["signed_letter"] for c in crossings)
        self.assertEqual(measured, (-2, -1))
        # Reversing these letters has the same complete winding vector,
        # but is a different based free word and must not be accepted.
        self.assertEqual(v.winding(measured), v.winding((-1, -2)))
        self.assertNotEqual(v.reduce_word(measured), v.reduce_word((-1, -2)))

    def test_native_deck_is_not_a_common_beta_prefix(self):
        theta = F(3, 14)
        zero = v.formula_word(1, theta, 0)
        native = v.formula_word(1, theta, 1)
        self.assertEqual(native, v.product((2, 3, 1), zero))
        self.assertNotEqual(native, v.product(v.BETA, zero))

    def test_second_path_has_real_backtracking_and_same_word(self):
        first = v.direct_crossings(v.MIDPOINTS[2], F(5, 7))
        second = v.second_crossings(2, F(5, 7), 0)
        first_raw = tuple(c["signed_letter"] for c in first)
        second_raw = tuple(c["signed_letter"] for c in second)
        self.assertNotEqual(first_raw, second_raw)
        self.assertEqual(v.reduce_word(first_raw), v.reduce_word(second_raw))

    def test_root_cut_endpoint_is_explicitly_handled(self):
        alpha = v.CUTS[0][0]
        with self.assertRaisesRegex(ValueError, "end lies on a cut"):
            v.direct_crossings(v.MIDPOINTS[0], alpha)
        left = alpha - (alpha - v.SEAMS[1][0]) / 8
        self.assertEqual(v.formula_word(0, alpha, 0), ())
        self.assertEqual(v.formula_word(1, alpha, 0), (-1,))
        for j in range(4):
            for n in (-1, 0, 1):
                raw = (c["signed_letter"] for c in v.direct_crossings(v.MIDPOINTS[j], left + n))
                self.assertEqual(v.reduce_word(raw), v.formula_word(j, alpha, n))

    def test_first_octal_symbol_handles_the_cut_endpoint_and_gap(self):
        self.assertEqual(v.address_word(0, 1, 3, 0), ())
        self.assertEqual(v.address_word(0, 1, 4, 0), (1,))
        for j in range(4):
            for n in (-1, 0, 1):
                self.assertEqual(v.address_word(j, 1, 3, n), v.formula_word(j, F(249, 896), n))
                self.assertEqual(v.address_word(j, 1, 4, n), v.formula_word(j, F(255, 896), n))
        with self.assertRaisesRegex(ValueError, "invalid Cantor octal symbol"):
            v.address_word(0, 1, 0, 0)

    def test_coarse_only_prefix_cannot_replace_native_mate(self):
        theta = F(5, 7)
        native = v.formula_word(3, theta, 0)
        coarse_reference = v.formula_word(0, theta, 0)
        self.assertEqual(native, ())
        self.assertEqual(coarse_reference, (1, 2))
        delta = lambda word: v.winding(word)[1] - v.winding(word)[2]
        self.assertEqual(delta(native), 0)
        self.assertEqual(delta(coarse_reference), 1)
        # Every coarse generator has zero transverse character; any
        # coarse-word prefix therefore leaves the obstruction unchanged.
        for coarse_generator in ((1, 2, 3), (4, 5, 6), (7, 8, 9)):
            self.assertEqual(delta(coarse_generator), 0)
            self.assertEqual(delta(v.product(coarse_generator, coarse_reference)), 1)
            self.assertEqual(delta(v.product(v.inverse(coarse_generator), coarse_reference)), 1)

    def mutate_source(self, relative, mutate):
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            for path in (v.SOURCE_WORDS, v.SOURCE_ROWS, v.SOURCE_ATLAS):
                target = repo / path
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes((v.DEFAULT_REPO / path).read_bytes())
            target = repo / relative
            data = json.loads(target.read_text())
            mutate(data)
            target.write_text(json.dumps(data))
            return v.build_manifest(repo)

    def test_native_coordinate_mutation_is_rejected(self):
        def mutate(data):
            stage = next(s for s in data["stages"] if s["stage"] == "G")
            stage["pieces"]["W"]["tiles"][1]["seam_midpoint_lift"] = "41/32"
        with self.assertRaisesRegex(ValueError, "native midpoint changed"):
            self.mutate_source(v.SOURCE_ATLAS, mutate)

    def test_prior_root_claim_is_compared_after_word_computation(self):
        def mutate(data):
            row = data["rows"][0]
            self.assertEqual(row["conditional_required_F9_root_subgroup_membership"], "outside_H")
            row["conditional_required_F9_root_subgroup_membership"] = "in_H"
        with self.assertRaisesRegex(ValueError, "DISAGREES WITH HISTORICAL ROOT CLASSIFICATION"):
            self.mutate_source(v.SOURCE_WORDS, mutate)


if __name__ == "__main__":
    unittest.main()
