"""Hostile exact-arithmetic tests for near-parabolic primitive v1 refusal."""
from __future__ import annotations

import copy
import unittest
from fractions import Fraction as Q

import regenerate_near_parabolic as near
from regenerate import Box, bracket


class NearParabolicPrimitiveTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.example = near.load(near.INPUT)

    def test_all_three_local_roots_and_shrinking_strict_complex_margins(self):
        records = near.certify(self.example)
        self.assertEqual(records["finite_parameter_order"], "-7/4 < c30 < c27 < c24")
        self.assertEqual(len(records["finite_selected_members"]), 3)
        for row, p, m, sep in zip(
                records["finite_selected_members"],
                near.EXPECTED_PERIODS,
                near.EXPECTED_MARGIN_RANGES,
                near.EXPECTED_PHASE_RANGES):
            self.assertEqual(row["physical_return"], p)
            self.assertEqual(row["restricted_degree"], 2)
            self.assertEqual(row["global_degree"], str(2**p))
            self.assertEqual(row["central_rouche_margin_strictly_between"],
                             list(map(str, m)))
            self.assertEqual(row["primitive_phase_disk_gap_strictly_between"],
                             list(map(str, sep)))
            self.assertTrue(row["complex_phases_pairwise_disjoint"])
            self.assertTrue(row["round_subcollar"]["not_a_measured_KKL_attachment_collar_h"])
            self.assertEqual(row["real_inner_geometry"]["number_of_inner_G_phase_intervals"], 1)
            self.assertEqual(row["real_inner_geometry"]["new_inverse_tree_attachments"], 0)
        self.assertGreater(m[0], 0)

    def test_faithful_v1_refusal_and_distinct_operations(self):
        output = near.certify(self.example)
        self.assertEqual(output["first_incompatible_v1_field"],
                         "MarkedHubbardTree.small_julia_intervals")
        self.assertIs(output["v1_physical_examples_emitted"], False)
        self.assertIsNone(output["canonical_KKL_attachment_h"])
        self.assertIsNone(output["canonical_KKL_attachment_ell"])
        self.assertIsNone(output["new_attachment_electrode_arc"])
        self.assertNotEqual(output["distinct_operations"]["covering_f_star"],
                            output["distinct_operations"]["immersion_iota_star"])
        self.assertIn("inapplicable", output["annular_contact_resistance_test"])

    def test_separating_complex_disks_and_collars_are_nontrivial(self):
        for row in self.example["members"]:
            p = row["p"]
            c = Box(near.Box.rational(Q(int(row["lower_numerator"]), 2**160)).low,
                    near.Box.rational(Q(int(row["upper_numerator"]), 2**160)).high)
            r = Q(row["outer_radius"])
            margin, _ = near.rouche_margin(c, p, r, r)
            self.assertGreater(margin, 0)
            smaller, _ = near.rouche_margin(c, p, Q(7, 8)*r, r)
            self.assertGreater(smaller, 0)
            gap, noncentral = near.complex_phase_bounds(bracket(c, 2*p), p, r)
            self.assertGreater(gap, 0)
            self.assertGreater(noncentral, 0)
            # A wildly enlarged disk must fail the *primitive* phase certificate.
            with self.assertRaisesRegex(AssertionError, "phase disks overlap"):
                near.complex_phase_bounds(bracket(c, 2*p), p, Q(1, 8))

    def test_incorrect_root_and_parameter_precision_rejected(self):
        for i in range(3):
            example = copy.deepcopy(self.example)
            row = example["members"][i]
            row["lower_numerator"] = str(int(row["lower_numerator"]) + 1)
            row["upper_numerator"] = str(int(row["upper_numerator"]) + 1)
            with self.assertRaisesRegex(AssertionError, "tip-equation root signs"):
                near.certify(example)
        example = copy.deepcopy(self.example)
        example["members"][0]["denominator_power_of_two"] = 159
        with self.assertRaisesRegex(AssertionError, "parameter precision"):
            near.certify(example)
        example = copy.deepcopy(self.example)
        example["members"][1]["p"] = 28
        with self.assertRaisesRegex(AssertionError, "physical return period"):
            near.certify(example)

    def test_reject_forged_wave_and_unsupported_margin(self):
        for field, value in (
            ("source_contract", "source_contracts/record_fields.json"),
            ("marking", {"target_cuts": []}),
            ("operations", {"covering": "iota^*"}),
            ("wave", {"harmonic_series_equality": True}),
        ):
            example = copy.deepcopy(self.example)
            example[field] = value
            with self.assertRaisesRegex(AssertionError, "forged v1 marking"):
                near.certify(example)
        example = copy.deepcopy(self.example)
        example["record_compatibility"] = "compatible"
        with self.assertRaisesRegex(AssertionError, "forged v1 marking"):
            near.certify(example)
        example = copy.deepcopy(self.example)
        example["first_incompatible_field"] = "WaveFamily.target_width"
        with self.assertRaisesRegex(AssertionError, "forged v1 marking"):
            near.certify(example)
        example = copy.deepcopy(self.example)
        example["members"][2]["rouche_margin_between"] = ["1/100", "1/10"]
        with self.assertRaisesRegex(AssertionError, "claimed exact margins"):
            near.certify(example)
        example = copy.deepcopy(self.example)
        example["not_asserted"].pop()
        with self.assertRaisesRegex(AssertionError, "missing research limits"):
            near.certify(example)

    def test_prior_output_git_blobs_and_immutable_canonical_manifest(self):
        for name, blob in near.SOURCE_LOCKS.items():
            with self.subTest(name=name):
                self.assertEqual(near.git_blob(near.REPO / name), blob)
        computed = near.make_manifest(self.example)
        self.assertEqual(near.MANIFEST.read_bytes(), near.canonical(computed))
        self.assertEqual(computed["outputs_sha256"],
                         near.hashlib.sha256(near.canonical(computed["outputs"])).hexdigest())
        self.assertEqual(computed["outputs"]["prior_primitive_comparison"]["p3"]
                         ["filtered_restrictions_cross_avoid"], [2, 1])
        self.assertTrue(computed["outputs"]["prior_primitive_comparison"]["p4"]
                        ["harmonic_equality"])


if __name__ == "__main__":
    unittest.main()
