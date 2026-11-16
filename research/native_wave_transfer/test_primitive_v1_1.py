"""Hostile v1.1 regression: source locks, two maps, no fictional Wave data."""
from __future__ import annotations

import copy
import hashlib
import unittest

import regenerate_primitive_v1_1 as v11
import regenerate_near_parabolic as old
from regenerate import canonical, load


class PrimitiveOneSlitV11Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.fixture = load(old.INPUT)
        cls.outputs = v11.make_outputs(cls.fixture)
        cls.contract = load(v11.CONTRACT)

    def test_three_certified_one_inner_and_p_ambient_phases(self):
        self.assertEqual([x["p"] for x in self.outputs["members"]], [24, 27, 30])
        self.assertEqual(self.outputs["mode"], v11.MODE)
        self.assertEqual(self.outputs["finite_parameter_order"],
                         "-7/4 < c30 < c27 < c24")
        for item in self.outputs["members"]:
            with self.subTest(p=item["p"]):
                v11.validate_member(item)
                self.assertEqual(item["ambient_phase_count"], item["p"])
                self.assertEqual(item["inner_return_interval_count"], 1)
                self.assertEqual(item["local_tree"]["new_attachment_components"], [])
                self.assertTrue(item["local_tree"]["complete_for_central_return"])
                self.assertIsNone(item["local_tree"]["ambient_KKL_attachment_census"])
                self.assertEqual(item["complex_certificates"]["restricted_degree"], 2)

    def test_atoms_separate_covering_and_inclusion(self):
        for item in self.outputs["members"]:
            boundary = item["ideal_boundary"]
            covering = item["operations"]["covering_f_star"]
            immersion = item["operations"]["immersion_iota_star"]
            self.assertEqual((boundary["target_inner_atom_count"],
                              boundary["covering_source_inner_atom_count"],
                              boundary["outer_component_atom_count"]), (2, 4, 1))
            self.assertFalse(boundary["count_invariant_under_refinement"])
            self.assertEqual(covering["source_to_target"], [1, 0, 1, 0])
            self.assertEqual(immersion["source_to_target_pullback"], [0, 0, 1, 1])
            self.assertEqual(immersion["target_to_source_blocks"], [[0, 1], [2, 3]])
            self.assertEqual(covering["preimages_per_target_side"], [2, 2])
            self.assertNotEqual(covering["map"], immersion["map"])

    def test_no_full_kkl_wave_perron_or_attachment_contact_from_local_slit(self):
        for item in self.outputs["members"]:
            self.assertEqual(item["local_edges"]["local_complementary_incidence_matrix"], [])
            self.assertEqual(item["local_edges"]["zero_local_edge_side_atoms"], list(v11.TARGET))
            for k in ("local_perron_root", "ambient_KKL_perron_root",
                      "ambient_KKL_old_edge_matrix", "KKL_closed_wave_crests"):
                self.assertIsNone(item["local_edges"][k])
            self.assertEqual(item["restrictions"]["local_covering_side_germs"], 2)
            self.assertEqual(item["restrictions"]["local_inclusion_side_germs"], 1)
            self.assertIsNone(item["restrictions"]["filtered_restriction_counts"])
            self.assertIsNone(item["restrictions"]["specified_whole_target_path"])
            self.assertTrue(all(value is None for value in item["wave"].values()))
            self.assertTrue(all(value is None for value in item["resistance"].values()))
            self.assertIsNone(item["collar"]["canonical_attachment_h"])
            self.assertIsNone(item["collar"]["canonical_attachment_ell"])
            self.assertEqual(item["collar"]["round_quadratic_like_modulus_lower_bound"],
                             "log(8/7)/(2*pi)")

    def test_hostile_mixed_actions_fabricated_wave_collar_or_spectrum_rejected(self):
        for parts, forged in (
            (("operations", "covering_f_star", "source_to_target"), [0, 0, 1, 1]),
            (("operations", "immersion_iota_star", "source_to_target_pullback"),
             [1, 0, 1, 0]),
            (("operations", "immersion_iota_star", "target_to_source_blocks"),
             [[0, 3], [1, 2]]),
            (("local_edges", "ambient_KKL_perron_root"), "0"),
            (("local_edges", "KKL_closed_wave_crests"), ["I_upper"]),
            (("restrictions", "filtered_restriction_counts"), [2, 1]),
            (("wave", "parent_width"), "log(8/7)/(2*pi)"),
            (("wave", "harmonic_equality"), True),
            (("collar", "canonical_attachment_h"), "log(8/7)"),
            (("collar", "canonical_attachment_ell"), "0"),
            (("resistance", "h_times_log_inverse_ell"), "0"),
            (("ideal_boundary", "count_invariant_under_refinement"), True),
            (("local_tree", "ambient_KKL_attachment_census"), []),
        ):
            with self.subTest(parts=parts):
                bad = copy.deepcopy(self.outputs["members"][0])
                cursor = bad
                for key in parts[:-1]:
                    cursor = cursor[key]
                cursor[parts[-1]] = forged
                with self.assertRaises(AssertionError):
                    v11.validate_member(bad)

    def test_registry_is_exact_source_status_coverage(self):
        v11.check_contract(self.outputs, self.contract)
        bad = copy.deepcopy(self.contract)
        del bad["fields"]["members[].wave.parent_width"]
        with self.assertRaisesRegex(AssertionError, "uncited"):
            v11.check_contract(self.outputs, bad)
        bad = copy.deepcopy(self.contract)
        bad["fields"]["members[].wave.parent_width"]["source"] = "MADE_UP"
        with self.assertRaisesRegex(AssertionError, "citation"):
            v11.check_contract(self.outputs, bad)
        bad = copy.deepcopy(self.contract)
        bad["fields"]["members[].wave.parent_width"]["status"] = "exact-finite"
        with self.assertRaisesRegex(AssertionError, "null lacks"):
            v11.check_contract(self.outputs, bad)
        bad = copy.deepcopy(self.outputs)
        for member in bad["members"]:
            member["wave"]["alien_width"] = "1"
        with self.assertRaisesRegex(AssertionError, "uncited"):
            v11.check_contract(bad, self.contract)
        bad = copy.deepcopy(self.outputs)
        bad["members"][0]["complex_certificates"]["restricted_degree"] = 2.0
        with self.assertRaises(AssertionError):
            v11.check_contract(bad, self.contract)

    def test_legacy_v1_tag_round_trip_is_canonical_byte_identity(self):
        for name in ("tip_pr68", "primitive4_tip12"):
            record = load(v11.HERE / ("experiment_manifests/" + name + ".json"))
            lifted = v11.legacy_embed(record)
            self.assertEqual(lifted["mode"], "v1-three-inner-phase")
            self.assertEqual(canonical(v11.legacy_project(lifted)), canonical(record))
            with self.assertRaises(AssertionError):
                v11.legacy_project({"mode": v11.MODE, "v1_record": record})
        for path, sha in old.SOURCE_LOCKS.items():
            self.assertEqual(old.git_blob(old.REPO / path), sha)

    def test_exact_frozen_old_refusal_and_new_immutable_manifest(self):
        previous = old.make_manifest(self.fixture)
        self.assertEqual(old.MANIFEST.read_bytes(), canonical(previous))
        candidate = v11.make_manifest(self.fixture, self.contract)
        self.assertEqual(candidate["outputs"], self.outputs)
        self.assertEqual(candidate["outputs_sha256"],
                         hashlib.sha256(canonical(self.outputs)).hexdigest())
        self.assertEqual(v11.MANIFEST.read_bytes(), canonical(candidate))

    def test_failed_prior_certificate_never_emits_a_new_one(self):
        bad = copy.deepcopy(self.fixture)
        bad["members"][0]["denominator_power_of_two"] = 159
        with self.assertRaisesRegex(AssertionError, "parameter precision"):
            v11.make_outputs(bad)
        bad = copy.deepcopy(self.fixture)
        bad["members"][1]["p"] = 28
        with self.assertRaisesRegex(AssertionError, "physical return period"):
            v11.make_outputs(bad)


if __name__ == "__main__":
    unittest.main()
