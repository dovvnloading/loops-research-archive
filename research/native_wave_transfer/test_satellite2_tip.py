"""Adversarial exact tip refusal tests: do not invent primitive Wave outputs."""
from __future__ import annotations

import copy
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import regenerate_satellite2_tip as tip


class MisiurewiczSatelliteTipTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.fixture = json.loads(tip.INPUT.read_text(encoding="utf-8"))

    def mutate_fails(self, mutation, message):
        example = copy.deepcopy(self.fixture)
        mutation(example)
        with self.assertRaisesRegex(AssertionError, message):
            tip.exact_certificate(example)

    def test_exact_positive_certificate_and_refusal(self):
        result = tip.exact_certificate(self.fixture)
        self.assertTrue(result["parameter"]["unique_real_root_by_positive_derivative"])
        self.assertEqual(result["central_return"]["rouche_margin_strictly_greater_than"], "1/5")
        self.assertTrue(result["central_return"]["noncentral_critical_points_outside_target_disk"])
        self.assertTrue(result["central_return"]["central_component_compactly_contained_in_target"])
        geom = result["exact_real_geometry"]
        self.assertEqual(geom["inner_invariant_interval"], "[-a,a]")
        self.assertEqual(geom["other_phase_interval"], "[c,-a]")
        self.assertEqual(geom["intersection_of_phases"], "{-a}")
        self.assertTrue(geom["central_real_inverse_tree_equals_inner_interval"])
        self.assertEqual(geom["new_attachments"], 0)
        self.assertEqual(geom["inner_old_edge_count_under_KKL_vertex_convention"], 0)
        self.assertEqual(result["compatibility"]["first_incompatible_field"],
                         "MarkedHubbardTree.small_julia_intervals")
        self.assertFalse(result["compatibility"]["v1_example_emitted"])
        for key in ("filtered_two_versus_one", "perron_root_of_old_edge_matrix",
                    "zero_old_edge_wave_crests", "parent_and_child_wave_widths"):
            self.assertIsNone(result["compatibility"][key])

    def test_root_mutations_are_rejected(self):
        self.mutate_fails(lambda o: o["parameter"].__setitem__("lower_numerator",
                          str(int(o["parameter"]["lower_numerator"])-1)),
                          "not adjacent")
        self.mutate_fails(lambda o: (o["parameter"].__setitem__("lower_numerator",
                          str(int(o["parameter"]["lower_numerator"])+1)),
                          o["parameter"].__setitem__("upper_numerator",
                          str(int(o["parameter"]["upper_numerator"])+1))),
                          "root signs")
        self.mutate_fails(lambda o: o["parameter"].__setitem__(
                          "denominator_power_of_two",127), "precision drift")
        self.mutate_fails(lambda o: o["parameter"].__setitem__(
                          "equation","x4=0"), "critical orbit polynomial")

    def test_physical_return_and_refusal_cannot_be_forged(self):
        self.mutate_fails(lambda o: o["renormalization"].__setitem__(
                          "restricted_degree",4), "physical return/domain")
        self.mutate_fails(lambda o: o["renormalization"].__setitem__(
                          "target","D(0,4/5)"), "physical return/domain")
        self.mutate_fails(lambda o: o.__setitem__(
                          "source_contract","source_contracts/record_fields.json"),
                          "forged v1 marking field")
        self.mutate_fails(lambda o: o.__setitem__(
                          "marking",{"target_cuts":[]}), "forged v1 marking field")
        self.mutate_fails(lambda o: o.__setitem__(
                          "record_compatibility","compatible"), "must not claim")
        self.mutate_fails(lambda o: o.__setitem__(
                          "first_incompatible_field","WaveFamily.target_width"),
                          "first semantic refusal")
        self.mutate_fails(lambda o: o["not_asserted"].pop(), "unasserted")

    def test_baselines_and_immutable_manifest(self):
        baseline = tip.primitive_baselines()
        self.assertEqual(baseline["p3"]["target_atoms"], 10)
        self.assertEqual(baseline["p4"]["source_atoms"], 20)
        self.assertEqual(baseline["p3"]["filtered_restrictions"], [2,1])
        self.assertTrue(baseline["p4"]["harmonic_equality"])
        computed = tip.make_manifest(self.fixture)
        self.assertEqual(tip.MANIFEST.read_bytes(),tip.canonical(computed))
        self.assertEqual(computed["outputs_sha256"],
                         tip.hashlib.sha256(tip.canonical(computed["outputs"])).hexdigest())
        with tempfile.TemporaryDirectory() as folder:
            changed = Path(folder)/"tip.json"
            changed.write_bytes(tip.INPUT.read_bytes()+b"\n")
            with patch.object(tip,"INPUT",changed):
                self.assertNotEqual(tip.make_manifest(self.fixture)["inputs"]["example_sha256"],
                                    computed["inputs"]["example_sha256"])

    def test_source_and_prior_manifests_remain_byte_locked(self):
        for name, blob in tip.SOURCE_LOCKS.items():
            with self.subTest(source=name):
                self.assertEqual(tip.git_blob(tip.ROOT/name),blob)
        for name,blob in tip.UNCHANGED_BLOBS.items():
            with self.subTest(unchanged=name):
                self.assertEqual(tip.git_blob(tip.HERE/name),blob)


if __name__ == "__main__":
    unittest.main()
