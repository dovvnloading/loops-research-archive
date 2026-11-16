"""Adversarial satellite refusal: require exact proofs, refuse fake v1 data."""
from __future__ import annotations

import copy
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import regenerate_satellite2 as sat

PRIMITIVE_BLOBS = {
    "physical_examples/tip_pr68.json": "65ecc49937b3c341005407a59b353b38f804afec",
    "physical_examples/primitive4_tip12.json": "d0154c8aec14b9355ed81144075486306ee7ab89",
    "physical_examples/primitive4_tip12_parameter.json": "99192901551611390ef8d5ab81458e8316a9c70b",
    "experiment_manifests/tip_pr68.json": "39233f576e7de78cf707b4d616177d0313b98b25",
    "experiment_manifests/primitive4_tip12.json": "abcc01ad0b5ab0b59cd46e9d080ce44141603392",
    "regenerate.py": "0dfa4f4c8d5321a7b9fdd74c9c1218228087e0f2",
    "regenerate_period4.py": "00bae744fbf752beb98994930fe666c02bb652c8",
}


class SatelliteRefusalTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.input = json.loads(sat.INPUT.read_text(encoding="utf-8"))

    def mutate_fails(self, edit: object, error: str) -> None:
        fixture = copy.deepcopy(self.input)
        edit(fixture)
        with self.assertRaisesRegex(AssertionError, error):
            sat.certify(fixture)

    def test_valid_exact_certificate(self) -> None:
        out = sat.certify(self.input)
        self.assertTrue(out["parameter"]["unique_real_parameter_in_bracket"])
        self.assertEqual(out["central_return"]["rouche_margin_strictly_gt"], "3/50")
        self.assertTrue(out["central_return"]["alpha_in_both_physical_phase_filled_sets"])
        self.assertTrue(out["central_return"]["K_of_G_has_nonempty_complex_interior"])
        self.assertFalse(out["compatibility"]["physical_example_v1_emitted"])
        self.assertEqual(out["compatibility"]["first_incompatible_field"],
                         "MarkedHubbardTree.small_julia_intervals")
        self.assertIn("not defined", out["compatibility"]["wave_harmonic_verdict"])
        self.assertEqual(len(out["compatibility"]["uncertified_satellite_observables"]), 6)

    def test_dyadic_root_mutations(self) -> None:
        self.mutate_fails(lambda o: o["parameter"].__setitem__("upper_numerator",
                           o["parameter"]["upper_numerator"] + 1), "adjacent dyadics")
        self.mutate_fails(lambda o: o["parameter"].__setitem__("lower_numerator",
                           o["parameter"]["lower_numerator"] - 1), "adjacent dyadics")
        self.mutate_fails(lambda o: (o["parameter"].__setitem__("lower_numerator",
                           o["parameter"]["lower_numerator"] + 1),
                           o["parameter"].__setitem__("upper_numerator",
                           o["parameter"]["upper_numerator"] + 1)), "root sign change")
        self.mutate_fails(lambda o: o["parameter"].__setitem__("denominator_power_of_two", 127),
                          "precision changed")
        self.mutate_fails(lambda o: o["parameter"].__setitem__("equation", "x2=0"),
                          "parameter equation")

    def test_no_forged_interval_or_operations(self) -> None:
        self.mutate_fails(lambda o: o.__setitem__("source_contract", "fake/v1"),
                          "must not be forged")
        self.mutate_fails(lambda o: o.__setitem__("marking", {"target_cuts": []}),
                          "must not be forged")
        self.mutate_fails(lambda o: o.__setitem__("first_incompatible_field",
                                                  "AttachmentCensus.components[].interval"),
                          "first incompatible")
        self.mutate_fails(lambda o: o.__setitem__("record_compatibility", "compatible"),
                          "refusal removed")
        self.mutate_fails(lambda o: o["renormalization"].__setitem__("physical_iterate", 4),
                          "central return")
        self.mutate_fails(lambda o: o["renormalization"].__setitem__("restricted_degree", 4),
                          "central return")
        self.mutate_fails(lambda o: o["not_asserted"].pop(), "uncomputed observables")

    def test_immutable_manifest_canonical_bytes(self) -> None:
        expected = sat.canonical(sat.manifest(self.input))
        self.assertEqual(sat.MANIFEST.read_bytes(), expected)
        self.assertTrue(expected.endswith(b"\n"))
        self.assertEqual(json.loads(expected)["outputs_sha256"],
                         sat.manifest(self.input)["outputs_sha256"])
        with tempfile.TemporaryDirectory() as td:
            tampered = Path(td) / "input.json"
            tampered.write_bytes(sat.INPUT.read_bytes() + b"\n")
            with patch.object(sat, "INPUT", tampered):
                self.assertNotEqual(sat.manifest(self.input)["inputs"]["example_sha256"],
                                    json.loads(expected)["inputs"]["example_sha256"])

    @unittest.skipUnless((sat.ROOT / "research/native_wave_transfer/SPECIFICATION.md").exists(),
                         "full repository source files not present in local isolated test")
    def test_locked_sources_and_untouched_primitive_blobs(self) -> None:
        for name, expected in sat.SOURCE_LOCKS.items():
            with self.subTest(source=name):
                self.assertEqual(sat.git_blob(sat.ROOT / name), expected)
        for name, expected in PRIMITIVE_BLOBS.items():
            with self.subTest(primitive=name):
                self.assertEqual(sat.git_blob(sat.HERE / name), expected)


if __name__ == "__main__":
    unittest.main()
