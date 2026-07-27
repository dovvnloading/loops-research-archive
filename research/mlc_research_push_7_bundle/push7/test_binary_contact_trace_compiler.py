#!/usr/bin/env python3
from __future__ import annotations

import copy
import json
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

from binary_contact_trace_compiler import (  # noqa: E402
    AtlasRecord,
    BinaryContactCompiler,
    CompilerError,
)


class BinaryContactCompilerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.source = json.loads((HERE / "source_binary_contact_example.json").read_text())

    def compiler(self, data=None) -> BinaryContactCompiler:
        return BinaryContactCompiler(AtlasRecord.from_json(data or copy.deepcopy(self.source)))

    def test_valid_example(self) -> None:
        report = self.compiler().compile(horizon=6, functoriality_depth=4)
        self.assertTrue(report["passed"])
        self.assertEqual(
            {x["parent_edge"] for x in report["source_boundary_contacts"]["L"]},
            {"r_LLL", "r_LLR", "r_LRL", "r_LRR"},
        )
        self.assertEqual(
            {x["parent_edge"] for x in report["source_boundary_contacts"]["R"]},
            {"r_RLL", "r_RLR", "r_RRL", "r_RRR"},
        )

    def test_corner_contacts_force_subdivision(self) -> None:
        report = self.compiler().compile(horizon=1, functoriality_depth=1)
        left = report["source_boundary_graph"]["L"]
        self.assertGreater(len(left["point_contacts"]), 0)
        self.assertTrue(any(x["subdivide_parent"] for x in left["point_contacts"]))

    def test_wrong_declared_contact_rejected_by_report(self) -> None:
        data = copy.deepcopy(self.source)
        data["branches"]["L"]["contact_atoms"] = ["r_LLL"]
        report = self.compiler(data).compile(horizon=2, functoriality_depth=2)
        self.assertFalse(report["passed"])
        self.assertEqual(len(report["source_contact_failures"]), 1)

    def test_refinement_non_naturality_detected(self) -> None:
        data = copy.deepcopy(self.source)
        data["refinement"]["branches"]["L"]["refined_child_parent"]["L_r_LLL_a"] = "r_LLR"
        report = self.compiler(data).compile(horizon=2, functoriality_depth=2)
        self.assertFalse(report["passed"])
        self.assertGreater(len(report["refinement_naturality"]["failures"]), 0)

    def test_duplicate_depth_n_vertex_rejected(self) -> None:
        data = copy.deepcopy(self.source)
        data["vertex_by_word"]["LLL"] = data["vertex_by_word"]["LLR"]
        with self.assertRaises(CompilerError):
            self.compiler(data).source_vertex_shift_checks()

    def test_contact_recursion_known_values(self) -> None:
        compiler = self.compiler()
        self.assertEqual(
            compiler.state_for_word("L"),
            frozenset({"r_LLL", "r_LRL", "r_RLL", "r_RRL"}),
        )
        self.assertEqual(
            compiler.state_for_word("LL"), frozenset({"r_LLL", "r_RLL"})
        )
        for word in ("LLL", "LLR", "LRL", "LRR", "RLL", "RLR", "RRL", "RRR"):
            self.assertEqual(compiler.state_for_word(word), frozenset({"r_LLL"}))
        self.assertEqual(compiler.state_for_word("LLLL"), frozenset({"r_LLL"}))
        self.assertEqual(compiler.state_for_word("LLLR"), frozenset())

    def test_post_transient_synchronization(self) -> None:
        report = self.compiler().compile(horizon=5, functoriality_depth=3)
        sync = report["synchronization"]
        self.assertTrue(sync["present"])
        self.assertEqual(sync["failures"], [])
        self.assertEqual(sync["persistent_state"], ["r_LLL"])
        self.assertEqual(sync["kill_branch_images"]["R"], [])

    def test_one_to_many_multiplicity_at_most_two(self) -> None:
        atlas = self.compiler().one_to_many_atlas()
        self.assertTrue(all(len(lifts) <= 2 for lifts in atlas.values()))
        self.assertTrue(all(len(lifts) == 2 for lifts in atlas.values()))


if __name__ == "__main__":
    unittest.main(verbosity=2)
