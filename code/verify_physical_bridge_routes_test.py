#!/usr/bin/env python3
"""Adversarial regression tests for documentary claim-status promotion.

These tests establish checker behavior, not the mathematics in a route.
Run: python3 -B code/verify_physical_bridge_routes_test.py
"""

import unittest

from verify_physical_bridge_routes import check_dependencies, read_register


class DependencyPromotionTests(unittest.TestCase):
    def test_unresolved_premise_cannot_be_laundered_through_model(self):
        # The former direct-edge check accepted this false promotion.
        for claimed in ("formal", "written", "imported"):
            for unfinished in ("open", "conditional", "diagnostic"):
                with self.subTest(claimed=claimed, unfinished=unfinished):
                    routes = {
                        "UNRESOLVED": (unfinished, []),
                        "MODEL": ("model", ["UNRESOLVED"]),
                        "CLAIM": (claimed, ["MODEL"]),
                    }
                    with self.assertRaisesRegex(
                        ValueError, r"CLAIM -> MODEL -> UNRESOLVED"
                    ):
                        check_dependencies(routes)

    def test_multiple_model_steps_preserve_the_unresolved_premise(self):
        routes = {
            "OPEN": ("open", []),
            "MODEL-A": ("model", ["OPEN"]),
            "MODEL-B": ("model", ["MODEL-A"]),
            "CLAIM": ("formal", ["MODEL-B"]),
        }
        with self.assertRaisesRegex(ValueError, r"CLAIM -> MODEL-B -> MODEL-A -> OPEN"):
            check_dependencies(routes)

    def test_standalone_model_and_conditional_claim_remain_allowed(self):
        check_dependencies({
            "OPEN": ("open", []),
            "MODEL": ("model", ["OPEN"]),
            "CONDITIONAL": ("conditional", ["MODEL"]),
        })

    def test_model_with_discharged_inputs_can_support_a_standing_claim(self):
        check_dependencies({
            "THEOREM": ("formal", []),
            "SOURCE": ("imported", []),
            "MODEL": ("model", ["THEOREM", "SOURCE"]),
            "CLAIM": ("written", ["MODEL", "THEOREM"]),
        })

    def test_shortest_dependency_witness_is_reported(self):
        routes = {
            "OPEN": ("open", []),
            "MODEL-A": ("model", ["OPEN"]),
            "MODEL-B": ("model", ["MODEL-A"]),
            "CLAIM": ("formal", ["MODEL-B", "OPEN"]),
        }
        with self.assertRaisesRegex(ValueError, r"CLAIM -> OPEN \(open\)"):
            check_dependencies(routes)

    def test_cycle_and_missing_inputs_remain_rejected(self):
        with self.assertRaisesRegex(ValueError, "Circular bridge"):
            check_dependencies({"A": ("model", ["B"]), "B": ("model", ["A"])})
        with self.assertRaisesRegex(ValueError, "unknown premise"):
            check_dependencies({"A": ("formal", ["MISSING"])})

    def test_current_archive_routes_keep_their_declared_statuses(self):
        check_dependencies(read_register())


if __name__ == "__main__":
    unittest.main()
