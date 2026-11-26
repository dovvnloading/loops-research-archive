#!/usr/bin/env python3
"""Regression tests for code/contribute.py. Standard library only.

    python -B code/test_contribute.py
"""
from __future__ import annotations

import datetime as dt
import json
import unittest
from pathlib import Path

import contribute as c

ROOT = Path(__file__).resolve().parents[1]
GOOD = """---
ledger: MAPPING_TELESCOPE
result: partial
ai: Example Agent 1.0
human_review: none
---

# A title

## Claim
One sentence.

## Evidence
Steps.

## Dependencies
RELATIVE_COVER_LIFT.

## Boundary
Does not close the row.

## Attribution
None beyond the archive.
"""


class LedgerRanking(unittest.TestCase):
    def setUp(self):
        self.ledger = c.Ledger(ROOT)

    def test_ready_rows_are_open_with_closed_prerequisites(self):
        ready = self.ledger.ready()
        self.assertTrue(ready)
        for row in ready:
            self.assertEqual(row["status"], "open")
            for item in self.ledger.pre[row["id"]]:
                self.assertNotEqual(self.ledger.by_id[item]["status"], "open")

    def test_ready_and_blocked_partition_the_open_rows(self):
        ready = {row["id"] for row in self.ledger.ready()}
        blocked = {row["id"] for row in self.ledger.blocked()}
        opened = {row["id"] for row in self.ledger.rows if row["status"] == "open"}
        self.assertFalse(ready & blocked)
        self.assertEqual(ready | blocked, opened)

    def test_downstream_follows_hypothesis_edges(self):
        # UPTCR_IMPLIES_MLC is conditional on this row through `hyp`, not `deps`.
        self.assertIn("UPTCR_IMPLIES_MLC",
                      self.ledger.downstream("UNIVERSAL_PROTECTED_TOWER_CLOSURE"))

    def test_committed_target_list_is_current(self):
        self.assertFalse(c.targets_stale(ROOT),
                         "run `python code/contribute.py targets` and commit the result")

    def test_target_json_never_promotes_a_status(self):
        data = json.loads((ROOT / c.TARGETS_JSON).read_text(encoding="utf-8"))
        for row in data["ready"] + data["blocked"]:
            self.assertEqual(self.ledger.by_id[row["id"]]["status"], "open")
        self.assertEqual(data["counts"]["open"], len(data["ready"]) + len(data["blocked"]))


class Notes(unittest.TestCase):
    def setUp(self):
        self.ledger = c.Ledger(ROOT)

    def test_complete_note_passes(self):
        self.assertEqual(c.note_problems(GOOD, self.ledger), [])

    def test_untouched_template_fails_and_only_its_content_may_wait(self):
        template = (ROOT / c.INBOX / "NOTE_TEMPLATE.md").read_text(encoding="utf-8")
        problems = c.note_problems(template, self.ledger)
        self.assertGreaterEqual(len(problems), len(c.SECTIONS) + 3)
        # The placeholder ID is never acceptable, even in a draft.
        self.assertTrue(any(not may_wait for _, _, may_wait in problems))
        started = template.replace("LEDGER_ID", "MAPPING_TELESCOPE", 1)
        self.assertTrue(all(may_wait for _, _, may_wait in c.note_problems(started, self.ledger)))

    def test_unknown_ledger_id_is_rejected(self):
        problems = c.note_problems(GOOD.replace("MAPPING_TELESCOPE", "MLC_IS_PROVED"), self.ledger)
        self.assertEqual([may_wait for _, _, may_wait in problems], [False])

    def test_missing_boundary_is_rejected(self):
        text = GOOD.replace("## Boundary\nDoes not close the row.\n", "")
        self.assertTrue(any("Boundary" in problem for problem, _, _ in c.note_problems(text, self.ledger)))

    def test_result_must_be_a_known_kind(self):
        text = GOOD.replace("result: partial", "result: proves MLC")
        self.assertTrue(any("result" in problem for problem, _, _ in c.note_problems(text, self.ledger)))

    def test_packet_paths(self):
        self.assertEqual(c.packet_of("contributions/a_20261126/NOTE.md"), "contributions/a_20261126")
        self.assertIsNone(c.packet_of("contributions/README.md"))
        self.assertIsNone(c.packet_of("research/frontier/x/NOTE.md"))


class Claims(unittest.TestCase):
    OPEN = {"MAPPING_TELESCOPE", "H1_CELL_TREE_EXTRACTION", "MBTT"}
    TODAY = dt.date(2026, 11, 26)

    def claims(self, **pull):
        pull = {"number": 7, "html_url": "u", "updated_at": "2026-11-25T00:00:00Z", **pull}
        return c.claimed_ids([pull], self.OPEN, self.TODAY)

    def test_title_claims(self):
        self.assertEqual(list(self.claims(title="[MAPPING_TELESCOPE] degree count")), ["MAPPING_TELESCOPE"])

    def test_body_ledger_line_claims(self):
        found = self.claims(title="work", body="---\nledger: H1_CELL_TREE_EXTRACTION, MBTT\n---")
        self.assertEqual(sorted(found), ["H1_CELL_TREE_EXTRACTION", "MBTT"])

    def test_a_dependency_mentioned_in_prose_is_not_a_claim(self):
        self.assertEqual(self.claims(title="notes", body="This uses MAPPING_TELESCOPE as input."), {})

    def test_closed_or_unknown_ids_are_ignored(self):
        self.assertEqual(self.claims(title="[YOCCOZ] and [NOT_A_ROW]"), {})

    def test_idle_claims_go_stale(self):
        found = self.claims(title="[MBTT] x", updated_at="2026-11-01T00:00:00Z")
        self.assertTrue(found["MBTT"][0]["stale"])
        self.assertFalse(self.claims(title="[MBTT] x")["MBTT"][0]["stale"])


if __name__ == "__main__":
    unittest.main(verbosity=1)
