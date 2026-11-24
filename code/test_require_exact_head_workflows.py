#!/usr/bin/env python3
"""Synthetic gh run-list cases; no network access or workflow dispatch."""
from __future__ import annotations

import copy
import json
import unittest

import require_exact_head_workflows as gate

SHA = "a"*40
OTHER = "b"*40


def run(identifier: int, status: str, conclusion=None, sha: str = SHA) -> dict:
    return json.loads(json.dumps({
        "databaseId": identifier, "headSha": sha,
        "status": status, "conclusion": conclusion,
    }))


class FakeGitHub:
    def __init__(self, responses: dict, heads=None):
        self.responses = copy.deepcopy(responses)
        self.heads = list(heads or [SHA, SHA])
        self.dispatched = []

    def head_sha(self):
        return self.heads.pop(0) if len(self.heads) > 1 else self.heads[0]

    def runs(self, workflow):
        responses = self.responses[workflow]
        return responses.pop(0) if len(responses) > 1 else responses[0]

    def dispatch(self, workflow):
        self.dispatched.append(workflow)


class ExactHeadWorkflowTests(unittest.TestCase):
    def client(self, responses, heads=None):
        return FakeGitHub(
            {workflow: copy.deepcopy(responses) for workflow in gate.REQUIRED_WORKFLOWS},
            heads=heads,
        )

    def require(self, client, attempts=4):
        gate.require_exact_head(
            client, SHA, attempts=attempts, interval=1,
            sleep=lambda _: None, emit=lambda _: None,
        )

    def test_success_precedes_newer_cancelled_and_failed_runs(self):
        runs = [run(30, "completed", "cancelled"),
                run(20, "completed", "failure"),
                run(10, "completed", "success")]
        self.assertEqual(gate.select_run(runs, SHA)["databaseId"], 10)

    def test_active_replacement_precedes_cancelled_and_failed_runs(self):
        runs = [run(30, "completed", "cancelled"),
                run(20, "in_progress"), run(10, "completed", "failure")]
        self.assertEqual(gate.select_run(runs, SHA)["databaseId"], 20)

    def test_newest_matching_success_is_selected(self):
        runs = [run(10, "completed", "success"), run(20, "completed", "success")]
        self.assertEqual(gate.select_run(runs, SHA)["databaseId"], 20)

    def test_success_at_wrong_sha_cannot_satisfy_gate(self):
        client = self.client([[run(1, "completed", "success", OTHER)]])
        with self.assertRaisesRegex(gate.GateError, "No successful exact-head"):
            self.require(client, attempts=2)
        self.assertEqual(client.dispatched, list(gate.REQUIRED_WORKFLOWS))

    def test_existing_success_is_reused_without_dispatch(self):
        client = self.client([[run(1, "completed", "success")]])
        self.require(client)
        self.assertEqual(client.dispatched, [])

    def test_active_run_is_reused_and_cancellation_replacement_followed(self):
        client = self.client([
            [run(1, "in_progress")],
            [run(1, "completed", "cancelled")],
            [run(2, "queued"), run(1, "completed", "cancelled")],
            [run(2, "completed", "success"), run(1, "completed", "cancelled")],
        ])
        self.require(client)
        self.assertEqual(client.dispatched, [])

    def test_initial_cancelled_only_run_gets_one_replacement_dispatch(self):
        client = self.client([
            [run(1, "completed", "cancelled")],
            [run(2, "completed", "success")],
        ])
        self.require(client)
        self.assertEqual(client.dispatched, list(gate.REQUIRED_WORKFLOWS))

    def test_cancelled_only_polling_cannot_pass(self):
        client = self.client([[run(1, "completed", "cancelled")]])
        with self.assertRaisesRegex(gate.GateError, "No successful exact-head"):
            self.require(client, attempts=2)

    def test_noncancelled_failed_check_remains_fatal(self):
        for conclusion in ("failure", "timed_out", "action_required",
                           "startup_failure", "skipped", "neutral"):
            with self.subTest(conclusion=conclusion):
                client = self.client([[run(1, "completed", conclusion)]])
                with self.assertRaisesRegex(gate.GateError, "failed check is fatal"):
                    self.require(client)
                self.assertEqual(client.dispatched, [])

    def test_failure_after_dispatch_remains_fatal(self):
        client = self.client([[], [run(1, "completed", "failure")]])
        with self.assertRaisesRegex(gate.GateError, "failed check is fatal"):
            self.require(client)

    def test_both_original_workflows_are_required(self):
        client = FakeGitHub({
            "lean-proofs.yml": [[run(1, "completed", "success")]],
            "weighted-lean.yml": [[run(2, "completed", "cancelled")]],
        })
        with self.assertRaisesRegex(gate.GateError, "weighted-lean.yml"):
            self.require(client, attempts=2)

    def test_head_move_before_validation_fails_without_dispatch(self):
        client = self.client([[run(1, "completed", "success")]], heads=[OTHER])
        with self.assertRaisesRegex(gate.GateError, "head moved before"):
            self.require(client)
        self.assertEqual(client.dispatched, [])

    def test_head_move_after_success_is_fatal(self):
        client = self.client([[run(1, "completed", "success")]], heads=[SHA, OTHER])
        with self.assertRaisesRegex(gate.GateError, "head moved during"):
            self.require(client)


if __name__ == "__main__":
    unittest.main()
