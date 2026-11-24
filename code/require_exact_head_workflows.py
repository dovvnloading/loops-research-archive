#!/usr/bin/env python3
"""Require both original CI workflows at one exact PR head.

Audit workflows may reach this gate concurrently. Reuse exact-head dispatches
and follow active replacements after concurrency cancellation. A cancelled run
never counts as success; actual failed checks remain fatal.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import sys
import time
from typing import Callable

REQUIRED_WORKFLOWS = ("lean-proofs.yml", "weighted-lean.yml")


class GateError(RuntimeError):
    pass


def select_run(runs: list[dict], sha: str) -> dict | None:
    """Prefer exact-head success, then active, then failure, then cancellation."""
    matches = [run for run in runs if run.get("headSha") == sha]

    def priority(run: dict) -> tuple[int, int]:
        status, conclusion = run.get("status"), run.get("conclusion")
        if status == "completed" and conclusion == "success":
            rank = 0
        elif status != "completed":
            rank = 1
        elif conclusion != "cancelled":
            rank = 2
        else:
            rank = 3
        return rank, -int(run["databaseId"])

    return min(matches, key=priority) if matches else None


def reject_failure(workflow: str, run: dict | None) -> None:
    if (run and run.get("status") == "completed"
            and run.get("conclusion") not in ("success", "cancelled")):
        raise GateError(
            f"{workflow}: exact-head run {run['databaseId']} concluded "
            f"{run.get('conclusion')!r}; a noncancelled failed check is fatal"
        )


class GitHub:
    def __init__(self, repo: str, branch: str):
        self.repo, self.branch = repo, branch

    @staticmethod
    def command(*args: str) -> str:
        return subprocess.run(
            ["gh", *args], check=True, text=True, capture_output=True
        ).stdout.strip()

    def head_sha(self) -> str:
        return self.command(
            "api", f"repos/{self.repo}/git/ref/heads/{self.branch}",
            "--jq", ".object.sha"
        )

    def runs(self, workflow: str) -> list[dict]:
        result = json.loads(self.command(
            "run", "list", "--repo", self.repo, "--workflow", workflow,
            "--branch", self.branch, "--event", "workflow_dispatch",
            "--limit", "100", "--json", "databaseId,headSha,status,conclusion"
        ))
        if not isinstance(result, list):
            raise GateError(f"{workflow}: unexpected run-list response")
        return result

    def dispatch(self, workflow: str) -> None:
        self.command(
            "workflow", "run", workflow, "--repo", self.repo, "--ref", self.branch
        )


def require_exact_head(
    client: GitHub,
    sha: str,
    *,
    attempts: int = 360,
    interval: float = 15,
    sleep: Callable[[float], None] = time.sleep,
    emit: Callable[[str], None] = print,
) -> None:
    if attempts <= 0 or not 0 < interval <= 60:
        raise GateError("positive bounded polling parameters are required")
    if client.head_sha() != sha:
        raise GateError("PR head moved before original workflow validation")

    for workflow in REQUIRED_WORKFLOWS:
        run = select_run(client.runs(workflow), sha)
        reject_failure(workflow, run)
        if run and (run.get("status") != "completed"
                    or run.get("conclusion") == "success"):
            emit(f"Reusing {workflow} exact-head run {run['databaseId']}")
        else:
            # Two callers can still race here. The polling rule below follows
            # the surviving run rather than failing on its cancelled sibling.
            client.dispatch(workflow)
            emit(f"Dispatched {workflow} for {sha}")

    pending = set(REQUIRED_WORKFLOWS)
    for attempt in range(attempts):
        for workflow in REQUIRED_WORKFLOWS:
            if workflow not in pending:
                continue
            run = select_run(client.runs(workflow), sha)
            reject_failure(workflow, run)
            if (run and run.get("status") == "completed"
                    and run.get("conclusion") == "success"):
                emit(f"PASS {workflow} at {sha}: run {run['databaseId']}")
                pending.remove(workflow)
            # Missing, active, or cancelled-only responses wait for a
            # replacement. None can satisfy the exact-head success gate.
        if not pending:
            break
        if attempt + 1 < attempts:
            sleep(interval)
    if pending:
        raise GateError(
            "No successful exact-head dispatch within the polling bound: "
            + ", ".join(sorted(pending))
        )
    if client.head_sha() != sha:
        raise GateError("PR head moved during original workflow validation")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--attempts", type=int, default=360)
    parser.add_argument("--interval", type=float, default=15)
    args = parser.parse_args()
    try:
        repo, branch, sha = (os.environ[key] for key in ("REPO", "PR_BRANCH", "PR_SHA"))
        if not re.fullmatch(r"[0-9a-fA-F]{40}", sha):
            raise GateError("PR_SHA must be the exact 40-digit commit ID")
        require_exact_head(
            GitHub(repo, branch), sha, attempts=args.attempts, interval=args.interval
        )
    except (KeyError, GateError, ValueError, subprocess.CalledProcessError) as exc:
        print(f"Exact-head workflow gate failed: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
