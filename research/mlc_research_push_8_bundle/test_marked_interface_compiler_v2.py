#!/usr/bin/env python3
from __future__ import annotations

import json
import random
import subprocess
from pathlib import Path

from marked_interface_compiler_v2 import (
    MarkingFailure,
    brute_force_valid_markings,
    compile_marked_interface,
)

ROOT = Path(__file__).resolve().parent


def load(name: str) -> dict:
    return json.loads((ROOT / name).read_text())


def deterministic_tests() -> list[str]:
    messages = []
    success = load("marked_interface_success.json")
    out = compile_marked_interface(success)
    assert out["selected_action_endpoints"] == [0, 2, 4, 6, 8]
    assert out["response_only_trace_endpoints"] == [1, 3, 5, 7]
    assert all(
        rec["end_proper"]
        for recs in out["selected_action_details"]["immersion_components"].values()
        for rec in recs
    )
    messages.append("success fixture: action/trace separation and end-proper flags")

    for name, fragment in [
        ("marked_interface_obstruction_mandatory.json", "split an immersion-forced block"),
        ("marked_interface_obstruction_covering.json", "no coarsening"),
    ]:
        try:
            compile_marked_interface(load(name))
        except MarkingFailure as exc:
            assert fragment in str(exc)
        else:
            raise AssertionError(f"{name} should obstruct")
        messages.append(f"obstruction fixture: {name}")
    return messages


def random_payload(rng: random.Random) -> dict:
    n = rng.randint(2, 7)
    m = rng.randint(2, 10)
    atoms = []
    for _ in range(m):
        imm = None if rng.random() < 0.35 else rng.randrange(n)
        atoms.append({"imm_micro": imm, "cov_micro": rng.randrange(n)})
    cov_vertices = [rng.randrange(n + 1) for _ in range(m + 1)]
    # Preserve the phase seam at the two ends of the linearized source.
    cov_vertices[0] = 0
    cov_vertices[-1] = n
    mandatory = [0, n]
    for v in range(1, n):
        if rng.random() < 0.22:
            mandatory.append(v)
    trace = sorted(set(mandatory + [v for v in range(1, n) if rng.random() < 0.55]))
    return {
        "target_micro_count": n,
        "seam_vertex": 0,
        "mandatory_ideal_endpoints": mandatory,
        "trace_overlay_endpoints": trace,
        "source_atoms": atoms,
        "source_vertex_cov_image": cov_vertices,
    }


def randomized_oracle_test(seed: int = 20260725, trials: int = 1500) -> dict:
    rng = random.Random(seed)
    compiled = 0
    obstructed = 0
    maximal_mismatch = 0
    false_positive = 0
    false_negative = 0
    for _ in range(trials):
        payload = random_payload(rng)
        brute = brute_force_valid_markings(payload)
        try:
            out = compile_marked_interface(payload)
            compiled += 1
            selected = out["selected_action_endpoints"]
            if not brute:
                false_positive += 1
                continue
            max_len = max(map(len, brute))
            maximal = [x for x in brute if len(x) == max_len]
            if selected not in maximal:
                maximal_mismatch += 1
        except MarkingFailure:
            obstructed += 1
            if brute:
                false_negative += 1
    assert false_positive == 0
    assert false_negative == 0
    assert maximal_mismatch == 0
    return {
        "seed": seed,
        "trials": trials,
        "compiled": compiled,
        "obstructed": obstructed,
        "false_positive": false_positive,
        "false_negative": false_negative,
        "maximal_marking_mismatch": maximal_mismatch,
    }


def main() -> None:
    messages = deterministic_tests()
    report = randomized_oracle_test()
    report["deterministic_tests"] = messages
    (ROOT / "marked_interface_test_report.json").write_text(
        json.dumps(report, indent=2, sort_keys=True)
    )
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
