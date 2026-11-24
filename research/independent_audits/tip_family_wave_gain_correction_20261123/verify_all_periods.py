#!/usr/bin/env python3
"""Compose the corrected tail with the unchanged ten finite-period checks.

The historical finite aggregate calls its historical limiting aggregate and
therefore retains the under-enclosure documented in NOTE.md.  This runner
does not call either historical aggregate.  It explicitly runs the repaired
tail and the ten original finite_case checks, preserving their input gates.
Each branch uses its own interval implementation; no monkeypatching or
cross-module interval-object conversion is used.
"""
from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import sys
from types import ModuleType


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
LEGACY_FINITE = ROOT / "research/independent_audits/tip_family_finite_p_wave_gain_20261116/verify.py"


def load_module(name: str, path: Path) -> ModuleType:
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Cannot import certificate source: {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module


corrected = load_module("tip_corrected_tail_20261123", HERE / "verify.py")
finite = load_module("tip_original_finite_cases_20261116", LEGACY_FINITE)


def certify() -> dict[str, object]:
    # This is the sole aggregate tail certificate used by this runner.
    tail = corrected.certify()

    # These are the input gates from the historical finite certify().  The
    # BLOCKS test preserves its finite geometric-incidence check; the current
    # physical proof does not promote that table to an immersion marking.
    old = json.loads(finite.gain.s.OLD.read_text())
    finite.require([row["p"] for row in old["periods"]] == list(range(3, 13)),
                   "ten dyadic primitive-tip source packets not found")
    finite.require(finite.gain.s.BLOCKS[0] == (18, 19, 0, 1, 2)
                   and finite.gain.s.BLOCKS[1] == (3, 4)
                   and finite.gain.s.BLOCKS[9] == (16, 17),
                   "historical source-block incidence data changed")
    results = []
    for row in old["periods"]:
        p, c, orbit = finite.v.checked_packet(row)
        results.append(finite.finite_case(p, c, orbit))
    finite.require([row["p"] for row in results] == list(range(3, 13)),
                   "finite-period certificate did not cover exactly p=3,...,12")
    return {"tail": tail, "finite": results}


def main() -> None:
    result = certify()
    for row in result["finite"]:
        print(f'p={row["p"]:2d} {row["construction"]}: '
              f'P>{row["proved_parent_gt"]}, C<{row["proved_child_lt"]}, '
              f'D>{row["proved_D_gt"]}; '
              f'interval D*1e6={row["defect_strict_lower_1e-6"]}')
    tail = result["tail"]
    for key in ("p13_parent_disk_lower", "p_ge_14_parent_disk_lower"):
        interval = tail[key]
        print(f"{key}: {corrected.v.bracket_dec(interval, 9)} (outer bounds * 1e9)")
    print(f'PASS: repaired p>=13 defect floor {tail["all_p_defect_strict_floor"]}.')
    print("PASS: all p>=3 independent defect >1/100; ten finite cases, "
          "actual p=13 isolation, and corrected uniform tail from p=14.")
    print("Neither the historical limiting nor finite aggregate was used. Analytic interpretation and "
          "the open full immersion-marking obligation are stated in NOTE.md.")


if __name__ == "__main__":
    main()
