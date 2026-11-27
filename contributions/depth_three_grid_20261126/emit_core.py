#!/usr/bin/env python3
"""Emit the fixed 27-row Lean arithmetic census from the exact packet data.

Generation is not a proof. Each emitted root and geometry statement is
re-evaluated by Lean's kernel; the complete finite word census is checked too.
Run from any directory. This writes only DepthThreeGrid.lean.
"""
from __future__ import annotations

import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent


def box(values: list[int]) -> str:
    return "⟨" + ", ".join(map(str, values)) + "⟩"


def main() -> None:
    data = json.loads((HERE / "data.json").read_text())
    rows = sorted(data["rows"], key=lambda row: row["word"])
    expected = [[p, q, r] for p in (3, 4, 5) for q in (3, 4, 5) for r in (3, 4, 5)]
    if [row["word"] for row in rows] != expected:
        raise ValueError("The exact data must cover all 27 words once")
    names = ["packet" + "".join(map(str, row["word"])) for row in rows]
    out = [
        "import DepthThreeCert", "", 
        "/-!", "# Complete exact census of the 27 depth-three arithmetic charts", "",
        "Generated from contributions/depth_three_grid_20261126/data.json.",
        "The 26 rows other than (3,3,3) are the previously missing finite grid.",
        "Every root and disk statement below is computed again by the kernel.",
        "The old row is retained as a regression; it is not counted as new.",
        "-/", "", "namespace LoopsFormal.DepthThreeGrid", "",
        "open LoopsFormal.Period27 LoopsFormal.DepthThree", "",
        "set_option maxRecDepth 100000", "set_option maxHeartbeats 100000000", "",
        f"def gridScale : Int := 2 ^ {data['scale_bits']}", "",
    ]
    for row, name in zip(rows, names):
        p, q, r = row["word"]
        suffix = name.removeprefix("packet")
        out += [f"def {name} : Packet :=", "  {", f"    p := {p}, q := {q}, r := {r}",
                f"    parameter := {box(row['parameter'])}"]
        out += [f"    radius{i} := {box(radius)}" for i, radius in enumerate(row["radii"], 1)]
        out += [f"    {key} := {box(row[key])}" for key in ("alpha", "reference2", "reference1")]
        out += ["  }", "", f"theorem root{suffix} : RootCertificate gridScale {p*q*r} {name}.parameter := by",
                "  decide +kernel", "",
                f"theorem geometry{suffix} : GeometryCertificate gridScale {name} := by",
                "  decide +kernel", ""]
    out += ["def gridPackets : List Packet :=", "  [" + ", ".join(names) + "]", "",
            "def remainingPackets : List Packet :=", "  [" + ", ".join(names[1:]) + "]", "",
            "/-- Every one of the 27 explicit rows passes both independent checks. -/",
            "theorem allGridCertificates (P : Packet) (hP : P ∈ gridPackets) :",
            "    RootCertificate gridScale (P.p * P.q * P.r) P.parameter ∧",
            "      GeometryCertificate gridScale P := by",
            "  simp only [gridPackets, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hP",
            "  rcases hP with " + " | ".join(["rfl"] * len(rows))]
    for name in names:
        suffix = name.removeprefix("packet")
        out += [f"  · exact ⟨root{suffix}, geometry{suffix}⟩"]
    out += ["", "/-- The displayed rows exhaust the full product, not a sampled subset. -/",
            "theorem gridComplete (p q r : Nat)",
            "    (hp : p ∈ ([3,4,5] : List Nat)) (hq : q ∈ ([3,4,5] : List Nat))",
            "    (hr : r ∈ ([3,4,5] : List Nat)) :",
            "    ∃ P ∈ gridPackets, P.p = p ∧ P.q = q ∧ P.r = r := by",
            "  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp hq hr",
            "  rcases hp with rfl | rfl | rfl <;>",
            "    rcases hq with rfl | rfl | rfl <;>",
            "    rcases hr with rfl | rfl | rfl"]
    for name in names:
        out += [f"  · exact ⟨{name}, by simp [gridPackets], rfl, rfl, rfl⟩"]
    out += ["", "/-- The common scale is strictly positive. -/",
            "theorem gridScale_positive : 0 < gridScale := by decide +kernel", "",
            "theorem gridCount : gridPackets.length = 27 := by decide +kernel", "",
            "/-- The real root charts are strictly disjoint even at their endpoints. -/",
            "theorem parameterChartsSeparated :",
            "    gridPackets.Pairwise (fun P Q =>",
            "      P.parameter.hi < Q.parameter.lo ∨ Q.parameter.hi < P.parameter.lo) := by",
            "  decide +kernel", "",
            "/-- The new packets retain the full-grid verification evidence. -/",
            "theorem remaining_subset_grid {P : Packet} (h : P ∈ remainingPackets) : P ∈ gridPackets := by",
            "  change P ∈ packet333 :: remainingPackets",
            "  exact List.mem_cons_of_mem _ h", "",
            "/-- Exactly the 26 unarchived words, with no duplication of a word. -/",
            "theorem remainingCount : remainingPackets.length = 26 := by decide +kernel", "",
            "theorem remainingWordsNodup :",
            "    (remainingPackets.map (fun P => (P.p, P.q, P.r))).Nodup := by",
            "  decide +kernel", "",
            "/-- Every missing triple has an explicit checked arithmetic packet. -/",
            "theorem remainingComplete (p q r : Nat)",
            "    (hp : p ∈ ([3,4,5] : List Nat)) (hq : q ∈ ([3,4,5] : List Nat))",
            "    (hr : r ∈ ([3,4,5] : List Nat)) (hnew : (p,q,r) ≠ (3,3,3)) :",
            "    ∃ P ∈ remainingPackets, P.p = p ∧ P.q = q ∧ P.r = r ∧",
            "      RootCertificate gridScale (p*q*r) P.parameter ∧ GeometryCertificate gridScale P := by",
            "  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hp hq hr",
            "  rcases hp with rfl | rfl | rfl <;>",
            "    rcases hq with rfl | rfl | rfl <;>",
            "    rcases hr with rfl | rfl | rfl",
            "  · exact False.elim (hnew rfl)"]
    for name in names[1:]:
        suffix = name.removeprefix("packet")
        out += [f"  · exact ⟨{name}, by simp [remainingPackets], rfl, rfl, rfl, root{suffix}, geometry{suffix}⟩"]
    out += ["", "end LoopsFormal.DepthThreeGrid", ""]
    (ROOT / "DepthThreeGrid.lean").write_text("\n".join(out), encoding="utf-8")
    print("Emitted 27 Lean packets; 26 new words, 54 kernel arithmetic theorems.")


if __name__ == "__main__":
    main()
