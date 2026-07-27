#!/usr/bin/env python3
"""Compile the exact nested-separator contact state for a finite word.

Input JSON:
{
  "atoms": ["e0", ...],
  "symbols": {
    "L": {"shared": ["e0"], "tau": {"e0": "e2"}},
    "R": {...}
  },
  "word": ["L", "R", ...],
  "initial_mask": ["e0", ...]   # optional; defaults to all atoms
}

Output records the four-way classes G,T,O,Z, exact mask recursion, and
strongly connected components of the zero-energy contact graph.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from typing import Dict, List, Set, Tuple


def validate(data: dict) -> None:
    atoms = set(data["atoms"])
    if len(atoms) != len(data["atoms"]):
        raise ValueError("atoms must be unique")
    for name, spec in data["symbols"].items():
        shared = set(spec["shared"])
        tau = spec["tau"]
        if shared != set(tau):
            raise ValueError(f"{name}: tau domain must equal shared set")
        if not shared <= atoms or not set(tau.values()) <= atoms:
            raise ValueError(f"{name}: unknown atom in shared/tau")
        if len(set(tau.values())) != len(tau):
            raise ValueError(f"{name}: tau must be injective on open atoms")
    for a in data["word"]:
        if a not in data["symbols"]:
            raise ValueError(f"unknown symbol {a}")


def tarjan(vertices: List[str], edges: Dict[str, Set[str]]) -> List[List[str]]:
    index = 0
    stack: List[str] = []
    on_stack: Set[str] = set()
    indices: Dict[str, int] = {}
    low: Dict[str, int] = {}
    out: List[List[str]] = []

    def visit(v: str) -> None:
        nonlocal index
        indices[v] = low[v] = index
        index += 1
        stack.append(v)
        on_stack.add(v)
        for w in edges.get(v, set()):
            if w not in indices:
                visit(w)
                low[v] = min(low[v], low[w])
            elif w in on_stack:
                low[v] = min(low[v], indices[w])
        if low[v] == indices[v]:
            comp = []
            while True:
                w = stack.pop()
                on_stack.remove(w)
                comp.append(w)
                if w == v:
                    break
            out.append(sorted(comp))

    for v in vertices:
        if v not in indices:
            visit(v)
    return sorted(out, key=lambda c: (len(c), c))


def compile_contact(data: dict) -> dict:
    validate(data)
    atoms = set(data["atoms"])
    R = set(data.get("initial_mask", data["atoms"]))
    if not R <= atoms:
        raise ValueError("initial_mask contains unknown atoms")

    stages = []
    masks = [sorted(R)]
    for j, a in enumerate(data["word"]):
        spec = data["symbols"][a]
        A = set(spec["shared"])
        tau = spec["tau"]
        G = (atoms - R) & (atoms - A)
        T = (atoms - R) & A
        O = R & (atoms - A)
        Z = R & A
        R_next = {tau[x] for x in Z}
        stages.append({
            "stage": j,
            "symbol": a,
            "mask_before": sorted(R),
            "G_genuine_glue": sorted(G),
            "T_zero_energy_transport": sorted(T),
            "O_root_side_only": sorted(O),
            "Z_double_inactive": sorted(Z),
            "mask_after": sorted(R_next),
        })
        R = R_next
        masks.append(sorted(R))

    edges: Dict[str, Set[str]] = {a: set() for a in atoms}
    edge_labels: List[dict] = []
    for symbol, spec in data["symbols"].items():
        for u, v in spec["tau"].items():
            edges[u].add(v)
            edge_labels.append({"from": u, "symbol": symbol, "to": v})
    sccs = tarjan(sorted(atoms), edges)
    recurrent = []
    for comp in sccs:
        cset = set(comp)
        has_cycle = len(comp) > 1 or any(v in edges[v] for v in comp)
        if has_cycle:
            recurrent.append(comp)

    return {
        "atoms": data["atoms"],
        "word": data["word"],
        "state_bound": 2 ** len(atoms),
        "masks": masks,
        "stages": stages,
        "contact_graph_edges": sorted(edge_labels, key=lambda x: (x["from"], x["symbol"], x["to"])),
        "strongly_connected_components": sccs,
        "recurrent_neutral_components": recurrent,
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("input", type=Path)
    ap.add_argument("-o", "--output", type=Path)
    args = ap.parse_args()
    data = json.loads(args.input.read_text(encoding="utf-8"))
    result = compile_contact(data)
    text = json.dumps(result, indent=2)
    if args.output:
        args.output.write_text(text + "\n", encoding="utf-8")
    print(text)


if __name__ == "__main__":
    main()
