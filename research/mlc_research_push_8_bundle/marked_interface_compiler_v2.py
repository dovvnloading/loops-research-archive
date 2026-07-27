#!/usr/bin/env python3
"""Exact finite compiler for a branch-adapted pulled/immersed ideal interface.

The model is one linearly cut ideal-boundary component.  The cut (seam) is a
retained phase endpoint, so no ideal interval may cross it.  Target micro-atoms
are numbered 0,...,n-1 and target vertices 0,...,n.

Each source open atom carries:
  * imm_micro: target micro-atom reached properly by the immersion, or None when
    the source boundary atom is nonproper (its image enters the target interior);
  * cov_micro: target micro-atom reached by the covering boundary map.

The compiler performs three logically distinct tasks.

1. It computes the finest immersion-admissible target partition.  Every maximal
   nonproper source run bridges its adjacent proper labels; those target labels,
   and every target micro-atom between them in the fixed phase order, must lie in
   one ideal interval.
2. It enumerates coarsenings of that partition, preserving mandatory ideal
   endpoints, and retains exactly those for which every boundary of every
   immersion pullback component is a covering preimage of a target endpoint.
   This is equivalent to f^*I refining iota^*I in the finite atom model.
3. It keeps an independent trace overlay.  Trace endpoints that are not action
   endpoints are retained as response/access subdivisions but are explicitly not
   licensed as KKL ideal-marking endpoints.

The script is a finite combinatorial proof/audit tool.  Analytic trace and
welding theorems are stated separately in the Research Push VIII memo.
"""
from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations
from typing import Dict, Iterable, List, Optional, Sequence, Set, Tuple
import argparse
import json


class MarkingFailure(RuntimeError):
    """Exact obstruction to a branch-adapted ideal marking."""


@dataclass(frozen=True)
class SourceAtom:
    imm_micro: Optional[int]
    cov_micro: int
    name: str = ""


@dataclass
class BranchModel:
    target_micro_count: int
    source_atoms: List[SourceAtom]
    source_vertex_cov_image: List[int]
    seam_vertex: int = 0

    def validate(self) -> None:
        n = self.target_micro_count
        m = len(self.source_atoms)
        if n < 1 or m < 1:
            raise ValueError("empty boundary model")
        if self.seam_vertex not in (0, n):
            # The linearized implementation identifies the phase seam with 0=n.
            raise ValueError("seam_vertex must be the retained 0=n phase seam")
        if len(self.source_vertex_cov_image) != m + 1:
            raise ValueError("linearized source needs m+1 covering vertex images")
        for atom in self.source_atoms:
            if atom.imm_micro is not None and not 0 <= atom.imm_micro < n:
                raise ValueError("bad immersion target micro-atom")
            if not 0 <= atom.cov_micro < n:
                raise ValueError("bad covering target micro-atom")
        for v in self.source_vertex_cov_image:
            if not 0 <= v <= n:
                raise ValueError("bad covering endpoint image")


def normalize_vertices(n: int, vertices: Iterable[int]) -> List[int]:
    out = {0, n}
    out.update(int(v) for v in vertices)
    if not all(0 <= v <= n for v in out):
        raise ValueError("target vertex outside [0,n]")
    return sorted(out)


def blocks_from_endpoints(n: int, endpoints: Sequence[int]) -> List[Tuple[int, int]]:
    e = normalize_vertices(n, endpoints)
    return [(e[i], e[i + 1]) for i in range(len(e) - 1) if e[i] < e[i + 1]]


def micro_to_block(n: int, endpoints: Sequence[int]) -> List[int]:
    blocks = blocks_from_endpoints(n, endpoints)
    out = [-1] * n
    for bid, (lo, hi) in enumerate(blocks):
        for k in range(lo, hi):
            out[k] = bid
    if any(v < 0 for v in out):
        raise AssertionError("target partition did not cover every micro-atom")
    return out


class UnionFind:
    def __init__(self, n: int):
        self.p = list(range(n))

    def find(self, x: int) -> int:
        while self.p[x] != x:
            self.p[x] = self.p[self.p[x]]
            x = self.p[x]
        return x

    def union(self, a: int, b: int) -> None:
        a, b = self.find(a), self.find(b)
        if a != b:
            self.p[b] = a


def maximal_none_runs(labels: Sequence[Optional[int]]) -> List[Tuple[int, int, Optional[int], Optional[int]]]:
    """Return linear nonproper runs [lo,hi) and adjacent proper labels."""
    m = len(labels)
    runs: List[Tuple[int, int, Optional[int], Optional[int]]] = []
    i = 0
    while i < m:
        if labels[i] is not None:
            i += 1
            continue
        lo = i
        while i < m and labels[i] is None:
            i += 1
        hi = i
        left = labels[lo - 1] if lo > 0 else None
        right = labels[hi] if hi < m else None
        runs.append((lo, hi, left, right))
    return runs


def immersion_base_partition(model: BranchModel) -> Tuple[List[int], List[dict]]:
    """Compute the unique finest partition allowed by immersion bridges.

    A nonproper run adjacent to proper target micro-atoms p and q belongs to both
    pullback hulls unless p and q lie in the same target interval.  With the
    retained phase seam, an interval containing p and q must contain every target
    micro-atom between them.  The transitive interval-convex closure gives the
    finest immersion-admissible partition.
    """
    n = model.target_micro_count
    labels = [a.imm_micro for a in model.source_atoms]
    uf = UnionFind(n)
    witnesses: List[dict] = []
    for lo, hi, left, right in maximal_none_runs(labels):
        if left is None or right is None or left == right:
            continue
        a, b = sorted((left, right))
        for k in range(a, b):
            uf.union(k, k + 1)
        witnesses.append(
            {
                "source_nonproper_run": [lo, hi],
                "adjacent_target_micro_atoms": [left, right],
                "forced_target_hull": [a, b + 1],
            }
        )

    # Interval-convex components.  Union operations above already include all
    # intermediate micro-atoms, so component changes are exactly valid cuts.
    endpoints = [0]
    for k in range(1, n):
        if uf.find(k - 1) != uf.find(k):
            endpoints.append(k)
    endpoints.append(n)
    return endpoints, witnesses


def immersion_hull_components(
    model: BranchModel, endpoints: Sequence[int]
) -> Tuple[Dict[int, List[List[int]]], List[List[int]]]:
    """Compute source pullback components for every target interval.

    The finite boundary-monotone pullback formula removes proper atoms labelled
    by other target blocks.  Every remaining connected run containing a seed of
    block b is one component of iota^*I_b.  Components containing no proper seed
    form the induced-marking remainder.
    """
    n = model.target_micro_count
    m = len(model.source_atoms)
    mb = micro_to_block(n, endpoints)
    block_count = len(blocks_from_endpoints(n, endpoints))
    labels: List[Optional[int]] = [
        None if a.imm_micro is None else mb[a.imm_micro]
        for a in model.source_atoms
    ]
    components: Dict[int, List[List[int]]] = {b: [] for b in range(block_count)}

    for b in range(block_count):
        allowed = [lab is None or lab == b for lab in labels]
        i = 0
        while i < m:
            if not allowed[i]:
                i += 1
                continue
            j = i
            has_seed = False
            while j < m and allowed[j]:
                has_seed = has_seed or labels[j] == b
                j += 1
            if has_seed:
                components[b].append(list(range(i, j)))
            i = j

    covered = {s for cs in components.values() for comp in cs for s in comp}
    remainder: List[List[int]] = []
    i = 0
    while i < m:
        if i in covered:
            i += 1
            continue
        j = i
        while j < m and j not in covered:
            j += 1
        remainder.append(list(range(i, j)))
        i = j
    return components, remainder


def component_boundaries(component: Sequence[int], source_atom_count: int) -> Tuple[int, int]:
    if not component:
        raise ValueError("empty source component")
    return min(component), max(component) + 1


def action_condition(
    model: BranchModel, endpoints: Sequence[int]
) -> Tuple[bool, dict]:
    components, remainder = immersion_hull_components(model, endpoints)
    endpoint_set = set(normalize_vertices(model.target_micro_count, endpoints))
    failures: List[dict] = []
    component_records: Dict[str, list] = {}

    for b, comps in components.items():
        recs = []
        for comp in comps:
            left_sv, right_sv = component_boundaries(comp, len(model.source_atoms))
            left_tv = model.source_vertex_cov_image[left_sv]
            right_tv = model.source_vertex_cov_image[right_sv]
            proper_positions = [
                s for s in comp if model.source_atoms[s].imm_micro is not None
            ]
            all_proper = len(proper_positions) == len(comp)
            end_proper = bool(proper_positions) and (
                model.source_atoms[comp[0]].imm_micro is not None
                and model.source_atoms[comp[-1]].imm_micro is not None
            )
            rec = {
                "source_atoms": comp,
                "source_boundary_vertices": [left_sv, right_sv],
                "covering_boundary_images": [left_tv, right_tv],
                "proper": all_proper,
                "end_proper": end_proper,
            }
            recs.append(rec)
            for sv, tv in ((left_sv, left_tv), (right_sv, right_tv)):
                if tv not in endpoint_set:
                    failures.append(
                        {
                            "target_block": b,
                            "source_boundary_vertex": sv,
                            "covering_image_not_endpoint": tv,
                        }
                    )
        component_records[str(b)] = recs

    return (not failures), {
        "immersion_components": component_records,
        "induced_remainder_components": remainder,
        "covering_refinement_failures": failures,
    }


def coarsenings_of_base(base_endpoints: Sequence[int], mandatory: Set[int]) -> Iterable[List[int]]:
    base = normalize_vertices(base_endpoints[-1], base_endpoints)
    internal = base[1:-1]
    optional = [e for e in internal if e not in mandatory]
    fixed = {0, base[-1]} | (mandatory & set(base))
    # Enumerate finest first; deterministic lexicographic tie-breaking later.
    for removed_count in range(0, len(optional) + 1):
        for removed in combinations(optional, removed_count):
            yield sorted((set(base) - set(removed)) | fixed)


def compile_marked_interface(payload: dict) -> dict:
    model = BranchModel(
        target_micro_count=int(payload["target_micro_count"]),
        source_atoms=[
            SourceAtom(
                imm_micro=(None if x.get("imm_micro") is None else int(x["imm_micro"])),
                cov_micro=int(x["cov_micro"]),
                name=str(x.get("name", "")),
            )
            for x in payload["source_atoms"]
        ],
        source_vertex_cov_image=[int(x) for x in payload["source_vertex_cov_image"]],
        seam_vertex=int(payload.get("seam_vertex", 0)),
    )
    model.validate()
    n = model.target_micro_count
    mandatory = set(normalize_vertices(n, payload.get("mandatory_ideal_endpoints", [])))
    trace_endpoints = set(normalize_vertices(n, payload.get("trace_overlay_endpoints", [])))

    base_endpoints, bridge_witnesses = immersion_base_partition(model)
    base_set = set(base_endpoints)
    impossible_mandatory = sorted(mandatory - base_set)
    if impossible_mandatory:
        raise MarkingFailure(
            "mandatory ideal endpoint(s) split an immersion-forced block: "
            + repr(impossible_mandatory)
        )

    valid: List[Tuple[List[int], dict]] = []
    for endpoints in coarsenings_of_base(base_endpoints, mandatory):
        ok, details = action_condition(model, endpoints)
        if ok:
            valid.append((endpoints, details))

    if not valid:
        raise MarkingFailure(
            "no coarsening of the immersion-admissible partition makes "
            "the covering-pulled marking refine the immersion-pulled marking"
        )

    # The enumeration is finest first.  Among equally fine candidates, choose the
    # lexicographically greatest endpoint list in the fixed external-angle order.
    max_count = max(len(e) for e, _ in valid)
    finalists = [(e, d) for e, d in valid if len(e) == max_count]
    endpoints, details = sorted(finalists, key=lambda item: item[0])[-1]
    action_set = set(endpoints)

    response_only = sorted(trace_endpoints - action_set)
    promotable_trace = sorted(trace_endpoints & action_set)
    blocks = blocks_from_endpoints(n, endpoints)

    # Covering pullback incidence: each source atom belongs to the target block
    # containing its covering image.
    mb = micro_to_block(n, endpoints)
    covering_incidence = [mb[a.cov_micro] for a in model.source_atoms]
    immersion_incidence: List[List[int]] = [[] for _ in model.source_atoms]
    for b, recs in details["immersion_components"].items():
        bid = int(b)
        for rec in recs:
            for s in rec["source_atoms"]:
                immersion_incidence[s].append(bid)

    return {
        "status": "compiled",
        "base_immersion_endpoints": base_endpoints,
        "immersion_bridge_witnesses": bridge_witnesses,
        "selected_action_endpoints": endpoints,
        "selected_action_blocks": [list(x) for x in blocks],
        "mandatory_ideal_endpoints": sorted(mandatory),
        "trace_overlay_endpoints": sorted(trace_endpoints),
        "promotable_trace_endpoints": promotable_trace,
        "response_only_trace_endpoints": response_only,
        "valid_action_marking_count": len(valid),
        "maximal_valid_action_marking_count": len(finalists),
        "selected_action_details": details,
        "covering_block_by_source_atom": covering_incidence,
        "immersion_blocks_by_source_atom": immersion_incidence,
    }


def independent_partition_valid(model: BranchModel, endpoints: Sequence[int]) -> bool:
    """Direct definition-level validity check, independent of the compiler closure."""
    n = model.target_micro_count
    m = len(model.source_atoms)
    mb = micro_to_block(n, endpoints)
    block_count = len(blocks_from_endpoints(n, endpoints))
    labels: List[Optional[int]] = [
        None if a.imm_micro is None else mb[a.imm_micro]
        for a in model.source_atoms
    ]
    hull_sets: Dict[int, Set[int]] = {b: set() for b in range(block_count)}
    hull_components: Dict[int, List[List[int]]] = {b: [] for b in range(block_count)}
    for b in range(block_count):
        allowed = [lab is None or lab == b for lab in labels]
        i = 0
        while i < m:
            if not allowed[i]:
                i += 1
                continue
            j = i
            seed = False
            while j < m and allowed[j]:
                seed = seed or labels[j] == b
                j += 1
            if seed:
                comp = list(range(i, j))
                hull_components[b].append(comp)
                hull_sets[b].update(comp)
            i = j
    # Pullbacks of distinct target intervals must be disjoint.
    for a in range(block_count):
        for b in range(a + 1, block_count):
            if hull_sets[a] & hull_sets[b]:
                return False
    endpoint_set = set(normalize_vertices(n, endpoints))
    # Every endpoint of every immersion pullback component must be a covering
    # preimage of a target endpoint.  This is exactly f^*I refining iota^*I in
    # the finite atom model.
    for comps in hull_components.values():
        for comp in comps:
            left, right = min(comp), max(comp) + 1
            if model.source_vertex_cov_image[left] not in endpoint_set:
                return False
            if model.source_vertex_cov_image[right] not in endpoint_set:
                return False
    return True


def brute_force_valid_markings(payload: dict) -> List[List[int]]:
    """Independent exhaustive oracle over every target endpoint subset."""
    model = BranchModel(
        target_micro_count=int(payload["target_micro_count"]),
        source_atoms=[
            SourceAtom(
                imm_micro=(None if x.get("imm_micro") is None else int(x["imm_micro"])),
                cov_micro=int(x["cov_micro"]),
            )
            for x in payload["source_atoms"]
        ],
        source_vertex_cov_image=[int(x) for x in payload["source_vertex_cov_image"]],
        seam_vertex=int(payload.get("seam_vertex", 0)),
    )
    model.validate()
    n = model.target_micro_count
    mandatory = set(normalize_vertices(n, payload.get("mandatory_ideal_endpoints", [])))
    out: List[List[int]] = []
    interior = list(range(1, n))
    for mask in range(1 << len(interior)):
        e = {0, n} | {
            interior[k] for k in range(len(interior)) if mask & (1 << k)
        }
        if not mandatory <= e:
            continue
        if independent_partition_valid(model, sorted(e)):
            out.append(sorted(e))
    return sorted(out)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("input_json")
    ap.add_argument("output_json")
    ap.add_argument("--bruteforce", action="store_true")
    args = ap.parse_args()
    with open(args.input_json, "r", encoding="utf-8") as f:
        payload = json.load(f)
    try:
        result = compile_marked_interface(payload)
        if args.bruteforce:
            result["bruteforce_valid_markings"] = brute_force_valid_markings(payload)
    except MarkingFailure as exc:
        result = {"status": "obstruction", "reason": str(exc)}
        if args.bruteforce:
            result["bruteforce_valid_markings"] = brute_force_valid_markings(payload)
    with open(args.output_json, "w", encoding="utf-8") as f:
        json.dump(result, f, indent=2, sort_keys=True)


if __name__ == "__main__":
    main()
