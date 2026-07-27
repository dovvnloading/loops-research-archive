#!/usr/bin/env python3
"""Exact finite compiler for the binary direct-decoration contact/trace atlas.

This is an algebraic audit tool.  It does not infer the Kahn--Lyubich ray angles;
those must be supplied by an exact source boundary word.  Once supplied, it:

* matches parent/child boundary edges exactly;
* compiles the two one-step contact subgraphs;
* iterates the normalized contact recursion;
* enumerates endpoint-flag itineraries;
* builds the one-to-many trace atom relation;
* checks word functoriality;
* checks normalized-overlay and refinement naturality.

All discrete calculations are exact.  Rational angle/potential coordinates use
fractions.Fraction; no floating-point geometry is used.
"""

from __future__ import annotations

import argparse
import json
from collections import defaultdict
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from pathlib import Path
from typing import Any, Iterable, Mapping, Sequence


class CompilerError(ValueError):
    """Raised when a source record violates an exact atlas requirement."""


def frac(value: Any) -> Fraction:
    if isinstance(value, Fraction):
        return value
    if isinstance(value, int):
        return Fraction(value, 1)
    if isinstance(value, str):
        return Fraction(value)
    if isinstance(value, float):
        return Fraction(str(value))
    raise TypeError(f"Cannot parse rational value {value!r}")


@dataclass(frozen=True)
class RayEdge:
    edge_id: str
    angle: Fraction
    inner_potential: Fraction
    outer_potential: Fraction
    start_flag: str
    end_flag: str

    def interval(self) -> tuple[Fraction, Fraction]:
        lo = min(self.inner_potential, self.outer_potential)
        hi = max(self.inner_potential, self.outer_potential)
        return lo, hi


@dataclass(frozen=True)
class EquipotentialEdge:
    edge_id: str
    level: int
    potential: Fraction
    theta_start: Fraction
    theta_end: Fraction
    start_flag: str
    end_flag: str


BoundaryEdge = RayEdge | EquipotentialEdge


def parse_edge(record: Mapping[str, Any]) -> BoundaryEdge:
    edge_type = record.get("type")
    if edge_type == "ray":
        return RayEdge(
            edge_id=str(record["id"]),
            angle=frac(record["angle"]) % 1,
            inner_potential=frac(record.get("inner_potential", 0)),
            outer_potential=frac(record["outer_potential"]),
            start_flag=str(record["start_flag"]),
            end_flag=str(record["end_flag"]),
        )
    if edge_type == "equipotential":
        level = int(record["level"])
        return EquipotentialEdge(
            edge_id=str(record["id"]),
            level=level,
            potential=frac(record.get("potential", Fraction(1, 2 ** level))),
            theta_start=frac(record["theta_start"]) % 1,
            theta_end=frac(record["theta_end"]) % 1,
            start_flag=str(record["start_flag"]),
            end_flag=str(record["end_flag"]),
        )
    raise CompilerError(f"Unknown boundary edge type: {edge_type!r}")


def _cyclic_interval_parts(a: Fraction, b: Fraction) -> list[tuple[Fraction, Fraction]]:
    a %= 1
    b %= 1
    if a == b:
        return [(Fraction(0), Fraction(1))]
    if a < b:
        return [(a, b)]
    return [(a, Fraction(1)), (Fraction(0), b)]


def _interval_overlap(
    first: tuple[Fraction, Fraction], second: tuple[Fraction, Fraction]
) -> tuple[Fraction, Fraction] | None:
    lo = max(first[0], second[0])
    hi = min(first[1], second[1])
    if lo < hi:
        return lo, hi
    return None


def _angle_in_cyclic_closed(angle: Fraction, a: Fraction, b: Fraction) -> bool:
    angle %= 1
    a %= 1
    b %= 1
    if a == b:
        return True
    if a < b:
        return a <= angle <= b
    return angle >= a or angle <= b


def _edge_endpoints(edge: BoundaryEdge) -> list[tuple[Fraction, Fraction, str]]:
    if isinstance(edge, RayEdge):
        return [
            (edge.angle, edge.inner_potential, edge.start_flag),
            (edge.angle, edge.outer_potential, edge.end_flag),
        ]
    return [
        (edge.theta_start, edge.potential, edge.start_flag),
        (edge.theta_end, edge.potential, edge.end_flag),
    ]


def _coord_key(angle: Fraction, potential: Fraction) -> str:
    return f"theta={angle % 1};potential={potential}"


def match_boundary_graph(
    parent_edges: Sequence[BoundaryEdge], child_edges: Sequence[BoundaryEdge]
) -> dict[str, Any]:
    """Compile open overlaps and all exact point contacts.

    Point contacts include ray/equipotential corners and touching endpoints.
    The output also records which edges require subdivision when the contact
    point lies in the relative interior of an edge.
    """

    open_contacts = match_boundary_contacts(parent_edges, child_edges)
    point_records: dict[tuple[str, str, str], dict[str, Any]] = {}

    def add_point(
        parent: BoundaryEdge, child: BoundaryEdge, angle: Fraction, potential: Fraction
    ) -> None:
        parent_flags = [
            flag
            for a, p, flag in _edge_endpoints(parent)
            if a % 1 == angle % 1 and p == potential
        ]
        child_flags = [
            flag
            for a, p, flag in _edge_endpoints(child)
            if a % 1 == angle % 1 and p == potential
        ]
        key = (parent.edge_id, child.edge_id, _coord_key(angle, potential))
        point_records[key] = {
            "parent_edge": parent.edge_id,
            "child_edge": child.edge_id,
            "angle": str(angle % 1),
            "potential": str(potential),
            "parent_endpoint_flags": sorted(parent_flags),
            "child_endpoint_flags": sorted(child_flags),
            "subdivide_parent": not bool(parent_flags),
            "subdivide_child": not bool(child_flags),
        }

    for parent in parent_edges:
        for child in child_edges:
            if isinstance(parent, RayEdge) and isinstance(child, RayEdge):
                if parent.angle != child.angle:
                    continue
                lo = max(parent.interval()[0], child.interval()[0])
                hi = min(parent.interval()[1], child.interval()[1])
                if lo == hi:
                    add_point(parent, child, parent.angle, lo)
            elif isinstance(parent, EquipotentialEdge) and isinstance(
                child, EquipotentialEdge
            ):
                if parent.potential != child.potential:
                    continue
                parent_end = _edge_endpoints(parent)[:2]
                child_end = _edge_endpoints(child)[:2]
                for angle, potential, _flag in parent_end:
                    if _angle_in_cyclic_closed(
                        angle, child.theta_start, child.theta_end
                    ):
                        add_point(parent, child, angle, potential)
                for angle, potential, _flag in child_end:
                    if _angle_in_cyclic_closed(
                        angle, parent.theta_start, parent.theta_end
                    ):
                        add_point(parent, child, angle, potential)
            elif isinstance(parent, RayEdge) and isinstance(
                child, EquipotentialEdge
            ):
                if (
                    parent.interval()[0] <= child.potential <= parent.interval()[1]
                    and _angle_in_cyclic_closed(
                        parent.angle, child.theta_start, child.theta_end
                    )
                ):
                    add_point(parent, child, parent.angle, child.potential)
            elif isinstance(parent, EquipotentialEdge) and isinstance(
                child, RayEdge
            ):
                if (
                    child.interval()[0] <= parent.potential <= child.interval()[1]
                    and _angle_in_cyclic_closed(
                        child.angle, parent.theta_start, parent.theta_end
                    )
                ):
                    add_point(parent, child, child.angle, parent.potential)

    points = sorted(
        point_records.values(),
        key=lambda item: (
            Fraction(item["angle"]),
            Fraction(item["potential"]),
            item["parent_edge"],
            item["child_edge"],
        ),
    )
    return {
        "open_contacts": open_contacts,
        "point_contacts": points,
        "required_parent_subdivisions": [
            item for item in points if item["subdivide_parent"]
        ],
        "required_child_subdivisions": [
            item for item in points if item["subdivide_child"]
        ],
    }


def match_boundary_contacts(
    parent_edges: Sequence[BoundaryEdge], child_edges: Sequence[BoundaryEdge]
) -> list[dict[str, Any]]:
    """Return all nondegenerate open boundary overlaps.

    Ray overlaps require the same exact external angle.  Equipotential overlaps
    require the same exact level and overlapping angular intervals.  Point
    contacts are carried separately by the endpoint-flag record.
    """

    contacts: list[dict[str, Any]] = []
    for parent_edge in parent_edges:
        for child_edge in child_edges:
            if isinstance(parent_edge, RayEdge) and isinstance(child_edge, RayEdge):
                if parent_edge.angle != child_edge.angle:
                    continue
                overlap = _interval_overlap(parent_edge.interval(), child_edge.interval())
                if overlap is not None:
                    contacts.append(
                        {
                            "kind": "ray",
                            "parent_edge": parent_edge.edge_id,
                            "child_edge": child_edge.edge_id,
                            "angle": str(parent_edge.angle),
                            "potential_interval": [str(overlap[0]), str(overlap[1])],
                        }
                    )
            elif isinstance(parent_edge, EquipotentialEdge) and isinstance(
                child_edge, EquipotentialEdge
            ):
                if parent_edge.level != child_edge.level:
                    continue
                for parent_part in _cyclic_interval_parts(
                    parent_edge.theta_start, parent_edge.theta_end
                ):
                    for child_part in _cyclic_interval_parts(
                        child_edge.theta_start, child_edge.theta_end
                    ):
                        overlap = _interval_overlap(parent_part, child_part)
                        if overlap is not None:
                            contacts.append(
                                {
                                    "kind": "equipotential",
                                    "parent_edge": parent_edge.edge_id,
                                    "child_edge": child_edge.edge_id,
                                    "level": parent_edge.level,
                                    "angle_interval": [
                                        str(overlap[0]),
                                        str(overlap[1]),
                                    ],
                                }
                            )
    return contacts


@dataclass(frozen=True)
class BranchAtlas:
    name: str
    contact_atoms: frozenset[str]
    contact_image: Mapping[str, str]
    child_parent: Mapping[str, str]
    flag_image: Mapping[str, str]

    def transition(self, state: Iterable[str]) -> frozenset[str]:
        output: set[str] = set()
        for atom in set(state) & set(self.contact_atoms):
            try:
                output.add(self.contact_image[atom])
            except KeyError as exc:
                raise CompilerError(
                    f"Branch {self.name}: contact atom {atom!r} has no image"
                ) from exc
        return frozenset(output)

    def lifts_by_parent(self) -> dict[str, tuple[str, ...]]:
        grouped: dict[str, list[str]] = defaultdict(list)
        for child, parent in self.child_parent.items():
            grouped[parent].append(child)
        return {parent: tuple(sorted(children)) for parent, children in grouped.items()}


@dataclass
class AtlasRecord:
    root_atoms: tuple[str, ...]
    root_flags: tuple[str, ...]
    branches: dict[str, BranchAtlas]
    transient_depth: int
    vertex_by_word: dict[str, str]
    synchronization: dict[str, Any] | None
    refinement: dict[str, Any] | None
    parent_edges: tuple[BoundaryEdge, ...]
    child_edges: dict[str, tuple[BoundaryEdge, ...]]

    @classmethod
    def from_json(cls, data: Mapping[str, Any]) -> "AtlasRecord":
        root_atoms = tuple(str(item) for item in data["root_atoms"])
        root_flags = tuple(str(item) for item in data.get("root_flags", []))
        branches: dict[str, BranchAtlas] = {}
        for name, branch_data in data["branches"].items():
            branches[name] = BranchAtlas(
                name=name,
                contact_atoms=frozenset(str(x) for x in branch_data["contact_atoms"]),
                contact_image={
                    str(key): str(value)
                    for key, value in branch_data["contact_image"].items()
                },
                child_parent={
                    str(key): str(value)
                    for key, value in branch_data["child_parent"].items()
                },
                flag_image={
                    str(key): str(value)
                    for key, value in branch_data.get("flag_image", {}).items()
                },
            )
        boundary_words = data.get("boundary_words", {})
        parent_edges = tuple(
            parse_edge(record) for record in boundary_words.get("parent", [])
        )
        child_edges = {
            name: tuple(parse_edge(record) for record in records)
            for name, records in boundary_words.get("children", {}).items()
        }
        return cls(
            root_atoms=root_atoms,
            root_flags=root_flags,
            branches=branches,
            transient_depth=int(data.get("transient_depth", 0)),
            vertex_by_word={
                str(key): str(value)
                for key, value in data.get("vertex_by_word", {}).items()
            },
            synchronization=data.get("synchronization"),
            refinement=data.get("refinement"),
            parent_edges=parent_edges,
            child_edges=child_edges,
        )


class BinaryContactCompiler:
    def __init__(self, record: AtlasRecord) -> None:
        self.record = record
        self.alphabet = tuple(sorted(record.branches))
        if set(self.alphabet) != {"L", "R"}:
            raise CompilerError(
                f"Expected exact binary alphabet {{L,R}}, got {self.alphabet!r}"
            )
        self._validate_base_record()

    def _validate_base_record(self) -> None:
        root_atom_set = set(self.record.root_atoms)
        root_flag_set = set(self.record.root_flags)
        for branch in self.record.branches.values():
            unknown_contacts = set(branch.contact_atoms) - root_atom_set
            if unknown_contacts:
                raise CompilerError(
                    f"Branch {branch.name}: unknown contact atoms {unknown_contacts}"
                )
            unknown_images = set(branch.contact_image.values()) - root_atom_set
            if unknown_images:
                raise CompilerError(
                    f"Branch {branch.name}: unknown contact images {unknown_images}"
                )
            unknown_parents = set(branch.child_parent.values()) - root_atom_set
            if unknown_parents:
                raise CompilerError(
                    f"Branch {branch.name}: unknown parent atoms {unknown_parents}"
                )
            if root_flag_set:
                unknown_flag_images = set(branch.flag_image.values()) - root_flag_set
                if unknown_flag_images:
                    raise CompilerError(
                        f"Branch {branch.name}: unknown flag images {unknown_flag_images}"
                    )

    def state_for_word(self, word: str) -> frozenset[str]:
        state = frozenset(self.record.root_atoms)
        for letter in word:
            try:
                branch = self.record.branches[letter]
            except KeyError as exc:
                raise CompilerError(f"Unknown branch symbol {letter!r}") from exc
            state = branch.transition(state)
        return state

    def states_through_depth(self, depth: int) -> dict[str, list[str]]:
        result: dict[str, list[str]] = {}
        for length in range(depth + 1):
            for word_tuple in product(self.alphabet, repeat=length):
                word = "".join(word_tuple)
                result[word or "epsilon"] = sorted(self.state_for_word(word))
        return result

    def flag_states_through_depth(self, depth: int) -> dict[str, list[str]]:
        result: dict[str, list[str]] = {}
        for length in range(depth + 1):
            for word_tuple in product(self.alphabet, repeat=length):
                word = "".join(word_tuple)
                state = frozenset(self.record.root_flags)
                for letter in word:
                    branch = self.record.branches[letter]
                    state = frozenset(
                        branch.flag_image[flag]
                        for flag in state
                        if flag in branch.flag_image
                    )
                result[word or "epsilon"] = sorted(state)
        return result

    def nested_contact_state(self, outer: str, inner: str) -> frozenset[str]:
        if inner.startswith(outer):
            return self.state_for_word(inner[len(outer) :])
        if outer.startswith(inner):
            return self.state_for_word(outer[len(inner) :])
        return frozenset()

    def endpoint_itinerary(self, initial_flag: str, word: str) -> list[str]:
        itinerary = [initial_flag]
        current = initial_flag
        for letter in word:
            branch = self.record.branches[letter]
            if current not in branch.flag_image:
                raise CompilerError(
                    f"Flag {current!r} has no {letter}-transition at prefix "
                    f"{word[:len(itinerary)-1]!r}"
                )
            current = branch.flag_image[current]
            itinerary.append(current)
        return itinerary

    def source_vertex_shift_checks(self) -> dict[str, Any]:
        n = self.record.transient_depth
        if n <= 0:
            return {"depth": 0, "word_chains": [], "prefix_families": []}
        expected_words = {"".join(word) for word in product(self.alphabet, repeat=n)}
        missing = expected_words - set(self.record.vertex_by_word)
        if missing:
            raise CompilerError(
                f"Missing depth-{n} source vertices for words {sorted(missing)}"
            )
        values = [self.record.vertex_by_word[word] for word in expected_words]
        if len(values) != len(set(values)):
            raise CompilerError("Depth-n word-to-vertex map is not injective")

        word_chains: list[dict[str, Any]] = []
        for word in sorted(expected_words):
            chain: list[dict[str, str | None]] = []
            for index in range(n + 1):
                suffix = word[index:]
                key = suffix if suffix else "epsilon"
                chain.append(
                    {
                        "word": key,
                        "vertex": self.record.vertex_by_word.get(key),
                    }
                )
            word_chains.append(
                {
                    "word": word,
                    "vertex": self.record.vertex_by_word[word],
                    "forward_suffix_chain": chain,
                }
            )

        prefix_families: list[dict[str, Any]] = []
        for length in range(n + 1):
            for prefix_tuple in product(self.alphabet, repeat=length):
                prefix = "".join(prefix_tuple)
                completions = sorted(
                    word for word in expected_words if word.startswith(prefix)
                )
                normalized = []
                for word in completions:
                    suffix = word[length:]
                    key = suffix if suffix else "epsilon"
                    normalized.append(
                        {
                            "physical_word": word,
                            "physical_vertex": self.record.vertex_by_word[word],
                            "normalized_suffix": key,
                            "normalized_vertex": self.record.vertex_by_word.get(key),
                        }
                    )
                prefix_families.append(
                    {
                        "prefix": prefix if prefix else "epsilon",
                        "landing_vertices": [
                            self.record.vertex_by_word[word] for word in completions
                        ],
                        "normalized": normalized,
                    }
                )
        return {
            "depth": n,
            "word_chains": word_chains,
            "prefix_families": prefix_families,
        }

    def one_to_many_atlas(self) -> dict[str, list[dict[str, str]]]:
        result: dict[str, list[dict[str, str]]] = {
            atom: [] for atom in self.record.root_atoms
        }
        for branch_name, branch in sorted(self.record.branches.items()):
            for child, parent in sorted(branch.child_parent.items()):
                result[parent].append({"branch": branch_name, "child_atom": child})
        return result

    def lifts_for_word(self, parent_atom: str, word: str) -> list[tuple[str, ...]]:
        """Enumerate exact branch-specific child-atom paths over one root atom.

        The atlas is written in co-moving root coordinates.  After each branch
        lift, the child atom maps back to the same declared root parent atom;
        the next symbol therefore lifts that same normalized parent.  The
        returned tuple retains every physical child-atom choice.
        """

        paths: list[tuple[str, ...]] = [tuple()]
        current_parent = parent_atom
        for letter in word:
            branch = self.record.branches[letter]
            choices = tuple(
                sorted(
                    child
                    for child, parent in branch.child_parent.items()
                    if parent == current_parent
                )
            )
            if not choices:
                return []
            paths = [path + (choice,) for path in paths for choice in choices]
        return paths

    def check_word_functoriality(self, max_depth: int) -> dict[str, Any]:
        """Check one-to-many relation composition in co-moving coordinates."""

        atlas = self.one_to_many_atlas()
        failures: list[dict[str, Any]] = []
        path_counts: dict[str, int] = {}
        for atom in self.record.root_atoms:
            for depth in range(1, max_depth + 1):
                for word_tuple in product(self.alphabet, repeat=depth):
                    word = "".join(word_tuple)
                    paths = self.lifts_for_word(atom, word)
                    path_counts[f"{atom}:{word}"] = len(paths)
                    expected = 1
                    for letter in word:
                        multiplicity = sum(
                            1
                            for child, parent in self.record.branches[
                                letter
                            ].child_parent.items()
                            if parent == atom
                        )
                        expected *= multiplicity
                    if len(paths) != expected:
                        failures.append(
                            {
                                "atom": atom,
                                "word": word,
                                "actual_path_count": len(paths),
                                "expected_path_count": expected,
                            }
                        )
                    if word and not any(
                        item["branch"] == word[0] for item in atlas[atom]
                    ) and paths:
                        failures.append(
                            {
                                "atom": atom,
                                "word": word,
                                "reason": "first branch absent from one-step atlas",
                            }
                        )
        return {"path_counts": path_counts, "failures": failures}

    def check_synchronization(self) -> dict[str, Any]:
        sync = self.record.synchronization
        if not sync:
            return {"present": False, "failures": []}
        depth = int(sync["depth"])
        persistent = frozenset(str(x) for x in sync["persistent_state"])
        persistent_branch = str(sync["persistent_branch"])
        kill_branches = tuple(str(x) for x in sync.get("kill_branches", []))
        failures: list[dict[str, Any]] = []
        depth_states: dict[str, list[str]] = {}
        for word_tuple in product(self.alphabet, repeat=depth):
            word = "".join(word_tuple)
            state = self.state_for_word(word)
            depth_states[word] = sorted(state)
            if state != persistent:
                failures.append(
                    {
                        "word": word,
                        "state": sorted(state),
                        "expected_persistent_state": sorted(persistent),
                    }
                )
        persisted = self.record.branches[persistent_branch].transition(persistent)
        if persisted != persistent:
            failures.append(
                {
                    "persistent_branch": persistent_branch,
                    "image": sorted(persisted),
                    "expected": sorted(persistent),
                }
            )
        killed: dict[str, list[str]] = {}
        for branch_name in kill_branches:
            image = self.record.branches[branch_name].transition(persistent)
            killed[branch_name] = sorted(image)
            if image:
                failures.append(
                    {
                        "kill_branch": branch_name,
                        "image": sorted(image),
                        "expected": [],
                    }
                )
        return {
            "present": True,
            "depth": depth,
            "persistent_state": sorted(persistent),
            "depth_states": depth_states,
            "persistent_branch": persistent_branch,
            "kill_branch_images": killed,
            "failures": failures,
        }

    def check_refinement_naturality(self) -> dict[str, Any]:
        refinement = self.record.refinement
        if not refinement:
            return {"present": False, "failures": []}
        coarse_root = {
            str(key): str(value)
            for key, value in refinement["coarse_of_refined_root"].items()
        }
        failures: list[dict[str, Any]] = []
        for branch_name, branch_ref in refinement["branches"].items():
            coarse_child = {
                str(key): str(value)
                for key, value in branch_ref["coarse_of_refined_child"].items()
            }
            refined_child_parent = {
                str(key): str(value)
                for key, value in branch_ref["refined_child_parent"].items()
            }
            coarse_branch = self.record.branches[branch_name]
            for refined_child, refined_parent in refined_child_parent.items():
                try:
                    coarse_child_atom = coarse_child[refined_child]
                    coarse_parent_atom = coarse_root[refined_parent]
                    expected_parent = coarse_branch.child_parent[coarse_child_atom]
                except KeyError as exc:
                    failures.append(
                        {
                            "branch": branch_name,
                            "refined_child": refined_child,
                            "reason": f"missing refinement datum: {exc}",
                        }
                    )
                    continue
                if coarse_parent_atom != expected_parent:
                    failures.append(
                        {
                            "branch": branch_name,
                            "refined_child": refined_child,
                            "coarse_parent_via_refinement": coarse_parent_atom,
                            "coarse_parent_via_old_atlas": expected_parent,
                        }
                    )
        return {"present": True, "failures": failures}

    def compile(self, horizon: int, functoriality_depth: int) -> dict[str, Any]:
        source_boundary_graph = {
            branch_name: match_boundary_graph(
                self.record.parent_edges,
                self.record.child_edges.get(branch_name, ()),
            )
            for branch_name in self.alphabet
        }
        source_contacts = {
            branch_name: source_boundary_graph[branch_name]["open_contacts"]
            for branch_name in self.alphabet
        }
        source_contact_failures: list[dict[str, Any]] = []
        if self.record.parent_edges:
            for branch_name in self.alphabet:
                derived = {
                    item["parent_edge"] for item in source_contacts[branch_name]
                }
                declared = set(self.record.branches[branch_name].contact_atoms)
                if derived != declared:
                    source_contact_failures.append(
                        {
                            "branch": branch_name,
                            "derived_from_boundary_words": sorted(derived),
                            "declared_contact_atoms": sorted(declared),
                        }
                    )
        word_functoriality = self.check_word_functoriality(functoriality_depth)
        synchronization = self.check_synchronization()
        refinement = self.check_refinement_naturality()
        report = {
            "alphabet": list(self.alphabet),
            "source_boundary_graph": source_boundary_graph,
            "source_boundary_contacts": source_contacts,
            "source_contact_failures": source_contact_failures,
            "contact_states": self.states_through_depth(horizon),
            "endpoint_flag_states": self.flag_states_through_depth(horizon),
            "one_to_many_atlas": self.one_to_many_atlas(),
            "source_vertex_shift_checks": self.source_vertex_shift_checks(),
            "synchronization": synchronization,
            "word_functoriality": word_functoriality,
            "refinement_naturality": refinement,
        }
        report["passed"] = (
            not source_contact_failures
            and not word_functoriality["failures"]
            and not synchronization["failures"]
            and not refinement["failures"]
        )
        return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path, help="Source atlas JSON record")
    parser.add_argument("output", type=Path, help="Compiled report JSON")
    parser.add_argument("--horizon", type=int, default=8)
    parser.add_argument("--functoriality-depth", type=int, default=5)
    args = parser.parse_args()

    with args.input.open("r", encoding="utf-8") as handle:
        data = json.load(handle)
    record = AtlasRecord.from_json(data)
    compiler = BinaryContactCompiler(record)
    report = compiler.compile(args.horizon, args.functoriality_depth)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w", encoding="utf-8") as handle:
        json.dump(report, handle, indent=2, sort_keys=True)
        handle.write("\n")
    if not report["passed"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
