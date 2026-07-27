#!/usr/bin/env python3
r"""Generate the atomic KKL Wave source-occurrence manifest.

This is a lexical and dependency artifact.  It deliberately does not claim
that any referenced theorem is true, that its hypotheses have been
instantiated, or that a direct-decoration execution has been constructed.

The generator:

* verifies the three locked KKL source files;
* blanks inactive TeX percent comments and ``comment`` environments while
  preserving source coordinates;
* records every active ``\ref``, ``\eqref``, and citation occurrence in the
  frozen slices as a distinct, content-addressed node;
* resolves referenced labels against active ``\label`` definitions in all
  three locked files;
* retains outside-slice definitions and citations as boundary nodes;
* records the known, unresolved formal-to-actual substitutions; and
* emits a small dependency graph and its strongly connected components.

Run with ``--check`` to compare a freshly generated canonical serialization
with the checked-in JSON without rewriting it.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Iterable


ROOT = Path(__file__).resolve().parent
SOURCE_ROOT = ROOT / ".tmp_wave_audit"
DEFAULT_OUTPUT = ROOT / "kkl_wave_atomic_source_occurrence_manifest.json"


SOURCE_SPECS: tuple[dict[str, Any], ...] = (
    {
        "file": "waves-with-Misha.tex",
        "sha256": "AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5",
        "slices": ((688, 1797), (1839, 2410)),
        "role": "main Wave, ideal-marking, dynamics, clone, and Wanderers source",
    },
    {
        "file": "value1.tex",
        "sha256": "2767F71E57862DA5CF50FF7B96FC08917E24CA8F9BD2D4523C467B2E896AD83A",
        "slices": ((1, 125),),
        "role": "active expanding-Value input",
    },
    {
        "file": "not-all-good2.tex",
        "sha256": "B5D40812E40D2E44037A8FC249DB687211CD67275E66EFFF8E7F29BC7CEDFB01",
        "slices": ((1, 606),),
        "role": "active tame, covering, Wanderers, and immersion input",
    },
)

EXPECTED_COUNTS = {
    "ref_occurrences": 300,
    "eqref_occurrences": 78,
    "citation_occurrences": 18,
    "all_occurrences": 396,
    "distinct_ref_labels": 97,
    "distinct_eqref_labels": 64,
    "distinct_cross_reference_labels": 161,
    "outside_slice_boundary_labels": 8,
}

EXPECTED_BOUNDARY_LABELS = {
    "lem:compare",
    "prop:parabolically bounded combinatorics",
    "sec:hubbard trees",
    "sec:life improvement",
    "sec:limbs",
    "sec:localization",
    "sec:renorm",
    "sec:value",
}


# These are not inferred by regular expressions.  They are explicit holes in
# the formal-to-actual substitution table required by Definition 5.2 of
# direct_decoration_wave_proof_use_ledger.md.  Keeping them here makes the
# generated artifact fail closed: lexical completeness cannot be mistaken for
# an instantiated analytic execution.
UNRESOLVED_SUBSTITUTIONS: tuple[dict[str, Any], ...] = (
    {
        "id": "US-01",
        "name": "direct_decoration_execution_skeleton",
        "status": "unresolved",
        "formal_parameters": [
            "proof-occurrence stages J",
            "theorem-call occurrences C",
            "return, critical, and degree words w",
        ],
        "required_actual_fields": [
            "actual direct-decoration checkpoint",
            "every intermediate unit-stage domain and codomain",
            "actual polynomial iterate on each stage",
            "selected theorem alternative and last-use occurrence",
        ],
        "reason": (
            "The frozen source gives a native proof program, not the selected "
            "direct-decoration execution H=(J,C,w)."
        ),
        "source_anchors": [],
    },
    {
        "id": "US-02",
        "name": "native_wave_carrier_and_marking_actualization",
        "status": "unresolved",
        "formal_parameters": [
            "U, T, V=U\\T",
            "ideal marking I",
            "pulled surfaces U^n\\T^n",
            "f^n and inclusion/immersion iota_n",
        ],
        "required_actual_fields": [
            "actual direct-decoration carriers",
            "complete proof-used ideal intervals and ends",
            "actual source and target maps",
            "proper/end-proper interval certificates",
        ],
        "reason": (
            "No source-to-project substitution selects the actual marked "
            "direct-decoration Wave surface and its complete interval marking."
        ),
        "source_anchors": [
            {
                "file": "waves-with-Misha.tex",
                "line_start": 1144,
                "line_end": 1153,
                "description": "native Wave surface and carrier notation",
            },
            {
                "file": "waves-with-Misha.tex",
                "line_start": 1842,
                "line_end": 1875,
                "description": "ideal markings, paths, waves, and ends",
            },
        ],
    },
    {
        "id": "US-03",
        "name": "wave_witness_and_target_family_actualization",
        "status": "unresolved",
        "formal_parameters": [
            "A, B, and all restricted subwaves",
            "target path/lamination/WAD schemas Gamma",
            "crest, base, and endpoint intervals",
        ],
        "required_actual_fields": [
            "one target-first row per actual proof occurrence",
            "actual family constructor and filters",
            "complete endpoint/base/crest record",
            "actual downstream and last-use occurrence",
        ],
        "reason": (
            "The atomic lexical occurrences do not select geometric witness "
            "families or discharge universal KKL restriction queries."
        ),
        "source_anchors": [],
    },
    {
        "id": "US-04",
        "name": "fast_forward_formal_to_actual_package",
        "status": "unresolved",
        "formal_parameters": [
            "j, N, M, J",
            "A^ver, A^out, A^lo, A^amp",
            "B and C image families",
        ],
        "required_actual_fields": [
            "definitions of all local indices at the call site",
            "well-typed source and target intervals",
            "proved exhaustive family partition",
            "actual route and degree words",
        ],
        "reason": (
            "Main lines 1734--1797 contain undefined or inconsistent symbols "
            "and do not supply a complete actual substitution or partition proof."
        ),
        "source_anchors": [
            {
                "file": "waves-with-Misha.tex",
                "line_start": 1734,
                "line_end": 1797,
                "description": "fast-forward fan argument",
            }
        ],
    },
    {
        "id": "US-05",
        "name": "localized_wanderers_theorem_call",
        "status": "unresolved",
        "formal_parameters": [
            "B",
            "A",
            "A-hat",
            "F",
            "D",
            "d",
            "n",
        ],
        "required_actual_fields": [
            "proper map and selected compact-component packages",
            "route family with the theorem's visit hypotheses",
            "degree bound",
            "topology/diameter constant and additive error",
            "identification of the estimated source WAD stratum",
        ],
        "reason": (
            "not-all-good2.tex lines 493--500 invokes thm:wanderers without "
            "printing the theorem's complete formal-to-actual substitution."
        ),
        "source_anchors": [
            {
                "file": "not-all-good2.tex",
                "line_start": 498,
                "line_end": 498,
                "kind": "ref",
                "target": "thm:wanderers",
                "description": "uninstantiated Wanderers invocation",
            }
        ],
    },
    {
        "id": "US-06",
        "name": "K06_citation_hypothesis_substitutions",
        "status": "unresolved",
        "formal_parameters": [
            "the formal hypotheses of each cited K06 lemma or construction"
        ],
        "required_actual_fields": [
            "exact cited statement and edition/source lock",
            "actual carrier, map, compact set, and degree arguments",
            "verification of every topology and properness hypothesis",
        ],
        "reason": (
            "Five active citation occurrences use K06; a citation key and locator "
            "are not a complete theorem-call substitution."
        ),
        "source_anchors": [
            {
                "kind": "cite",
                "target": "K06",
                "description": "all active K06 citation occurrences",
            }
        ],
    },
    {
        "id": "US-07",
        "name": "wave_to_KL_pseudopiece_stage_selector",
        "status": "unresolved",
        "formal_parameters": [
            "native Wave surface U^n\\T^n",
            "native target intervals and family schemas",
        ],
        "required_actual_fields": [
            "actual puzzle piece Y and KL pseudo-piece",
            "tile label and central chart",
            "prime-end marking map",
            "lifted basepoint and deck phase",
            "source/target relative-cover subgroups",
            "seam equalizer",
        ],
        "reason": (
            "The locked KKL source contains no direct-decoration Wave-to-KL "
            "pseudo-piece selector; ambient iterate alignment does not provide one."
        ),
        "source_anchors": [],
    },
    {
        "id": "US-08",
        "name": "pullback_description_exhaustion_repair",
        "status": "unresolved",
        "formal_parameters": [
            "target interval I",
            "all components X of T'\\T attached at I",
            "maximal pulled ideal interval iota^*I",
        ],
        "required_actual_fields": [
            "a corrected maximality/exhaustion implication",
            "classification of every additional proper source path",
            "proof that no larger subordinate interval is admissible",
        ],
        "reason": (
            "Main line 1260 ends with the malformed assertion that I is not "
            "subordinate to I, so the printed proof does not establish exhaustion."
        ),
        "source_anchors": [
            {
                "file": "waves-with-Misha.tex",
                "line_start": 1262,
                "line_end": 1262,
                "kind": "ref",
                "target": "prop:pullback description",
                "description": "first downstream reference after malformed proof",
            }
        ],
    },
)


REFERENCE_RE = re.compile(
    r"\\(?P<kind>eqref|ref)\s*\{(?P<target>[^{}\r\n]+)\}"
)
CITATION_RE = re.compile(
    r"\\(?P<macro>cite[A-Za-z@*]*)\s*"
    r"(?:\[[^\]\r\n]*\]\s*)*"
    r"\{(?P<targets>[^{}\r\n]+)\}"
)
LABEL_RE = re.compile(r"\\label\s*\{(?P<label>[^{}\r\n]+)\}")
BEGIN_COMMENT_RE = re.compile(r"\\begin\s*\{comment\}")
END_COMMENT_RE = re.compile(r"\\end\s*\{comment\}")


@dataclass(frozen=True)
class LockedSource:
    file: str
    relative_path: str
    sha256: str
    text: str
    active_text: str
    slices: tuple[tuple[int, int], ...]
    role: str
    line_starts: tuple[int, ...]
    percent_comment_count: int
    comment_environment_count: int


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def stable_hash(*parts: str) -> str:
    payload = "\x1f".join(parts).encode("utf-8")
    return hashlib.sha256(payload).hexdigest().upper()


def node_id(prefix: str, digest: str) -> str:
    return f"{prefix}:{digest[:24]}"


def canonical_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n").encode(
        "utf-8"
    )


def blank_non_newline(chars: list[str], start: int, end: int) -> None:
    for index in range(start, end):
        if chars[index] not in "\r\n":
            chars[index] = " "


def strip_inactive_tex(text: str) -> tuple[str, int, int]:
    """Blank inactive TeX while preserving every character coordinate."""

    chars = list(text)
    percent_count = 0
    line_start = 0
    for line in text.splitlines(keepends=True):
        content_end = len(line.rstrip("\r\n"))
        for local_index in range(content_end):
            if line[local_index] != "%":
                continue
            slash_count = 0
            back = local_index - 1
            while back >= 0 and line[back] == "\\":
                slash_count += 1
                back -= 1
            if slash_count % 2 == 0:
                blank_non_newline(
                    chars, line_start + local_index, line_start + len(line)
                )
                percent_count += 1
                break
        line_start += len(line)

    percent_stripped = "".join(chars)
    search_from = 0
    environment_count = 0
    while True:
        begin = BEGIN_COMMENT_RE.search(percent_stripped, search_from)
        if begin is None:
            break
        end = END_COMMENT_RE.search(percent_stripped, begin.end())
        span_end = len(percent_stripped) if end is None else end.end()
        blank_non_newline(chars, begin.start(), span_end)
        environment_count += 1
        if end is None:
            break
        search_from = span_end
        percent_stripped = "".join(chars)

    active = "".join(chars)
    if len(active) != len(text):
        raise AssertionError("inactive-text stripping changed source coordinates")
    return active, percent_count, environment_count


def compute_line_starts(text: str) -> tuple[int, ...]:
    starts = [0]
    for match in re.finditer(r"\n", text):
        starts.append(match.end())
    return tuple(starts)


def position(line_starts: tuple[int, ...], offset: int) -> tuple[int, int]:
    # The source files are small enough that binary search from bisect is ample.
    import bisect

    line_index = bisect.bisect_right(line_starts, offset) - 1
    return line_index + 1, offset - line_starts[line_index] + 1


def line_span_offsets(
    text: str, line_starts: tuple[int, ...], start_line: int, end_line: int
) -> tuple[int, int]:
    if start_line < 1 or end_line < start_line:
        raise ValueError(f"invalid line span {start_line}--{end_line}")
    line_count = len(line_starts)
    if end_line > line_count:
        raise ValueError(
            f"line span {start_line}--{end_line} exceeds {line_count} lines"
        )
    start = line_starts[start_line - 1]
    end = line_starts[end_line] if end_line < line_count else len(text)
    return start, end


def line_in_slices(line: int, slices: Iterable[tuple[int, int]]) -> bool:
    return any(start <= line <= end for start, end in slices)


def load_sources() -> list[LockedSource]:
    sources: list[LockedSource] = []
    for spec in SOURCE_SPECS:
        path = SOURCE_ROOT / spec["file"]
        raw = path.read_bytes()
        actual_hash = sha256_bytes(raw)
        if actual_hash != spec["sha256"]:
            raise RuntimeError(
                f"source-lock failure for {path}: expected {spec['sha256']}, "
                f"found {actual_hash}"
            )
        text = raw.decode("utf-8")
        active_text, percent_count, environment_count = strip_inactive_tex(text)
        sources.append(
            LockedSource(
                file=spec["file"],
                relative_path=f".tmp_wave_audit/{spec['file']}",
                sha256=actual_hash,
                text=text,
                active_text=active_text,
                slices=tuple(spec["slices"]),
                role=spec["role"],
                line_starts=compute_line_starts(text),
                percent_comment_count=percent_count,
                comment_environment_count=environment_count,
            )
        )
    return sources


def occurrence_record(
    source: LockedSource,
    kind: str,
    macro: str,
    targets: list[str],
    start: int,
    end: int,
) -> dict[str, Any]:
    line, column = position(source.line_starts, start)
    end_line, end_column = position(source.line_starts, end)
    source_text = source.text[start:end]
    active_text = source.active_text[start:end]
    digest = stable_hash(
        "occurrence-v1",
        source.sha256,
        kind,
        str(line),
        str(column),
        source_text,
        "\x1e".join(targets),
    )
    return {
        "id": node_id("occ", digest),
        "occurrence_sha256": digest,
        "kind": kind,
        "macro": macro,
        "targets": targets,
        "source_file": source.file,
        "source_sha256": source.sha256,
        "line": line,
        "column": column,
        "end_line": end_line,
        "end_column_exclusive": end_column,
        "char_offset": start,
        "char_end_offset_exclusive": end,
        "source_text": source_text,
        "active_text": active_text,
        "resolution": None,
    }


def extract_occurrences(sources: list[LockedSource]) -> list[dict[str, Any]]:
    occurrences: list[dict[str, Any]] = []
    for source in sources:
        for start_line, end_line in source.slices:
            span_start, span_end = line_span_offsets(
                source.text, source.line_starts, start_line, end_line
            )
            active_span = source.active_text[span_start:span_end]
            for match in REFERENCE_RE.finditer(active_span):
                start = span_start + match.start()
                end = span_start + match.end()
                occurrences.append(
                    occurrence_record(
                        source=source,
                        kind=match.group("kind"),
                        macro=match.group("kind"),
                        targets=[match.group("target").strip()],
                        start=start,
                        end=end,
                    )
                )
            for match in CITATION_RE.finditer(active_span):
                start = span_start + match.start()
                end = span_start + match.end()
                targets = [
                    key.strip()
                    for key in match.group("targets").split(",")
                    if key.strip()
                ]
                occurrences.append(
                    occurrence_record(
                        source=source,
                        kind="cite",
                        macro=match.group("macro"),
                        targets=targets,
                        start=start,
                        end=end,
                    )
                )
    source_order = {spec["file"]: index for index, spec in enumerate(SOURCE_SPECS)}
    occurrences.sort(
        key=lambda item: (
            source_order[item["source_file"]],
            item["char_offset"],
            item["kind"],
        )
    )
    ids = [item["id"] for item in occurrences]
    if len(ids) != len(set(ids)):
        raise AssertionError("occurrence node IDs are not unique")
    return occurrences


def extract_label_definitions(
    sources: list[LockedSource],
) -> tuple[list[dict[str, Any]], dict[str, list[dict[str, Any]]]]:
    definitions: list[dict[str, Any]] = []
    by_label: dict[str, list[dict[str, Any]]] = {}
    source_order = {spec["file"]: index for index, spec in enumerate(SOURCE_SPECS)}
    for source in sources:
        for match in LABEL_RE.finditer(source.active_text):
            line, column = position(source.line_starts, match.start())
            end_line, end_column = position(source.line_starts, match.end())
            label = match.group("label").strip()
            digest = stable_hash(
                "definition-v1",
                source.sha256,
                label,
                str(line),
                str(column),
                source.text[match.start() : match.end()],
            )
            record = {
                "id": node_id("def", digest),
                "definition_sha256": digest,
                "label": label,
                "source_file": source.file,
                "source_sha256": source.sha256,
                "line": line,
                "column": column,
                "end_line": end_line,
                "end_column_exclusive": end_column,
                "in_frozen_slice": line_in_slices(line, source.slices),
                "source_text": source.text[match.start() : match.end()],
            }
            definitions.append(record)
            by_label.setdefault(label, []).append(record)
    definitions.sort(
        key=lambda item: (
            source_order[item["source_file"]],
            item["line"],
            item["column"],
        )
    )
    return definitions, by_label


def make_citation_nodes(
    occurrences: list[dict[str, Any]],
) -> dict[str, dict[str, Any]]:
    keys = sorted(
        {
            target
            for occurrence in occurrences
            if occurrence["kind"] == "cite"
            for target in occurrence["targets"]
        }
    )
    result: dict[str, dict[str, Any]] = {}
    for key in keys:
        digest = stable_hash("citation-boundary-v1", key)
        result[key] = {
            "id": node_id("cite", digest),
            "citation_sha256": digest,
            "key": key,
            "status": "external_boundary_not_resolved_by_three_source_lock",
        }
    return result


def resolve_occurrences(
    occurrences: list[dict[str, Any]],
    definitions_by_label: dict[str, list[dict[str, Any]]],
    citation_nodes: dict[str, dict[str, Any]],
) -> tuple[list[dict[str, Any]], list[dict[str, Any]], list[str]]:
    unresolved_labels: list[str] = []
    boundary_by_label: dict[str, dict[str, Any]] = {}
    for occurrence in occurrences:
        if occurrence["kind"] == "cite":
            occurrence["resolution"] = {
                "status": "external_citation_boundary",
                "target_node_ids": [
                    citation_nodes[key]["id"] for key in occurrence["targets"]
                ],
            }
            continue

        label = occurrence["targets"][0]
        definitions = definitions_by_label.get(label, [])
        if not definitions:
            unresolved_labels.append(label)
            occurrence["resolution"] = {
                "status": "unresolved_label",
                "target_node_ids": [],
            }
            continue
        inside = [item for item in definitions if item["in_frozen_slice"]]
        status = (
            "resolved_inside_frozen_slice"
            if inside
            else "resolved_outside_frozen_slice_boundary"
        )
        occurrence["resolution"] = {
            "status": status,
            "target_node_ids": [item["id"] for item in definitions],
        }
        if status == "resolved_outside_frozen_slice_boundary":
            boundary = boundary_by_label.setdefault(
                label,
                {
                    "label": label,
                    "definition_node_ids": [item["id"] for item in definitions],
                    "definition_locations": [
                        {
                            "source_file": item["source_file"],
                            "line": item["line"],
                            "column": item["column"],
                        }
                        for item in definitions
                    ],
                    "incoming_occurrence_ids": [],
                },
            )
            boundary["incoming_occurrence_ids"].append(occurrence["id"])

    boundaries = [boundary_by_label[key] for key in sorted(boundary_by_label)]
    return occurrences, boundaries, sorted(set(unresolved_labels))


def substitution_records(
    occurrences: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for template in UNRESOLVED_SUBSTITUTIONS:
        record = dict(template)
        digest = stable_hash(
            "unresolved-substitution-v1",
            record["id"],
            record["name"],
            json.dumps(record["formal_parameters"], sort_keys=True),
            json.dumps(record["required_actual_fields"], sort_keys=True),
        )
        record["node_id"] = node_id("subst", digest)
        record["substitution_sha256"] = digest
        anchor_ids: list[str] = []
        for anchor in record["source_anchors"]:
            for occurrence in occurrences:
                if "file" in anchor and occurrence["source_file"] != anchor["file"]:
                    continue
                if "line_start" in anchor and not (
                    anchor["line_start"]
                    <= occurrence["line"]
                    <= anchor["line_end"]
                ):
                    continue
                if "kind" in anchor and occurrence["kind"] != anchor["kind"]:
                    continue
                if "target" in anchor and anchor["target"] not in occurrence["targets"]:
                    continue
                anchor_ids.append(occurrence["id"])
        record["source_anchor_occurrence_ids"] = sorted(set(anchor_ids))
        records.append(record)
    return records


def dependency_edge(source: str, target: str, relation: str) -> dict[str, str]:
    digest = stable_hash("edge-v1", source, target, relation)
    return {
        "id": node_id("edge", digest),
        "source": source,
        "target": target,
        "relation": relation,
    }


def tarjan_scc(
    node_ids: list[str], edges: list[dict[str, str]]
) -> tuple[list[dict[str, Any]], list[dict[str, str]]]:
    adjacency: dict[str, list[str]] = {node: [] for node in node_ids}
    for edge in edges:
        adjacency[edge["source"]].append(edge["target"])
    for targets in adjacency.values():
        targets.sort()

    index = 0
    stack: list[str] = []
    on_stack: set[str] = set()
    indices: dict[str, int] = {}
    lowlink: dict[str, int] = {}
    raw_components: list[list[str]] = []

    def visit(vertex: str) -> None:
        nonlocal index
        indices[vertex] = index
        lowlink[vertex] = index
        index += 1
        stack.append(vertex)
        on_stack.add(vertex)
        for target in adjacency[vertex]:
            if target not in indices:
                visit(target)
                lowlink[vertex] = min(lowlink[vertex], lowlink[target])
            elif target in on_stack:
                lowlink[vertex] = min(lowlink[vertex], indices[target])
        if lowlink[vertex] == indices[vertex]:
            component: list[str] = []
            while True:
                member = stack.pop()
                on_stack.remove(member)
                component.append(member)
                if member == vertex:
                    break
            raw_components.append(sorted(component))

    for node in sorted(node_ids):
        if node not in indices:
            visit(node)

    self_loops = {
        edge["source"] for edge in edges if edge["source"] == edge["target"]
    }
    components: list[dict[str, Any]] = []
    membership: dict[str, str] = {}
    for members in sorted(raw_components, key=lambda group: group[0]):
        digest = stable_hash("scc-v1", *members)
        component_id = node_id("scc", digest)
        cyclic = len(members) > 1 or any(member in self_loops for member in members)
        record = {
            "id": component_id,
            "members": members,
            "size": len(members),
            "cyclic": cyclic,
        }
        components.append(record)
        for member in members:
            membership[member] = component_id

    condensation_pairs = sorted(
        {
            (membership[edge["source"]], membership[edge["target"]])
            for edge in edges
            if membership[edge["source"]] != membership[edge["target"]]
        }
    )
    condensation_edges = [
        {
            "source_scc": source,
            "target_scc": target,
        }
        for source, target in condensation_pairs
    ]
    return components, condensation_edges


def build_dependency_manifest(
    occurrences: list[dict[str, Any]],
    definitions: list[dict[str, Any]],
    citation_nodes: dict[str, dict[str, Any]],
    substitutions: list[dict[str, Any]],
) -> dict[str, Any]:
    referenced_definition_ids = {
        target
        for occurrence in occurrences
        for target in occurrence["resolution"]["target_node_ids"]
        if target.startswith("def:")
    }
    graph_nodes: list[dict[str, Any]] = []
    for occurrence in occurrences:
        graph_nodes.append(
            {
                "id": occurrence["id"],
                "kind": "source_occurrence",
                "occurrence_kind": occurrence["kind"],
            }
        )
    for definition in definitions:
        if definition["id"] in referenced_definition_ids:
            graph_nodes.append(
                {
                    "id": definition["id"],
                    "kind": "label_definition",
                    "label": definition["label"],
                }
            )
    for citation in citation_nodes.values():
        graph_nodes.append(
            {
                "id": citation["id"],
                "kind": "citation_boundary",
                "key": citation["key"],
            }
        )
    for substitution in substitutions:
        graph_nodes.append(
            {
                "id": substitution["node_id"],
                "kind": "unresolved_formal_to_actual_substitution",
                "substitution_id": substitution["id"],
            }
        )
    graph_nodes.sort(key=lambda item: item["id"])

    edges: list[dict[str, str]] = []
    for occurrence in occurrences:
        relation = (
            "imports_citation_boundary"
            if occurrence["kind"] == "cite"
            else "resolves_label_to"
        )
        for target in occurrence["resolution"]["target_node_ids"]:
            edges.append(dependency_edge(occurrence["id"], target, relation))
    for substitution in substitutions:
        for anchor_id in substitution["source_anchor_occurrence_ids"]:
            edges.append(
                dependency_edge(
                    substitution["node_id"], anchor_id, "anchored_at_occurrence"
                )
            )
    edges.sort(key=lambda item: (item["source"], item["target"], item["relation"]))
    edge_ids = [edge["id"] for edge in edges]
    if len(edge_ids) != len(set(edge_ids)):
        raise AssertionError("dependency edge IDs are not unique")

    node_ids = [node["id"] for node in graph_nodes]
    components, condensation_edges = tarjan_scc(node_ids, edges)
    return {
        "edge_direction": "source node requires target node",
        "nodes": graph_nodes,
        "edges": edges,
        "strongly_connected_components": components,
        "condensation_edges": condensation_edges,
        "summary": {
            "node_count": len(graph_nodes),
            "edge_count": len(edges),
            "scc_count": len(components),
            "cyclic_scc_count": sum(1 for item in components if item["cyclic"]),
            "condensation_edge_count": len(condensation_edges),
        },
    }


def build_manifest() -> dict[str, Any]:
    sources = load_sources()
    occurrences = extract_occurrences(sources)
    definitions, definitions_by_label = extract_label_definitions(sources)
    citation_nodes = make_citation_nodes(occurrences)
    occurrences, boundaries, unresolved_labels = resolve_occurrences(
        occurrences, definitions_by_label, citation_nodes
    )
    substitutions = substitution_records(occurrences)

    ref_occurrences = [item for item in occurrences if item["kind"] == "ref"]
    eqref_occurrences = [item for item in occurrences if item["kind"] == "eqref"]
    cite_occurrences = [item for item in occurrences if item["kind"] == "cite"]
    ref_labels = {item["targets"][0] for item in ref_occurrences}
    eqref_labels = {item["targets"][0] for item in eqref_occurrences}
    cross_reference_labels = ref_labels | eqref_labels

    actual_counts = {
        "ref_occurrences": len(ref_occurrences),
        "eqref_occurrences": len(eqref_occurrences),
        "citation_occurrences": len(cite_occurrences),
        "all_occurrences": len(occurrences),
        "distinct_ref_labels": len(ref_labels),
        "distinct_eqref_labels": len(eqref_labels),
        "distinct_cross_reference_labels": len(cross_reference_labels),
        "outside_slice_boundary_labels": len(boundaries),
    }
    if actual_counts != EXPECTED_COUNTS:
        raise AssertionError(
            f"frozen-slice count mismatch: expected {EXPECTED_COUNTS}, "
            f"found {actual_counts}"
        )
    boundary_labels = {item["label"] for item in boundaries}
    if boundary_labels != EXPECTED_BOUNDARY_LABELS:
        raise AssertionError(
            "outside-slice boundary mismatch: expected "
            f"{sorted(EXPECTED_BOUNDARY_LABELS)}, found {sorted(boundary_labels)}"
        )
    if unresolved_labels:
        raise AssertionError(
            f"unresolved cross-reference labels in three-file universe: "
            f"{unresolved_labels}"
        )
    if any(len(items) != 1 for items in definitions_by_label.values()):
        duplicates = {
            label: [item["id"] for item in items]
            for label, items in definitions_by_label.items()
            if len(items) != 1
        }
        raise AssertionError(f"ambiguous active label definitions: {duplicates}")

    dependency_manifest = build_dependency_manifest(
        occurrences, definitions, citation_nodes, substitutions
    )
    source_records = [
        {
            "file": source.file,
            "relative_path": source.relative_path,
            "sha256": source.sha256,
            "role": source.role,
            "frozen_slices": [
                {"start_line": start, "end_line": end}
                for start, end in source.slices
            ],
            "line_count": len(source.line_starts),
            "inactive_tex_audit": {
                "percent_comment_starts": source.percent_comment_count,
                "comment_environments": source.comment_environment_count,
                "coordinate_preserving": True,
            },
        }
        for source in sources
    ]

    return {
        "schema": "kkl-wave-atomic-source-occurrence-manifest-v1",
        "generated_by": "generate_kkl_wave_atomic_source_manifest.py",
        "artifact_scope": (
            "lexical source occurrences, label/citation boundaries, unresolved "
            "formal-to-actual substitutions, and a simple dependency/SCC graph"
        ),
        "promotion_policy": {
            "promotes_proof_obligation": False,
            "direct_decoration_wave_proof_use_ledger_status": "open",
            "reason": (
                "The manifest is an atomic source prerequisite.  US-01--US-08 "
                "remain unresolved and no actual direct-decoration execution is "
                "constructed."
            ),
        },
        "source_locks": source_records,
        "frozen_program": {
            "inactive_tex_policy": (
                "blank unescaped-percent comments and comment environments "
                "without changing line or column coordinates"
            ),
            "occurrence_policy": (
                "each active macro occurrence is a distinct node; repeated use "
                "of one label is never deduplicated"
            ),
            "counts": actual_counts,
            "expected_counts": EXPECTED_COUNTS,
        },
        "occurrences": occurrences,
        "label_resolution": {
            "all_active_definitions_in_locked_files": definitions,
            "active_definition_count": len(definitions),
            "referenced_label_count": len(cross_reference_labels),
            "unresolved_cross_reference_labels": unresolved_labels,
            "outside_slice_boundary_labels": boundaries,
        },
        "citation_boundaries": [
            citation_nodes[key] for key in sorted(citation_nodes)
        ],
        "unresolved_formal_to_actual_substitutions": substitutions,
        "dependency_manifest": dependency_manifest,
        "validation": {
            "source_hashes_match": True,
            "coordinates_preserved_after_inactive_text_stripping": True,
            "occurrence_ids_unique": True,
            "all_cross_reference_labels_resolved_across_locked_files": True,
            "outside_slice_boundary_set_exact": True,
            "counts_exact": True,
            "formal_to_actual_table_complete_status": "explicitly_incomplete",
            "analytic_truth_claimed": False,
        },
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--output",
        type=Path,
        default=DEFAULT_OUTPUT,
        help=f"output path (default: {DEFAULT_OUTPUT})",
    )
    parser.add_argument(
        "--check",
        action="store_true",
        help="compare generated canonical JSON with the existing output",
    )
    args = parser.parse_args()

    manifest = build_manifest()
    encoded = canonical_bytes(manifest)
    if args.check:
        if not args.output.exists():
            print(f"missing generated manifest: {args.output}", file=sys.stderr)
            return 1
        existing = args.output.read_bytes()
        if existing != encoded:
            print(
                f"generated manifest is stale: {args.output}\n"
                f"expected sha256 {sha256_bytes(encoded)}\n"
                f"existing sha256 {sha256_bytes(existing)}",
                file=sys.stderr,
            )
            return 1
        print(
            "PASS atomic manifest is current: "
            f"{args.output} sha256={sha256_bytes(encoded)}"
        )
        return 0

    args.output.write_bytes(encoded)
    counts = manifest["frozen_program"]["counts"]
    graph = manifest["dependency_manifest"]["summary"]
    print(
        "WROTE "
        f"{args.output} sha256={sha256_bytes(encoded)} "
        f"ref={counts['ref_occurrences']} "
        f"eqref={counts['eqref_occurrences']} "
        f"cite={counts['citation_occurrences']} "
        f"boundary={counts['outside_slice_boundary_labels']} "
        f"nodes={graph['node_count']} edges={graph['edge_count']} "
        f"scc={graph['scc_count']}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
