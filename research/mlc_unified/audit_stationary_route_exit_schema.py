"""Finite diagnostics for the marked stationary route-exit schema.

The model checks only finite supplied bookkeeping:

* the earliest recorded failure is not skipped;
* simultaneous failure causes are not erased by a primary code;
* the complete access/sheet/window history is retained;
* the declared exit path is a literal contiguous subpath of the target route;
* only a critical-free degree-one source-domain exit is classified as clean D1.
* ambient breaks and unbroken short exits are absorbed;
* only nonshort ambient-singleton survivors become new coordinates; and
* two presentations of one physical leaf cannot be charged twice.

It does not construct a Borel KKL occurrence space, prove analytic
continuation, calculate extremal width, or establish a uniform conductance
bound.  Passing this file never promotes an analytic or ledger obligation.
"""

from __future__ import annotations

from dataclasses import dataclass, replace


CAUSE_PRIORITY = (
    "INITIAL_GERM_MISSING",
    "CRITICAL_VALUE_HIT",
    "SOURCE_DOMAIN_EXIT",
    "SHEET_COLLISION",
    "WINDOW_EXIT",
    "ACCESS_FAILURE",
    "HORIZON_EXHAUSTED",
    "TARGET_TOUCH_REENTRY",
    "OTHER_SHEET_CONTINUATION",
    "REMOTE_REACHED",
)
ALLOWED_CAUSES = frozenset(CAUSE_PRIORITY)
PRIORITY_INDEX = {
    cause: index for index, cause in enumerate(CAUSE_PRIORITY)
}


@dataclass(frozen=True)
class GateRecord:
    """One proof-authorized, non-collar route gate.

    The unbarred strings are raw geometric/marking payload.  The
    ``*_type`` strings are values of a separately supplied finite response
    quotient.  In particular, an exact occurrence window is never treated
    as a finite token merely because this diagnostic stores it as a string.
    """

    path_index: int
    stage: int
    branch: str
    branch_type: str
    access_in: str
    access_in_type: str
    access_out: str
    access_out_type: str
    cyclic_slots: tuple[int, int]
    cyclic_type: str
    sheet: str
    sheet_type: str
    window: str
    window_type: str


@dataclass(frozen=True)
class FailureEvent:
    """One cause becoming active at a discrete diagnostic time."""

    path_index: int
    cause: str


@dataclass(frozen=True)
class RetainedPredecessor:
    """One raw member of a nonempty ambient predecessor fiber.

    A stagewise list becomes a segmented occurrence flag only after actual
    containment, simple representatives, and occurrence-window extraction
    have all been certified.  The extracted occurrence embedding remains
    raw payload and is deliberately absent from ``route_signature``.
    """

    stage: int
    native_stage_action: str
    ambient_input: str
    path_token: str
    immersion_contained: bool
    simple_wave_representative: bool
    occurrence_embedding: str
    occurrence_orientation: str
    occurrence_window_extracted: bool
    fine_marked_path: bool
    coarse_subordinate: bool
    covering_image: str
    ambient_output: str


@dataclass(frozen=True)
class MarkedSwitchState:
    """Complete raw state for the exhaustive first-switch dichotomy."""

    access: str
    cyclic_slot: int
    obstacle_word: tuple[str, ...]
    occurrence_window: str
    sheet: str
    attachment_parent: str
    localization: str
    relative_cover: str
    remote_end: str
    whole_target_coverage: str
    fine_filter_status: str
    coarse_filter_status: str
    future_compatibility: str


@dataclass(frozen=True)
class RouteExitOccurrence:
    """Finite shadow of one marked measurable continuation occurrence."""

    token: str
    leaf_token: str
    proof_call: str
    horizon: int
    ambient_horizon: int
    ambient_singleton_prefix: tuple[bool, ...]
    short_member: bool
    orientation: str
    target_path: tuple[str, ...]
    source_lift: tuple[str, ...]
    immersed_source_prefix: tuple[str, ...]
    gates: tuple[GateRecord, ...]
    events: tuple[FailureEvent, ...]
    failure_index: int
    failure_causes: frozenset[str]
    primary_code: str
    failure_locus: str
    failure_locus_type: str
    active_access: str
    active_access_type: str
    requested_access: str
    requested_access_type: str
    active_sheet: str
    active_sheet_type: str
    requested_sheet: str
    requested_sheet_type: str
    active_window: str
    active_window_type: str
    requested_window: str
    requested_window_type: str
    dying_route_token: str
    replacement_route_token: str
    ambient_output_token: str
    replacement_covering_image: str
    replacement_retained: bool
    retained_predecessors: tuple[RetainedPredecessor, ...]
    first_switch_stage: int
    switch_kind: str
    dying_marked_state: MarkedSwitchState
    replacement_marked_state: MarkedSwitchState
    switch_response_type: str
    replacement_selection_basis: str
    borel_selection_claimed: bool
    uniform_fiber_bound_claimed: bool
    single_deepest_proper_path_claimed: bool
    ideal_end_survival_claimed: bool
    degree_one_corridor: bool
    critical_value_free: bool
    declared_exit_arc: tuple[str, ...]


def primary_code(causes: frozenset[str]) -> str:
    """Return the deterministic primary code without discarding the cause set."""

    if not causes:
        raise ValueError("empty cause set")
    unknown = causes - ALLOWED_CAUSES
    if unknown:
        raise ValueError(f"unknown causes: {sorted(unknown)}")
    return min(causes, key=PRIORITY_INDEX.__getitem__)


def earliest_event_data(
    events: tuple[FailureEvent, ...],
) -> tuple[int, frozenset[str]]:
    if not events:
        raise ValueError("no failure event")
    first_index = min(event.path_index for event in events)
    causes = frozenset(
        event.cause for event in events if event.path_index == first_index
    )
    return first_index, causes


def last_gate_before(
    gates: tuple[GateRecord, ...], failure_index: int
) -> GateRecord:
    eligible = tuple(
        gate for gate in gates if gate.path_index < failure_index
    )
    if not eligible:
        raise ValueError("no gate strictly before failure")
    return max(eligible, key=lambda gate: gate.path_index)


def expected_exit_arc(record: RouteExitOccurrence) -> tuple[str, ...]:
    gate = last_gate_before(record.gates, record.failure_index)
    return record.target_path[gate.path_index : record.failure_index + 1]


def validate_occurrence(
    record: RouteExitOccurrence, *, max_horizon: int
) -> list[str]:
    errors: list[str] = []

    if not record.token or not record.proof_call:
        errors.append("R0_MISSING_OCCURRENCE_ID")
    if not record.leaf_token:
        errors.append("R0_MISSING_LEAF_ID")
    # ``max_horizon`` is the ambient KKL unbreakability horizon
    # N=b+3.  A stationary route may use only h<=m_rt=N-1=b+2.
    if (
        record.horizon < 1
        or record.horizon > record.ambient_horizon - 1
    ):
        errors.append("R1_HORIZON_OUT_OF_RANGE")
    if (
        record.ambient_horizon < 2
        or record.ambient_horizon > max_horizon
    ):
        errors.append("R1_AMBIENT_HORIZON_OUT_OF_RANGE")
    singleton_word = record.ambient_singleton_prefix
    if not singleton_word:
        errors.append("R1_NO_AMBIENT_SINGLETON_WORD")
    elif False not in singleton_word:
        if len(singleton_word) != record.ambient_horizon:
            errors.append("R1_INCOMPLETE_AMBIENT_SINGLETON_WORD")
    else:
        first_false = singleton_word.index(False)
        if first_false != len(singleton_word) - 1:
            errors.append("R1_AMBIENT_STATUS_AFTER_FIRST_BREAK")
        if len(singleton_word) > record.ambient_horizon:
            errors.append("R1_AMBIENT_SINGLETON_WORD_TOO_LONG")
    if record.orientation not in {"forward", "backward"}:
        errors.append("R2_INVALID_ORIENTATION")
    if len(record.target_path) < 2:
        errors.append("R3_DEGENERATE_TARGET_PATH")
    if not 0 <= record.failure_index < len(record.target_path):
        errors.append("R4_FAILURE_INDEX_OUT_OF_RANGE")

    if not record.gates:
        errors.append("R5_NO_ROUTE_GATE")
    else:
        if record.gates[0].path_index != 0:
            errors.append("R5_FIRST_GATE_NOT_AT_SEED")
        gate_indices = tuple(gate.path_index for gate in record.gates)
        if any(
            left >= right
            for left, right in zip(gate_indices, gate_indices[1:])
        ):
            errors.append("R5_GATE_ORDER")
        gate_stages = tuple(gate.stage for gate in record.gates)
        if any(
            left > right
            for left, right in zip(gate_stages, gate_stages[1:])
        ):
            errors.append("R5_STAGE_ORDER")
        for gate in record.gates:
            if not 0 <= gate.stage <= record.horizon:
                errors.append("R5_GATE_STAGE_OUT_OF_RANGE")
            if (
                "REMOTE_REACHED" not in record.failure_causes
                and gate.path_index >= record.failure_index
            ):
                errors.append("R5_GATE_NOT_REACHED_BEFORE_FAILURE")
            if not all(
                (
                    gate.branch,
                    gate.branch_type,
                    gate.access_in,
                    gate.access_in_type,
                    gate.access_out,
                    gate.access_out_type,
                    gate.cyclic_type,
                    gate.sheet,
                    gate.sheet_type,
                    gate.window,
                    gate.window_type,
                )
            ):
                errors.append("R6_INCOMPLETE_GATE_LABEL")
            if gate.cyclic_slots[0] == gate.cyclic_slots[1]:
                errors.append("R6_MERGED_ACCESS_SLOTS")

    if not record.events:
        errors.append("R7_NO_FAILURE_EVENT")
    else:
        for event in record.events:
            if event.cause not in ALLOWED_CAUSES:
                errors.append("R7_UNKNOWN_FAILURE_CAUSE")
            if not 0 <= event.path_index < len(record.target_path):
                errors.append("R7_EVENT_INDEX_OUT_OF_RANGE")
        if not any(error.startswith("R7_") for error in errors):
            first_index, first_causes = earliest_event_data(record.events)
            if record.failure_index != first_index:
                errors.append("R8_SKIPPED_EARLIER_FAILURE")
            if record.failure_causes != first_causes:
                errors.append("R9_INCOMPLETE_SIMULTANEOUS_CAUSES")

    if not record.failure_causes:
        errors.append("R9_EMPTY_FAILURE_CAUSES")
    elif record.failure_causes <= ALLOWED_CAUSES:
        if record.primary_code != primary_code(record.failure_causes):
            errors.append("R10_WRONG_PRIMARY_CODE")
    else:
        errors.append("R9_UNKNOWN_RECORDED_CAUSE")

    if "REMOTE_REACHED" in record.failure_causes:
        if record.failure_causes != frozenset({"REMOTE_REACHED"}):
            errors.append("R11_REMOTE_MIXED_WITH_FAILURE")
        if record.failure_index != len(record.target_path) - 1:
            errors.append("R11_REMOTE_BEFORE_ROUTE_END")
        if record.declared_exit_arc:
            errors.append("R11_REMOTE_HAS_EXIT_ARC")
    else:
        if record.failure_index == 0:
            if record.failure_causes != frozenset(
                {"INITIAL_GERM_MISSING"}
            ):
                errors.append("R12_ZERO_TIME_NONINITIAL_FAILURE")
        else:
            expected_prefix = record.target_path[
                : record.failure_index + 1
            ]
            if record.immersed_source_prefix != expected_prefix:
                errors.append("R13_SOURCE_TARGET_PREFIX_MISMATCH")
            if len(record.source_lift) != len(expected_prefix):
                errors.append("R13_SOURCE_LIFT_LENGTH")
            try:
                expected_arc = expected_exit_arc(record)
            except ValueError:
                errors.append("R14_NO_GATE_BEFORE_FAILURE")
            else:
                if record.declared_exit_arc != expected_arc:
                    errors.append("R15_NOT_LITERAL_EXIT_SUBARC")
                if (
                    len(expected_arc) < 2
                    or len(set(expected_arc)) < 2
                ):
                    errors.append("R16_DEGENERATE_EXIT_SUBARC")

    terminal_labels = (
        record.failure_locus,
        record.failure_locus_type,
        record.active_access,
        record.active_access_type,
        record.requested_access,
        record.requested_access_type,
        record.active_sheet,
        record.active_sheet_type,
        record.requested_sheet,
        record.requested_sheet_type,
        record.active_window,
        record.active_window_type,
        record.requested_window,
        record.requested_window_type,
    )
    if not all(terminal_labels):
        errors.append("R17_INCOMPLETE_TERMINAL_LABEL")
    if (
        "SHEET_COLLISION" in record.failure_causes
        and record.active_sheet == record.requested_sheet
    ):
        errors.append("R18_UNWITNESSED_SHEET_COLLISION")
    if (
        "OTHER_SHEET_CONTINUATION" in record.failure_causes
        and record.active_sheet == record.requested_sheet
    ):
        errors.append("R18_UNWITNESSED_OTHER_SHEET")
    if (
        "WINDOW_EXIT" in record.failure_causes
        and record.active_window == record.requested_window
    ):
        errors.append("R19_UNWITNESSED_WINDOW_EXIT")
    if (
        "ACCESS_FAILURE" in record.failure_causes
        and record.active_access == record.requested_access
    ):
        errors.append("R20_UNWITNESSED_ACCESS_FAILURE")
    if (
        "CRITICAL_VALUE_HIT" in record.failure_causes
        and record.critical_value_free
    ):
        errors.append("R21_CRITICAL_FLAG_CONTRADICTION")
    ambient_unbroken = False not in record.ambient_singleton_prefix
    selected_route_failed = "REMOTE_REACHED" not in record.failure_causes
    if ambient_unbroken and selected_route_failed:
        if not record.replacement_retained:
            errors.append("R23_NO_RETAINED_REPLACEMENT")
        if not all(
            (
                record.dying_route_token,
                record.replacement_route_token,
                record.ambient_output_token,
                record.replacement_covering_image,
            )
        ):
            errors.append("R23_INCOMPLETE_REPLACEMENT_LABEL")
        if (
            record.replacement_covering_image
            != record.ambient_output_token
        ):
            errors.append("R25_REPLACEMENT_OUTPUT_MISMATCH")
        if len(record.retained_predecessors) != record.ambient_horizon:
            errors.append("R26_INCOMPLETE_RETAINED_PREDECESSOR_CHAIN")
        for expected_stage, retained in enumerate(
            record.retained_predecessors
        ):
            if retained.stage != expected_stage:
                errors.append("R26_RETAINED_STAGE_ORDER")
            if not all(
                (
                    retained.native_stage_action,
                    retained.ambient_input,
                    retained.path_token,
                    retained.occurrence_embedding,
                    retained.occurrence_orientation,
                    retained.covering_image,
                    retained.ambient_output,
                )
            ):
                errors.append("R26_INCOMPLETE_RETAINED_STAGE")
            if not retained.immersion_contained:
                errors.append("R26_IMMERSION_CONTAINMENT_FAILURE")
            if not retained.simple_wave_representative:
                errors.append("R26_NONSIMPLE_WAVE_REPRESENTATIVE")
            if not retained.occurrence_window_extracted:
                errors.append("R26_OCCURRENCE_WINDOW_NOT_EXTRACTED")
            if retained.occurrence_orientation not in {
                "PRESERVING",
                "REVERSING",
            }:
                errors.append("R26_INVALID_OCCURRENCE_ORIENTATION")
            if not retained.fine_marked_path:
                errors.append("R26_NOT_FINE_MARKED_PATH")
            if retained.coarse_subordinate:
                errors.append("R26_COARSE_SUBORDINATE_RETAINED_PATH")
            if retained.covering_image != retained.ambient_output:
                errors.append("R26_STAGE_OUTPUT_MISMATCH")
        if not 0 <= record.first_switch_stage < record.horizon:
            errors.append("R27_SWITCH_STAGE_OUT_OF_RANGE")
        elif record.first_switch_stage < len(
            record.retained_predecessors
        ):
            first_replacement = record.retained_predecessors[
                record.first_switch_stage
            ]
            if first_replacement.path_token != record.replacement_route_token:
                errors.append("R27_FIRST_REPLACEMENT_TOKEN_MISMATCH")
            if first_replacement.ambient_output != record.ambient_output_token:
                errors.append("R27_FIRST_REPLACEMENT_OUTPUT_MISMATCH")
        for state in (
            record.dying_marked_state,
            record.replacement_marked_state,
        ):
            if not all(
                (
                    state.access,
                    state.obstacle_word,
                    state.occurrence_window,
                    state.sheet,
                    state.attachment_parent,
                    state.localization,
                    state.relative_cover,
                    state.remote_end,
                    state.whole_target_coverage,
                    state.fine_filter_status,
                    state.coarse_filter_status,
                    state.future_compatibility,
                )
            ) or not all(state.obstacle_word):
                errors.append("R28_INCOMPLETE_MARKED_SWITCH_STATE")
        if record.switch_kind == "STRICT_PATH_REPLACEMENT":
            if record.dying_route_token == record.replacement_route_token:
                errors.append("R24_STRICT_REPLACEMENT_EQUALS_DYING_PATH")
        elif record.switch_kind == "MARKED_STATE_MISMATCH":
            if (
                record.dying_marked_state
                == record.replacement_marked_state
            ):
                errors.append("R28_UNWITNESSED_MARKED_STATE_MISMATCH")
        else:
            errors.append("R28_INVALID_SWITCH_KIND")
        if not record.switch_response_type:
            errors.append("R28_MISSING_FINITE_SWITCH_RESPONSE_TYPE")

    if record.replacement_selection_basis not in {
        "POINTWISE_FINITE_CHOICE",
        "PROVED_BOREL_SELECTOR",
    }:
        errors.append("R29_UNKNOWN_SELECTION_BASIS")
    if (
        record.replacement_selection_basis == "POINTWISE_FINITE_CHOICE"
        and record.borel_selection_claimed
    ):
        errors.append("R29_POINTWISE_DOES_NOT_PROVE_BOREL_SELECTION")
    if (
        record.replacement_selection_basis == "POINTWISE_FINITE_CHOICE"
        and record.uniform_fiber_bound_claimed
    ):
        errors.append("R30_POINTWISE_DOES_NOT_PROVE_UNIFORM_BOUND")
    if record.single_deepest_proper_path_claimed:
        errors.append("R31_PREFIX_FLAG_DOES_NOT_PROVE_DEEPEST_PROPER_PATH")
    if record.ideal_end_survival_claimed:
        errors.append("R32_WINDOWS_DO_NOT_PROVE_IDEAL_END_SURVIVAL")

    return errors


def is_clean_d1(record: RouteExitOccurrence, *, max_horizon: int) -> bool:
    """Conservative D1 classification used by the route-exit schema."""

    return (
        validate_occurrence(record, max_horizon=max_horizon) == []
        and record.failure_causes == frozenset({"SOURCE_DOMAIN_EXIT"})
        and record.degree_one_corridor
        and record.critical_value_free
    )


def response_class(record: RouteExitOccurrence) -> str:
    """Source-typed survivor reduction; route failure is not ambient break."""

    if False in record.ambient_singleton_prefix:
        return "ABSORBED_AMBIENT_BREAK"
    if record.short_member:
        return "ABSORBED_SHORT"
    return "ACTIVE_NONSHORT_SINGLETON_SURVIVOR"


def is_new_clean_d1(
    record: RouteExitOccurrence, *, max_horizon: int
) -> bool:
    return (
        is_clean_d1(record, max_horizon=max_horizon)
        and response_class(record)
        == "ACTIVE_NONSHORT_SINGLETON_SURVIVOR"
    )


def gate_type_label(gate: GateRecord) -> tuple[object, ...]:
    """Supplied finite response type; no raw geometry occurs here."""

    return (
        gate.stage,
        gate.branch_type,
        gate.access_in_type,
        gate.access_out_type,
        gate.cyclic_type,
        gate.sheet_type,
        gate.window_type,
    )


def retained_raw_label(item: RetainedPredecessor) -> tuple[object, ...]:
    """Uncompressed witness payload, deliberately excluded from kappa."""

    return (
        item.stage,
        item.native_stage_action,
        item.ambient_input,
        item.path_token,
        item.immersion_contained,
        item.simple_wave_representative,
        item.occurrence_embedding,
        item.occurrence_orientation,
        item.occurrence_window_extracted,
        item.fine_marked_path,
        item.coarse_subordinate,
        item.covering_image,
        item.ambient_output,
    )


def marked_state_raw_label(state: MarkedSwitchState) -> tuple[object, ...]:
    """Uncompressed switch state, deliberately excluded from kappa."""

    return (
        state.access,
        state.cyclic_slot,
        state.obstacle_word,
        state.occurrence_window,
        state.sheet,
        state.attachment_parent,
        state.localization,
        state.relative_cover,
        state.remote_end,
        state.whole_target_coverage,
        state.fine_filter_status,
        state.coarse_filter_status,
        state.future_compatibility,
    )


def route_signature(record: RouteExitOccurrence) -> tuple[object, ...]:
    """Finite key induced by a supplied response quotient.

    Raw paths, exact occurrence embeddings/windows, raw access/sheet labels,
    and the full retained predecessor chain remain on ``record``.  This
    routine does not prove that the supplied quotient is response-sound.
    """

    return (
        record.proof_call,
        record.horizon,
        record.ambient_horizon,
        record.ambient_singleton_prefix,
        record.short_member,
        response_class(record),
        record.orientation,
        tuple(gate_type_label(gate) for gate in record.gates),
        tuple(sorted(record.failure_causes)),
        record.primary_code,
        record.failure_locus_type,
        record.active_access_type,
        record.requested_access_type,
        record.active_sheet_type,
        record.requested_sheet_type,
        record.active_window_type,
        record.requested_window_type,
        record.first_switch_stage,
        record.switch_kind,
        record.switch_response_type,
    )


def ensure_single_valued(
    records: tuple[RouteExitOccurrence, ...],
) -> None:
    seen: dict[str, str] = {}
    for record in records:
        previous = seen.get(record.leaf_token)
        if previous is not None:
            raise ValueError(
                "R22_DUPLICATE_LEAF_OCCURRENCE: "
                f"{record.leaf_token} represented by "
                f"{previous} and {record.token}"
            )
        seen[record.leaf_token] = record.token


def compile_survivor_bookkeeping(
    records: tuple[RouteExitOccurrence, ...], *, max_horizon: int
) -> dict[tuple[object, ...], tuple[str, ...]]:
    """Compile only nonshort ambient-singleton survivor coordinates."""

    ensure_single_valued(records)
    compiled: dict[tuple[object, ...], list[str]] = {}
    for record in records:
        errors = validate_occurrence(
            record, max_horizon=max_horizon
        )
        if errors:
            raise ValueError(f"{record.token}: {errors}")
        if (
            response_class(record)
            != "ACTIVE_NONSHORT_SINGLETON_SURVIVOR"
        ):
            continue
        compiled.setdefault(route_signature(record), []).append(record.token)
    return {
        signature: tuple(tokens)
        for signature, tokens in compiled.items()
    }


def geometric_exit_family(
    records: tuple[RouteExitOccurrence, ...],
) -> frozenset[tuple[str, ...]]:
    """Union of active survivor exit arcs; rejects duplicate leaf charges."""

    ensure_single_valued(records)
    return frozenset(
        record.declared_exit_arc
        for record in records
        if record.declared_exit_arc
        and response_class(record)
        == "ACTIVE_NONSHORT_SINGLETON_SURVIVOR"
    )


def gate(
    path_index: int,
    stage: int,
    *,
    sheet: str,
    window: str,
    access: str,
    branch: str | None = None,
    sheet_type: str = "SHEET_CORE",
    window_type: str = "WINDOW_CORE",
) -> GateRecord:
    return GateRecord(
        path_index=path_index,
        stage=stage,
        branch=branch or f"branch-{stage}",
        branch_type=f"BRANCH_STAGE_{stage}",
        access_in=f"{access}-in",
        access_in_type=f"ACCESS_IN_STAGE_{stage}",
        access_out=f"{access}-out",
        access_out_type=f"ACCESS_OUT_STAGE_{stage}",
        cyclic_slots=(2 * stage, 2 * stage + 1),
        cyclic_type=f"CYCLIC_PAIR_STAGE_{stage}",
        sheet=sheet,
        sheet_type=sheet_type,
        window=window,
        window_type=window_type,
    )


def source_exit_occurrence(
    token: str = "omega-0",
    *,
    leaf_token: str | None = None,
    middle_sheet: str = "sheet-middle",
    middle_sheet_type: str = "SHEET_MIDDLE",
    middle_window: str = "window-middle",
    middle_window_type: str = "WINDOW_MIDDLE",
    terminal_sheet: str = "sheet-middle",
    terminal_window: str = "window-middle",
    events: tuple[FailureEvent, ...] | None = None,
    causes: frozenset[str] | None = None,
    primary: str | None = None,
    declared_exit_arc: tuple[str, ...] | None = None,
    horizon: int = 2,
    ambient_horizon: int = 4,
    ambient_singleton_prefix: tuple[bool, ...] | None = None,
    short_member: bool = False,
) -> RouteExitOccurrence:
    target = ("seed", "a", "middle", "c", "failure", "remote")
    event_word = events or (
        FailureEvent(4, "SOURCE_DOMAIN_EXIT"),
    )
    first_index, actual_causes = earliest_event_data(event_word)
    recorded_causes = causes or actual_causes
    gates = (
        gate(
            0,
            0,
            sheet="sheet-seed",
            window="window-seed",
            access="access-seed",
            sheet_type="SHEET_SEED",
            window_type="WINDOW_SEED",
        ),
        gate(
            2,
            1,
            sheet=middle_sheet,
            window=middle_window,
            access="access-middle",
            sheet_type=middle_sheet_type,
            window_type=middle_window_type,
        ),
    )
    exit_arc = declared_exit_arc
    if exit_arc is None:
        exit_arc = target[2 : first_index + 1]
    first_switch_stage = min(1, horizon - 1)
    ambient_nodes = tuple(
        f"ambient-path-{stage}"
        for stage in range(ambient_horizon + 1)
    )
    replacement_token = "retained-replacement-route"
    retained_chain = tuple(
        RetainedPredecessor(
            stage=stage,
            native_stage_action=f"native-KKL-F-{stage}-star",
            ambient_input=ambient_nodes[stage],
            path_token=(
                replacement_token
                if stage == first_switch_stage
                else f"retained-stage-{stage}"
            ),
            immersion_contained=True,
            simple_wave_representative=True,
            occurrence_embedding=f"raw-occurrence-map-{stage}",
            occurrence_orientation="PRESERVING",
            occurrence_window_extracted=True,
            fine_marked_path=True,
            coarse_subordinate=False,
            covering_image=ambient_nodes[stage + 1],
            ambient_output=ambient_nodes[stage + 1],
        )
        for stage in range(ambient_horizon)
    )
    first_ambient_output = ambient_nodes[first_switch_stage + 1]
    return RouteExitOccurrence(
        token=token,
        leaf_token=leaf_token or token,
        proof_call="stationary-D1",
        horizon=horizon,
        ambient_horizon=ambient_horizon,
        ambient_singleton_prefix=(
            ambient_singleton_prefix
            if ambient_singleton_prefix is not None
            else (True,) * ambient_horizon
        ),
        short_member=short_member,
        orientation="forward",
        target_path=target,
        source_lift=tuple(f"x-{point}" for point in target[: first_index + 1]),
        immersed_source_prefix=target[: first_index + 1],
        gates=gates,
        events=event_word,
        failure_index=first_index,
        failure_causes=recorded_causes,
        primary_code=primary or primary_code(recorded_causes),
        failure_locus="source-domain-boundary:end-7",
        failure_locus_type="SOURCE_END",
        active_access="access-middle-out",
        active_access_type="ACCESS_MIDDLE_OUT",
        requested_access="access-remote-in",
        requested_access_type="ACCESS_REMOTE_IN",
        active_sheet=terminal_sheet,
        active_sheet_type="SHEET_TERMINAL",
        requested_sheet="sheet-requested",
        requested_sheet_type="SHEET_REQUESTED",
        active_window=terminal_window,
        active_window_type="WINDOW_TERMINAL",
        requested_window="window-requested",
        requested_window_type="WINDOW_REQUESTED",
        dying_route_token="named-route-that-fails",
        replacement_route_token=replacement_token,
        ambient_output_token=first_ambient_output,
        replacement_covering_image=first_ambient_output,
        replacement_retained=True,
        retained_predecessors=retained_chain,
        first_switch_stage=first_switch_stage,
        switch_kind="STRICT_PATH_REPLACEMENT",
        dying_marked_state=MarkedSwitchState(
            access="access-middle-out",
            cyclic_slot=2,
            obstacle_word=("obstacle-A",),
            occurrence_window=terminal_window,
            sheet=terminal_sheet,
            attachment_parent="attachment-parent-A",
            localization="localization-central",
            relative_cover="relative-cover-compatible",
            remote_end="declared-remote-end",
            whole_target_coverage="DECLARED_TARGET_PORTION_FAILED",
            fine_filter_status="FINE_FILTER_PASSED",
            coarse_filter_status="COARSE_FILTER_PASSED",
            future_compatibility="declared-future-word",
        ),
        replacement_marked_state=MarkedSwitchState(
            access="replacement-access",
            cyclic_slot=3,
            obstacle_word=("obstacle-A",),
            occurrence_window="replacement-window",
            sheet="replacement-sheet",
            attachment_parent="attachment-parent-B",
            localization="localization-central",
            relative_cover="relative-cover-compatible",
            remote_end="actual-remote-end",
            whole_target_coverage="COMPLETE_TARGET_PORTION",
            fine_filter_status="FINE_FILTER_PASSED",
            coarse_filter_status="COARSE_FILTER_PASSED",
            future_compatibility="actual-future-word",
        ),
        switch_response_type="STRICT_REPLACEMENT_CORE",
        replacement_selection_basis="POINTWISE_FINITE_CHOICE",
        borel_selection_claimed=False,
        uniform_fiber_bound_claimed=False,
        single_deepest_proper_path_claimed=False,
        ideal_end_survival_claimed=False,
        degree_one_corridor=True,
        critical_value_free=True,
        declared_exit_arc=exit_arc,
    )


def relabel_route(
    record: RouteExitOccurrence, prefix: str
) -> RouteExitOccurrence:
    def relabel_gate(item: GateRecord) -> GateRecord:
        return replace(
            item,
            branch=f"{prefix}:{item.branch}",
            access_in=f"{prefix}:{item.access_in}",
            access_out=f"{prefix}:{item.access_out}",
            sheet=f"{prefix}:{item.sheet}",
            window=f"{prefix}:{item.window}",
        )

    def relabel_retained(
        item: RetainedPredecessor,
    ) -> RetainedPredecessor:
        return replace(
            item,
            native_stage_action=f"{prefix}:{item.native_stage_action}",
            ambient_input=f"{prefix}:{item.ambient_input}",
            path_token=f"{prefix}:{item.path_token}",
            occurrence_embedding=f"{prefix}:{item.occurrence_embedding}",
            covering_image=f"{prefix}:{item.covering_image}",
            ambient_output=f"{prefix}:{item.ambient_output}",
        )

    def relabel_state(state: MarkedSwitchState) -> MarkedSwitchState:
        return replace(
            state,
            access=f"{prefix}:{state.access}",
            obstacle_word=tuple(
                f"{prefix}:{item}" for item in state.obstacle_word
            ),
            occurrence_window=f"{prefix}:{state.occurrence_window}",
            sheet=f"{prefix}:{state.sheet}",
            attachment_parent=f"{prefix}:{state.attachment_parent}",
            localization=f"{prefix}:{state.localization}",
            relative_cover=f"{prefix}:{state.relative_cover}",
            remote_end=f"{prefix}:{state.remote_end}",
            whole_target_coverage=(
                f"{prefix}:{state.whole_target_coverage}"
            ),
            fine_filter_status=f"{prefix}:{state.fine_filter_status}",
            coarse_filter_status=(
                f"{prefix}:{state.coarse_filter_status}"
            ),
            future_compatibility=(
                f"{prefix}:{state.future_compatibility}"
            ),
        )

    return replace(
        record,
        gates=tuple(relabel_gate(item) for item in record.gates),
        active_access=f"{prefix}:{record.active_access}",
        requested_access=f"{prefix}:{record.requested_access}",
        active_sheet=f"{prefix}:{record.active_sheet}",
        requested_sheet=f"{prefix}:{record.requested_sheet}",
        active_window=f"{prefix}:{record.active_window}",
        requested_window=f"{prefix}:{record.requested_window}",
        dying_route_token=f"{prefix}:{record.dying_route_token}",
        replacement_route_token=f"{prefix}:{record.replacement_route_token}",
        ambient_output_token=f"{prefix}:{record.ambient_output_token}",
        replacement_covering_image=(
            f"{prefix}:{record.replacement_covering_image}"
        ),
        retained_predecessors=tuple(
            relabel_retained(item)
            for item in record.retained_predecessors
        ),
        dying_marked_state=relabel_state(record.dying_marked_state),
        replacement_marked_state=relabel_state(
            record.replacement_marked_state
        ),
    )


def test_valid_clean_source_exit() -> None:
    record = source_exit_occurrence()
    assert validate_occurrence(record, max_horizon=4) == []
    assert is_clean_d1(record, max_horizon=4)
    assert is_new_clean_d1(record, max_horizon=4)
    assert (
        response_class(record)
        == "ACTIVE_NONSHORT_SINGLETON_SURVIVOR"
    )
    assert record.declared_exit_arc == ("middle", "c", "failure")


def test_earlier_failure_cannot_be_skipped() -> None:
    events = (
        FailureEvent(3, "WINDOW_EXIT"),
        FailureEvent(4, "SOURCE_DOMAIN_EXIT"),
    )
    record = source_exit_occurrence(events=events)
    record = replace(
        record,
        failure_index=4,
        failure_causes=frozenset({"SOURCE_DOMAIN_EXIT"}),
        primary_code="SOURCE_DOMAIN_EXIT",
        source_lift=tuple(f"x-{point}" for point in record.target_path[:5]),
        immersed_source_prefix=record.target_path[:5],
        declared_exit_arc=record.target_path[2:5],
    )
    assert "R8_SKIPPED_EARLIER_FAILURE" in validate_occurrence(
        record, max_horizon=4
    )


def test_simultaneous_causes_must_all_survive() -> None:
    events = (
        FailureEvent(4, "SOURCE_DOMAIN_EXIT"),
        FailureEvent(4, "SHEET_COLLISION"),
    )
    record = source_exit_occurrence(
        events=events,
        causes=frozenset({"SOURCE_DOMAIN_EXIT"}),
    )
    assert "R9_INCOMPLETE_SIMULTANEOUS_CAUSES" in validate_occurrence(
        record, max_horizon=4
    )


def test_primary_code_uses_fixed_priority() -> None:
    events = (
        FailureEvent(4, "SOURCE_DOMAIN_EXIT"),
        FailureEvent(4, "CRITICAL_VALUE_HIT"),
    )
    record = source_exit_occurrence(
        events=events,
        primary="SOURCE_DOMAIN_EXIT",
    )
    assert "R10_WRONG_PRIMARY_CODE" in validate_occurrence(
        record, max_horizon=4
    )


def test_same_endpoints_do_not_prove_literal_overflow() -> None:
    record = source_exit_occurrence(
        declared_exit_arc=("middle", "invented-point", "failure"),
    )
    assert "R15_NOT_LITERAL_EXIT_SUBARC" in validate_occurrence(
        record, max_horizon=4
    )


def test_touch_and_reentry_is_not_clean_d1() -> None:
    events = (FailureEvent(4, "TARGET_TOUCH_REENTRY"),)
    record = source_exit_occurrence(events=events)
    assert validate_occurrence(record, max_horizon=4) == []
    assert not is_clean_d1(record, max_horizon=4)


def test_other_sheet_continuation_is_not_clean_d1() -> None:
    events = (FailureEvent(4, "OTHER_SHEET_CONTINUATION"),)
    record = source_exit_occurrence(events=events)
    assert validate_occurrence(record, max_horizon=4) == []
    assert not is_clean_d1(record, max_horizon=4)


def test_full_sheet_history_prevents_terminal_label_aliasing() -> None:
    left = source_exit_occurrence(
        "left",
        middle_sheet="sheet-history-left",
        middle_sheet_type="SHEET_HISTORY_LEFT",
        terminal_sheet="same-terminal-sheet",
    )
    right = source_exit_occurrence(
        "right",
        middle_sheet="sheet-history-right",
        middle_sheet_type="SHEET_HISTORY_RIGHT",
        terminal_sheet="same-terminal-sheet",
    )
    assert left.active_sheet == right.active_sheet
    assert route_signature(left) != route_signature(right)


def test_full_window_history_prevents_terminal_label_aliasing() -> None:
    left = source_exit_occurrence(
        "left",
        middle_window="window-history-left",
        middle_window_type="WINDOW_HISTORY_LEFT",
        terminal_window="same-terminal-window",
    )
    right = source_exit_occurrence(
        "right",
        middle_window="window-history-right",
        middle_window_type="WINDOW_HISTORY_RIGHT",
        terminal_window="same-terminal-window",
    )
    assert left.active_window == right.active_window
    assert route_signature(left) != route_signature(right)


def test_failure_locus_is_not_erased_by_common_labels() -> None:
    left = source_exit_occurrence("left")
    right = replace(
        source_exit_occurrence("right"),
        failure_locus="source-domain-boundary:end-8",
        failure_locus_type="DISTINCT_SOURCE_END_TYPE",
    )
    assert left.active_access == right.active_access
    assert left.active_sheet == right.active_sheet
    assert left.active_window == right.active_window
    assert route_signature(left) != route_signature(right)


def test_label_renaming_does_not_change_geometric_exit_family() -> None:
    record = source_exit_occurrence()
    renamed = relabel_route(record, "renamed")
    assert route_signature(record) == route_signature(renamed)
    assert geometric_exit_family((record,)) == geometric_exit_family(
        (renamed,)
    )


def test_raw_switch_chain_is_not_a_finite_signature_coordinate() -> None:
    record = source_exit_occurrence()
    renamed = relabel_route(record, "different-raw-witness")
    assert (
        retained_raw_label(record.retained_predecessors[0])
        != retained_raw_label(renamed.retained_predecessors[0])
    )
    assert (
        marked_state_raw_label(record.dying_marked_state)
        != marked_state_raw_label(renamed.dying_marked_state)
    )
    assert route_signature(record) == route_signature(renamed)


def test_response_type_separates_when_the_quotient_requires_it() -> None:
    record = source_exit_occurrence()
    distinct = replace(
        relabel_route(record, "different-raw-witness"),
        switch_response_type="DIFFERENT_PROVED_RESPONSE_TYPE",
    )
    assert route_signature(record) != route_signature(distinct)


def test_code_refinement_does_not_change_union_exit_geometry() -> None:
    base = source_exit_occurrence("base")
    mixed = source_exit_occurrence(
        "mixed",
        events=(
            FailureEvent(4, "SOURCE_DOMAIN_EXIT"),
            FailureEvent(4, "SHEET_COLLISION"),
        ),
    )
    assert route_signature(base) != route_signature(mixed)
    assert geometric_exit_family((base,)) == geometric_exit_family(
        (mixed,)
    )


def test_critical_or_degree_two_exit_is_not_clean_d1() -> None:
    critical = replace(
        source_exit_occurrence(
            events=(FailureEvent(4, "CRITICAL_VALUE_HIT"),)
        ),
        critical_value_free=False,
    )
    degree_two = replace(
        source_exit_occurrence("degree-two"),
        degree_one_corridor=False,
    )
    assert not is_clean_d1(critical, max_horizon=4)
    assert not is_clean_d1(degree_two, max_horizon=4)


def test_route_exit_is_not_conflated_with_kkl_break() -> None:
    record = source_exit_occurrence()
    assert record.failure_causes == frozenset({"SOURCE_DOMAIN_EXIT"})
    assert False not in record.ambient_singleton_prefix
    assert (
        response_class(record)
        == "ACTIVE_NONSHORT_SINGLETON_SURVIVOR"
    )


def test_true_ambient_break_is_absorbed() -> None:
    broken = source_exit_occurrence(
        "broken",
        ambient_singleton_prefix=(True, False),
    )
    assert validate_occurrence(broken, max_horizon=4) == []
    assert response_class(broken) == "ABSORBED_AMBIENT_BREAK"
    assert is_clean_d1(broken, max_horizon=4)
    assert not is_new_clean_d1(broken, max_horizon=4)
    assert geometric_exit_family((broken,)) == frozenset()
    assert compile_survivor_bookkeeping(
        (broken,), max_horizon=4
    ) == {}


def test_short_unbroken_exit_is_absorbed() -> None:
    short = source_exit_occurrence("short", short_member=True)
    assert validate_occurrence(short, max_horizon=4) == []
    assert response_class(short) == "ABSORBED_SHORT"
    assert is_clean_d1(short, max_horizon=4)
    assert not is_new_clean_d1(short, max_horizon=4)
    assert geometric_exit_family((short,)) == frozenset()
    assert compile_survivor_bookkeeping(
        (short,), max_horizon=4
    ) == {}


def test_duplicate_leaf_occurrences_are_rejected() -> None:
    first = source_exit_occurrence(
        "presentation-one", leaf_token="same-physical-leaf"
    )
    second = source_exit_occurrence(
        "presentation-two",
        leaf_token="same-physical-leaf",
        middle_sheet="alternate-selected-sheet",
    )
    for compiler in (
        lambda: compile_survivor_bookkeeping(
            (first, second), max_horizon=4
        ),
        lambda: geometric_exit_family((first, second)),
    ):
        try:
            compiler()
        except ValueError as error:
            assert "R22_DUPLICATE_LEAF_OCCURRENCE" in str(error)
        else:
            raise AssertionError("duplicate leaf occurrence was charged")


def test_active_survivor_requires_retained_replacement() -> None:
    missing = replace(
        source_exit_occurrence(),
        replacement_retained=False,
    )
    assert "R23_NO_RETAINED_REPLACEMENT" in validate_occurrence(
        missing, max_horizon=4
    )


def test_replacement_must_differ_from_dying_route() -> None:
    aliased = replace(
        source_exit_occurrence(),
        replacement_route_token="named-route-that-fails",
    )
    assert (
        "R24_STRICT_REPLACEMENT_EQUALS_DYING_PATH"
        in validate_occurrence(aliased, max_horizon=4)
    )


def test_replacement_must_map_to_ambient_singleton_output() -> None:
    wrong_output = replace(
        source_exit_occurrence(),
        replacement_covering_image="different-output",
    )
    assert "R25_REPLACEMENT_OUTPUT_MISMATCH" in validate_occurrence(
        wrong_output, max_horizon=4
    )


def test_survivor_requires_predecessor_at_every_stage() -> None:
    incomplete = source_exit_occurrence()
    incomplete = replace(
        incomplete,
        retained_predecessors=incomplete.retained_predecessors[:-1],
    )
    assert "R26_INCOMPLETE_RETAINED_PREDECESSOR_CHAIN" in (
        validate_occurrence(incomplete, max_horizon=4)
    )


def test_marked_state_switch_can_reuse_underlying_path() -> None:
    record = source_exit_occurrence()
    stage = record.first_switch_stage
    chain = list(record.retained_predecessors)
    chain[stage] = replace(
        chain[stage],
        path_token=record.dying_route_token,
    )
    record = replace(
        record,
        retained_predecessors=tuple(chain),
        replacement_route_token=record.dying_route_token,
        switch_kind="MARKED_STATE_MISMATCH",
    )
    assert validate_occurrence(record, max_horizon=4) == []


def test_marked_state_switch_requires_actual_state_difference() -> None:
    record = source_exit_occurrence()
    stage = record.first_switch_stage
    chain = list(record.retained_predecessors)
    chain[stage] = replace(
        chain[stage],
        path_token=record.dying_route_token,
    )
    record = replace(
        record,
        retained_predecessors=tuple(chain),
        replacement_route_token=record.dying_route_token,
        switch_kind="MARKED_STATE_MISMATCH",
        replacement_marked_state=record.dying_marked_state,
    )
    assert "R28_UNWITNESSED_MARKED_STATE_MISMATCH" in (
        validate_occurrence(record, max_horizon=4)
    )


def test_pointwise_choice_does_not_claim_borel_selection() -> None:
    overclaimed = replace(
        source_exit_occurrence(),
        borel_selection_claimed=True,
    )
    assert "R29_POINTWISE_DOES_NOT_PROVE_BOREL_SELECTION" in (
        validate_occurrence(overclaimed, max_horizon=4)
    )


def test_pointwise_choice_does_not_claim_uniform_fiber_bound() -> None:
    overclaimed = replace(
        source_exit_occurrence(),
        uniform_fiber_bound_claimed=True,
    )
    assert "R30_POINTWISE_DOES_NOT_PROVE_UNIFORM_BOUND" in (
        validate_occurrence(overclaimed, max_horizon=4)
    )


def test_incomplete_unbroken_ambient_word_is_rejected() -> None:
    incomplete = source_exit_occurrence(
        ambient_singleton_prefix=(True, True, True),
    )
    assert "R1_INCOMPLETE_AMBIENT_SINGLETON_WORD" in validate_occurrence(
        incomplete, max_horizon=4
    )


def test_status_after_first_ambient_break_is_rejected() -> None:
    impossible = source_exit_occurrence(
        ambient_singleton_prefix=(True, False, True),
    )
    assert "R1_AMBIENT_STATUS_AFTER_FIRST_BREAK" in validate_occurrence(
        impossible, max_horizon=4
    )


def test_critical_flag_contradiction_is_rejected() -> None:
    contradictory = source_exit_occurrence(
        events=(FailureEvent(4, "CRITICAL_VALUE_HIT"),)
    )
    assert "R21_CRITICAL_FLAG_CONTRADICTION" in validate_occurrence(
        contradictory, max_horizon=4
    )


def test_unreached_late_gate_is_rejected() -> None:
    record = source_exit_occurrence()
    late_gate = gate(
        5,
        2,
        sheet="future-sheet",
        window="future-window",
        access="future-access",
    )
    record = replace(record, gates=record.gates + (late_gate,))
    assert "R5_GATE_NOT_REACHED_BEFORE_FAILURE" in validate_occurrence(
        record, max_horizon=4
    )


def test_finite_compiler_keeps_distinct_histories() -> None:
    records = (
        source_exit_occurrence(
            "one",
            middle_sheet="sheet-one",
            middle_sheet_type="SHEET_TYPE_ONE",
        ),
        source_exit_occurrence(
            "two",
            middle_sheet="sheet-two",
            middle_sheet_type="SHEET_TYPE_TWO",
        ),
        source_exit_occurrence(
            "three",
            middle_window="window-three",
            middle_window_type="WINDOW_TYPE_THREE",
        ),
    )
    compiled = compile_survivor_bookkeeping(records, max_horizon=4)
    assert len(compiled) == 3
    assert sum(len(tokens) for tokens in compiled.values()) == 3


def test_horizon_bound_is_enforced() -> None:
    record = source_exit_occurrence(horizon=5)
    assert "R1_HORIZON_OUT_OF_RANGE" in validate_occurrence(
        record, max_horizon=4
    )


def test_route_horizon_stops_before_ambient_extra_stage() -> None:
    record = source_exit_occurrence(horizon=4, ambient_horizon=4)
    assert "R1_HORIZON_OUT_OF_RANGE" in validate_occurrence(
        record, max_horizon=4
    )


def test_segmented_flag_requires_actual_window_extraction() -> None:
    record = source_exit_occurrence()
    chain = list(record.retained_predecessors)
    chain[2] = replace(
        chain[2],
        occurrence_window_extracted=False,
    )
    record = replace(record, retained_predecessors=tuple(chain))
    assert "R26_OCCURRENCE_WINDOW_NOT_EXTRACTED" in validate_occurrence(
        record, max_horizon=4
    )


def test_prefix_flag_does_not_prove_deepest_path_or_end_survival() -> None:
    deepest = replace(
        source_exit_occurrence(),
        single_deepest_proper_path_claimed=True,
    )
    ends = replace(
        source_exit_occurrence(),
        ideal_end_survival_claimed=True,
    )
    assert "R31_PREFIX_FLAG_DOES_NOT_PROVE_DEEPEST_PROPER_PATH" in (
        validate_occurrence(deepest, max_horizon=4)
    )
    assert "R32_WINDOWS_DO_NOT_PROVE_IDEAL_END_SURVIVAL" in (
        validate_occurrence(ends, max_horizon=4)
    )


def main() -> None:
    tests = (
        test_valid_clean_source_exit,
        test_earlier_failure_cannot_be_skipped,
        test_simultaneous_causes_must_all_survive,
        test_primary_code_uses_fixed_priority,
        test_same_endpoints_do_not_prove_literal_overflow,
        test_touch_and_reentry_is_not_clean_d1,
        test_other_sheet_continuation_is_not_clean_d1,
        test_full_sheet_history_prevents_terminal_label_aliasing,
        test_full_window_history_prevents_terminal_label_aliasing,
        test_failure_locus_is_not_erased_by_common_labels,
        test_label_renaming_does_not_change_geometric_exit_family,
        test_raw_switch_chain_is_not_a_finite_signature_coordinate,
        test_response_type_separates_when_the_quotient_requires_it,
        test_code_refinement_does_not_change_union_exit_geometry,
        test_critical_or_degree_two_exit_is_not_clean_d1,
        test_route_exit_is_not_conflated_with_kkl_break,
        test_true_ambient_break_is_absorbed,
        test_short_unbroken_exit_is_absorbed,
        test_duplicate_leaf_occurrences_are_rejected,
        test_active_survivor_requires_retained_replacement,
        test_replacement_must_differ_from_dying_route,
        test_replacement_must_map_to_ambient_singleton_output,
        test_survivor_requires_predecessor_at_every_stage,
        test_marked_state_switch_can_reuse_underlying_path,
        test_marked_state_switch_requires_actual_state_difference,
        test_pointwise_choice_does_not_claim_borel_selection,
        test_pointwise_choice_does_not_claim_uniform_fiber_bound,
        test_incomplete_unbroken_ambient_word_is_rejected,
        test_status_after_first_ambient_break_is_rejected,
        test_critical_flag_contradiction_is_rejected,
        test_unreached_late_gate_is_rejected,
        test_finite_compiler_keeps_distinct_histories,
        test_horizon_bound_is_enforced,
        test_route_horizon_stops_before_ambient_extra_stage,
        test_segmented_flag_requires_actual_window_extraction,
        test_prefix_flag_does_not_prove_deepest_path_or_end_survival,
    )
    for test in tests:
        test()
    print(f"stationary route-exit schema regressions: {len(tests)} passed")
    print("diagnostic only; no analytic or ledger obligation promoted")


if __name__ == "__main__":
    main()
