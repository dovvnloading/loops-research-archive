"""Finite schema regressions for the stationary two-occurrence binder.

This validator checks consistency of *supplied labels*.  It cannot verify
analytic properness, prime-end landing, subordination, component separation,
or existence of a KKL occurrence.  Passing these tests never promotes a
proof obligation.
"""

from __future__ import annotations

from dataclasses import dataclass, replace


@dataclass(frozen=True)
class StageRecord:
    r: int
    parameter_token: str
    input_trace: str
    immersion_image: str
    output_trace: str
    covering_image: str
    proper: bool
    fine_marked_path: bool
    coarse_subordinate: bool
    fine_endpoints: tuple[str, str]
    coarse_endpoints: tuple[str, str]
    accesses: tuple[str, str]
    cyclic_slots: tuple[int, int]
    sheet_fiber: str
    parent_access: str
    homotopy_word: tuple[str, ...]
    terminal_wave_member: bool = False


@dataclass(frozen=True)
class OccurrenceRecord:
    alpha: str
    horizon: int
    sign: str
    full_component: str
    core_path_token: str
    core_proper: bool
    base_trace: str
    base_marked_path: bool
    base_contained_in_alpha: bool
    route: tuple[str, ...]
    route_edges: tuple[str, ...]
    stages: tuple[StageRecord, ...]


@dataclass(frozen=True)
class PairCertificate:
    minus: OccurrenceRecord
    plus: OccurrenceRecord
    component_separation_witness: str


def validate_occurrence(record: OccurrenceRecord) -> list[str]:
    errors: list[str] = []
    if record.horizon < 1:
        errors.append("F0_TOWER_TYPE: nonpositive horizon")
    if record.sign not in {"-", "+"}:
        errors.append("F6_WRONG_ROUTE: invalid sign")
    if not record.full_component:
        errors.append("F1_NO_FULL_COMPONENT")
    if not record.core_path_token:
        errors.append("F2_NO_PROPER_CORE: no common core path")
    if not record.core_proper:
        errors.append("F2_NO_PROPER_CORE")
    if not record.base_marked_path:
        errors.append("F3_NOT_FINE_MARKED_PATH: base trace")
    if not record.base_contained_in_alpha:
        errors.append("F6_WRONG_ROUTE: base trace not in leaf")
    if len(record.stages) != record.horizon:
        errors.append("F0_TOWER_TYPE: horizon/stage mismatch")

    expected_route = (
        ("BL0", "L0^(n+1)")
        if record.sign == "-"
        else ("L0^(n+1)", "boundary\\BL0")
    )
    if (
        len(record.route) < 2
        or (record.route[0], record.route[-1]) != expected_route
    ):
        errors.append("F6_WRONG_ROUTE")
    if (
        len(record.route_edges) != max(0, len(record.route) - 1)
        or not all(record.route_edges)
    ):
        errors.append("F6_WRONG_ROUTE: missing route subarc")

    previous_output: str | None = None
    common_parameter: str | None = None
    for expected_r, stage in enumerate(record.stages, start=1):
        if stage.r != expected_r:
            errors.append(f"F0_TOWER_TYPE@{expected_r}")
        if expected_r == 1 and stage.input_trace != record.base_trace:
            errors.append("F5_CARTESIAN_SYNC@1: base trace")
        if stage.immersion_image != stage.input_trace:
            errors.append(f"F5_CARTESIAN_SYNC@{stage.r}: immersion")
        if stage.covering_image != stage.output_trace:
            errors.append(f"F5_CARTESIAN_SYNC@{stage.r}: covering")
        if not stage.parameter_token:
            errors.append(f"F5_CARTESIAN_SYNC@{stage.r}: no common parameter")
        if common_parameter is None:
            common_parameter = stage.parameter_token
        elif stage.parameter_token != common_parameter:
            errors.append(f"F5_CARTESIAN_SYNC@{stage.r}: parameter mismatch")
        if previous_output is not None and stage.input_trace != previous_output:
            errors.append(f"F5_CARTESIAN_SYNC@{stage.r}: predecessor")
        if not stage.proper:
            errors.append(f"F2_NO_PROPER_CORE@{stage.r}")
        if not stage.fine_marked_path:
            errors.append(f"F3_NOT_FINE_MARKED_PATH@{stage.r}")
        if stage.coarse_subordinate:
            errors.append(f"F4_COARSE_SUBORDINATION@{stage.r}")
        if not all(stage.fine_endpoints) or not all(stage.coarse_endpoints):
            errors.append(f"F3_NOT_FINE_MARKED_PATH@{stage.r}: endpoint")
        if not all(stage.accesses):
            errors.append(f"F7_ACCESS_OR_CYCLIC_ORDER@{stage.r}")
        if stage.cyclic_slots[0] == stage.cyclic_slots[1]:
            errors.append(f"F7_ACCESS_OR_CYCLIC_ORDER@{stage.r}: merged slots")
        if not stage.sheet_fiber:
            errors.append(f"F5_CARTESIAN_SYNC@{stage.r}: sheet")
        if not stage.parent_access:
            errors.append(f"F7_ACCESS_OR_CYCLIC_ORDER@{stage.r}: parent")
        previous_output = stage.output_trace

    if record.stages and not record.stages[-1].terminal_wave_member:
        errors.append("F9_TERMINAL_NOT_IN_WAVE")
    return errors


def validate_pair(certificate: PairCertificate) -> list[str]:
    errors = validate_occurrence(certificate.minus)
    errors.extend(validate_occurrence(certificate.plus))
    if certificate.minus.sign != "-" or certificate.plus.sign != "+":
        errors.append("F6_WRONG_ROUTE: pair orientation")
    if certificate.minus.alpha != certificate.plus.alpha:
        errors.append("F0_TOWER_TYPE: different leaves")
    if certificate.minus.horizon != certificate.plus.horizon:
        errors.append("F0_TOWER_TYPE: different horizons")
    if certificate.minus.full_component == certificate.plus.full_component:
        errors.append("F8_COMPONENT_MERGER")
    if not certificate.component_separation_witness:
        errors.append("F8_COMPONENT_MERGER: no witness")
    return errors


def terminal_noncollision(certificate: PairCertificate) -> bool:
    """Later TSNC predicate; intentionally not part of binder validity."""

    minus_terminal = certificate.minus.stages[-1].output_trace
    plus_terminal = certificate.plus.stages[-1].output_trace
    return minus_terminal != plus_terminal


def stage(
    r: int,
    input_trace: str,
    output_trace: str,
    *,
    parameter_token: str = "common-t",
    coarse_subordinate: bool = False,
    parent_access: str = "actual-parent/access",
    homotopy_word: tuple[str, ...] = ("edge",),
    terminal: bool = False,
) -> StageRecord:
    return StageRecord(
        r=r,
        parameter_token=parameter_token,
        input_trace=input_trace,
        immersion_image=input_trace,
        output_trace=output_trace,
        covering_image=output_trace,
        proper=True,
        fine_marked_path=True,
        coarse_subordinate=coarse_subordinate,
        fine_endpoints=(f"fine-{r}-in", f"fine-{r}-out"),
        coarse_endpoints=(f"coarse-{r}-in", f"coarse-{r}-out"),
        accesses=(f"access-{r}-in", f"access-{r}-out"),
        cyclic_slots=(0, 1),
        sheet_fiber=f"fiber-point-{r}",
        parent_access=parent_access,
        homotopy_word=homotopy_word,
        terminal_wave_member=terminal,
    )


def occurrence(
    sign: str,
    component: str,
    *,
    terminal_trace: str = "terminal-wave",
    second_input: str = "middle",
    second_parameter_token: str = "common-t",
    coarse_subordinate: bool = False,
    parent_access: str = "actual-parent/access",
    homotopy_word: tuple[str, ...] = ("edge",),
) -> OccurrenceRecord:
    route = (
        ("BL0", "L0^(n+1)")
        if sign == "-"
        else ("L0^(n+1)", "boundary\\BL0")
    )
    return OccurrenceRecord(
        alpha="alpha-occurrence",
        horizon=2,
        sign=sign,
        full_component=component,
        core_path_token=f"theta-{sign}",
        core_proper=True,
        base_trace=f"portion-{sign}",
        base_marked_path=True,
        base_contained_in_alpha=True,
        route=route,
        route_edges=("actual-route-subarc",),
        stages=(
            stage(1, f"portion-{sign}", "middle"),
            stage(
                2,
                second_input,
                terminal_trace,
                parameter_token=second_parameter_token,
                coarse_subordinate=coarse_subordinate,
                parent_access=parent_access,
                homotopy_word=homotopy_word,
                terminal=True,
            ),
        ),
    )


def test_valid_binder_does_not_imply_terminal_noncollision() -> None:
    certificate = PairCertificate(
        minus=occurrence("-", "component-minus"),
        plus=occurrence("+", "component-plus"),
        component_separation_witness="removed-deep-obstacle",
    )
    assert validate_pair(certificate) == []
    assert not terminal_noncollision(certificate)


def test_broken_cartesian_synchronization_is_rejected() -> None:
    certificate = PairCertificate(
        minus=occurrence("-", "component-minus", second_input="wrong-middle"),
        plus=occurrence("+", "component-plus"),
        component_separation_witness="removed-deep-obstacle",
    )
    assert any(
        error.startswith("F5_CARTESIAN_SYNC")
        for error in validate_pair(certificate)
    )


def test_independent_stage_parameters_are_rejected() -> None:
    certificate = PairCertificate(
        minus=occurrence(
            "-",
            "component-minus",
            second_parameter_token="independent-s",
        ),
        plus=occurrence("+", "component-plus"),
        component_separation_witness="removed-deep-obstacle",
    )
    assert any(
        "parameter mismatch" in error
        for error in validate_pair(certificate)
    )


def test_filter_loss_is_rejected() -> None:
    certificate = PairCertificate(
        minus=occurrence(
            "-",
            "component-minus",
            coarse_subordinate=True,
        ),
        plus=occurrence("+", "component-plus"),
        component_separation_witness="removed-deep-obstacle",
    )
    assert "F4_COARSE_SUBORDINATION@2" in validate_pair(certificate)


def test_missing_parent_access_is_rejected() -> None:
    certificate = PairCertificate(
        minus=occurrence("-", "component-minus", parent_access=""),
        plus=occurrence("+", "component-plus"),
        component_separation_witness="removed-deep-obstacle",
    )
    assert any(
        "parent" in error
        for error in validate_pair(certificate)
    )


def test_merged_complete_components_are_rejected() -> None:
    certificate = PairCertificate(
        minus=occurrence("-", "same-component"),
        plus=occurrence("+", "same-component"),
        component_separation_witness="claimed-but-false",
    )
    assert "F8_COMPONENT_MERGER" in validate_pair(certificate)


def test_endpoint_labels_do_not_erase_homotopy_word() -> None:
    minus = occurrence(
        "-",
        "component-minus",
        homotopy_word=("collar", "winding-0"),
    )
    plus = occurrence(
        "+",
        "component-plus",
        homotopy_word=("collar", "winding-1"),
    )
    assert minus.stages[-1].fine_endpoints == plus.stages[-1].fine_endpoints
    assert minus.stages[-1].homotopy_word != plus.stages[-1].homotopy_word
    certificate = PairCertificate(
        minus=minus,
        plus=plus,
        component_separation_witness="different-fiber-components",
    )
    assert validate_pair(certificate) == []


def test_terminal_noncollision_is_a_separate_positive_check() -> None:
    certificate = PairCertificate(
        minus=occurrence(
            "-",
            "component-minus",
            terminal_trace="terminal-minus",
        ),
        plus=occurrence(
            "+",
            "component-plus",
            terminal_trace="terminal-plus",
        ),
        component_separation_witness="different-fiber-components",
    )
    assert validate_pair(certificate) == []
    assert terminal_noncollision(certificate)


def test_nonpositive_horizon_is_rejected() -> None:
    bad = replace(
        occurrence("-", "component-minus"),
        horizon=0,
        stages=(),
    )
    assert any(
        "nonpositive horizon" in error
        for error in validate_occurrence(bad)
    )


def test_nonproper_core_is_rejected() -> None:
    bad = replace(
        occurrence("-", "component-minus"),
        core_proper=False,
    )
    assert "F2_NO_PROPER_CORE" in validate_occurrence(bad)


def test_unmarked_base_trace_is_rejected() -> None:
    bad = replace(
        occurrence("-", "component-minus"),
        base_marked_path=False,
    )
    assert "F3_NOT_FINE_MARKED_PATH: base trace" in validate_occurrence(bad)


def test_expanded_route_uses_endpoint_semantics() -> None:
    expanded = replace(
        occurrence("-", "component-minus"),
        route=("BL0", "actual-intermediate-access", "L0^(n+1)"),
        route_edges=("subarc-1", "subarc-2"),
    )
    assert validate_occurrence(expanded) == []


def main() -> None:
    tests = (
        test_valid_binder_does_not_imply_terminal_noncollision,
        test_broken_cartesian_synchronization_is_rejected,
        test_independent_stage_parameters_are_rejected,
        test_filter_loss_is_rejected,
        test_missing_parent_access_is_rejected,
        test_merged_complete_components_are_rejected,
        test_endpoint_labels_do_not_erase_homotopy_word,
        test_terminal_noncollision_is_a_separate_positive_check,
        test_nonpositive_horizon_is_rejected,
        test_nonproper_core_is_rejected,
        test_unmarked_base_trace_is_rejected,
        test_expanded_route_uses_endpoint_semantics,
    )
    for test in tests:
        test()
    print(f"stationary binder schema regressions: {len(tests)} passed")
    print("diagnostic only; no analytic KKL obligation promoted")


if __name__ == "__main__":
    main()
