"""Finite regressions for the segmented KKL occurrence invariant.

This script checks only the finite bookkeeping proved in
``kkl_stationary_two_occurrence_source_attack.md`` Section 12.  It does
not prove that any analytic KKL restriction exists, lands at a prime
end, survives the marking filter, or has positive extremal width.
Passing it cannot promote a proof obligation.
"""

from __future__ import annotations

from dataclasses import dataclass, replace
from fractions import Fraction


@dataclass(frozen=True)
class AffineWindow:
    """An increasing affine embedding t |-> lo + (hi-lo)t."""

    lo: Fraction
    hi: Fraction

    def valid(self) -> bool:
        return Fraction(0) <= self.lo < self.hi <= Fraction(1)

    def compose(self, inner: "AffineWindow") -> "AffineWindow":
        """Return self o inner."""

        span = self.hi - self.lo
        return AffineWindow(
            self.lo + span * inner.lo,
            self.lo + span * inner.hi,
        )


IDENTITY_WINDOW = AffineWindow(Fraction(0), Fraction(1))


@dataclass(frozen=True)
class StageExtension:
    r: int
    input_trace: str
    full_lift: str
    output_trace: str
    window: AffineWindow
    immersion_factorization_witness: str
    covering_factorization_witness: str
    full_lift_proper: bool
    fine_marked: bool
    coarse_subordinate: bool
    endpoint_accesses: tuple[str, str]
    route_witness: str
    terminal_wave_member: bool = False


@dataclass(frozen=True)
class SegmentedOccurrence:
    alpha: str
    sign: str
    stages: tuple[StageExtension, ...]


@dataclass(frozen=True)
class SegmentedPair:
    minus: SegmentedOccurrence
    plus: SegmentedOccurrence


def cumulative_windows(
    occurrence: SegmentedOccurrence,
) -> tuple[AffineWindow, ...]:
    """Return A_{r,h}=a_{r+1} o ... o a_h for r=1,...,h."""

    h = len(occurrence.stages)
    result: list[AffineWindow] = [IDENTITY_WINDOW for _ in range(h)]
    running = IDENTITY_WINDOW
    for index in range(h - 2, -1, -1):
        next_window = occurrence.stages[index + 1].window
        running = next_window.compose(running)
        result[index] = running
    return tuple(result)


def base_nested_window(occurrence: SegmentedOccurrence) -> AffineWindow:
    """Return a_1 o ... o a_h, the base trace window."""

    result = IDENTITY_WINDOW
    for stage in reversed(occurrence.stages):
        result = stage.window.compose(result)
    return result


def validate_occurrence(occurrence: SegmentedOccurrence) -> list[str]:
    errors: list[str] = []
    if occurrence.sign not in {"-", "+"}:
        errors.append("S0_BAD_ROUTE_SIGN")
    if not occurrence.stages:
        errors.append("S0_EMPTY_HORIZON")
        return errors

    previous = occurrence.alpha
    for expected_r, stage in enumerate(occurrence.stages, start=1):
        if stage.r != expected_r:
            errors.append(f"S0_STAGE_INDEX@{expected_r}")
        if stage.input_trace != previous:
            errors.append(f"S1_PREDECESSOR_MISMATCH@{expected_r}")
        if not stage.full_lift:
            errors.append(f"S2_NO_FULL_STAGE_EXTENSION@{expected_r}")
        if not stage.window.valid():
            errors.append(f"S3_INVALID_WINDOW@{expected_r}")
        if not stage.immersion_factorization_witness:
            errors.append(f"S4_NO_IMMERSION_FACTORIZATION@{expected_r}")
        if not stage.covering_factorization_witness:
            errors.append(f"S5_NO_COVERING_FACTORIZATION@{expected_r}")
        if not stage.full_lift_proper:
            errors.append(f"S6_STAGE_NONPROPER@{expected_r}")
        if not stage.fine_marked:
            errors.append(f"S7_STAGE_NOT_FINE_MARKED@{expected_r}")
        if stage.coarse_subordinate:
            errors.append(f"S8_STAGE_COARSE_SUBORDINATION@{expected_r}")
        if not all(stage.endpoint_accesses):
            errors.append(f"S9_MISSING_ACCESS@{expected_r}")
        if not stage.route_witness:
            errors.append(f"S10_MISSING_ROUTE_WITNESS@{expected_r}")
        previous = stage.output_trace

    if not occurrence.stages[-1].terminal_wave_member:
        errors.append("S11_TERMINAL_NOT_IN_WAVE")
    return errors


def validate_pair(pair: SegmentedPair) -> list[str]:
    errors = validate_occurrence(pair.minus)
    errors.extend(validate_occurrence(pair.plus))
    if pair.minus.sign != "-" or pair.plus.sign != "+":
        errors.append("S0_PAIR_ORIENTATION")
    if pair.minus.alpha != pair.plus.alpha:
        errors.append("S0_DIFFERENT_BASE_LEAVES")
    return errors


def stage(
    r: int,
    input_trace: str,
    output_trace: str,
    *,
    window: AffineWindow = AffineWindow(Fraction(1, 4), Fraction(3, 4)),
    terminal: bool = False,
) -> StageExtension:
    return StageExtension(
        r=r,
        input_trace=input_trace,
        full_lift=f"gamma-{r}-{input_trace}",
        output_trace=output_trace,
        window=window,
        immersion_factorization_witness=f"i-gamma-{r}=delta-{r-1}-on-window",
        covering_factorization_witness=f"f-gamma-{r}=delta-{r}",
        full_lift_proper=True,
        fine_marked=True,
        coarse_subordinate=False,
        endpoint_accesses=(f"access-{r}-in", f"access-{r}-out"),
        route_witness=f"route-{r}",
        terminal_wave_member=terminal,
    )


def occurrence(sign: str, terminal_trace: str = "terminal") -> SegmentedOccurrence:
    return SegmentedOccurrence(
        alpha="alpha",
        sign=sign,
        stages=(
            stage(1, "alpha", f"middle-{sign}"),
            stage(2, f"middle-{sign}", terminal_trace, terminal=True),
        ),
    )


def test_valid_nested_chain() -> None:
    record = occurrence("-")
    assert validate_occurrence(record) == []
    assert cumulative_windows(record)[0] == record.stages[1].window
    expected = record.stages[0].window.compose(record.stages[1].window)
    assert base_nested_window(record) == expected


def test_proper_window_is_allowed() -> None:
    """A strict window is the native case, not a schema failure."""

    record = occurrence("-")
    assert record.stages[0].window != IDENTITY_WINDOW
    assert validate_occurrence(record) == []


def test_missing_full_extension_is_rejected() -> None:
    record = occurrence("-")
    bad_stage = replace(record.stages[1], full_lift="")
    bad = replace(record, stages=(record.stages[0], bad_stage))
    assert "S2_NO_FULL_STAGE_EXTENSION@2" in validate_occurrence(bad)


def test_nonproper_full_extension_is_rejected() -> None:
    record = occurrence("-")
    bad_stage = replace(record.stages[0], full_lift_proper=False)
    bad = replace(record, stages=(bad_stage, record.stages[1]))
    assert "S6_STAGE_NONPROPER@1" in validate_occurrence(bad)


def test_filter_failure_is_rejected() -> None:
    record = occurrence("-")
    bad_stage = replace(record.stages[0], coarse_subordinate=True)
    bad = replace(record, stages=(bad_stage, record.stages[1]))
    assert "S8_STAGE_COARSE_SUBORDINATION@1" in validate_occurrence(bad)


def test_predecessor_mismatch_is_rejected() -> None:
    record = occurrence("-")
    bad_stage = replace(record.stages[1], input_trace="unrelated")
    bad = replace(record, stages=(record.stages[0], bad_stage))
    assert "S1_PREDECESSOR_MISMATCH@2" in validate_occurrence(bad)


def test_invalid_window_is_rejected() -> None:
    record = occurrence("-")
    bad_stage = replace(
        record.stages[0],
        window=AffineWindow(Fraction(3, 4), Fraction(1, 4)),
    )
    bad = replace(record, stages=(bad_stage, record.stages[1]))
    assert "S3_INVALID_WINDOW@1" in validate_occurrence(bad)


def test_pair_validity_does_not_imply_terminal_noncollision() -> None:
    pair = SegmentedPair(
        minus=occurrence("-", terminal_trace="same-terminal"),
        plus=occurrence("+", terminal_trace="same-terminal"),
    )
    assert validate_pair(pair) == []
    assert (
        pair.minus.stages[-1].output_trace
        == pair.plus.stages[-1].output_trace
    )


def run() -> None:
    tests = [
        test_valid_nested_chain,
        test_proper_window_is_allowed,
        test_missing_full_extension_is_rejected,
        test_nonproper_full_extension_is_rejected,
        test_filter_failure_is_rejected,
        test_predecessor_mismatch_is_rejected,
        test_invalid_window_is_rejected,
        test_pair_validity_does_not_imply_terminal_noncollision,
    ]
    for test in tests:
        test()
    print(f"{len(tests)} segmented-binder schema regressions passed")


if __name__ == "__main__":
    run()
