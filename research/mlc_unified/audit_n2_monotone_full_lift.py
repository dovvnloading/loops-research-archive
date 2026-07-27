"""Finite diagnostics for the N2 monotone full-lift criterion.

The analytic proof is Proposition 4.5 of
kkl_stationary_n2_selected_predecessor_endpoint.md.  These graph
examples test the necessity of its typing assumptions; they do not
prove any analytic or complex-dynamical obligation.
"""

from __future__ import annotations


def components(
    graph: dict[str, set[str]], removed: set[str]
) -> list[frozenset[str]]:
    unseen = set(graph) - removed
    answer: list[frozenset[str]] = []
    while unseen:
        start = next(iter(unseen))
        seen = {start}
        stack = [start]
        while stack:
            vertex = stack.pop()
            for neighbor in graph[vertex]:
                if neighbor in removed or neighbor in seen:
                    continue
                seen.add(neighbor)
                stack.append(neighbor)
        unseen -= seen
        answer.append(frozenset(seen))
    return answer


def fibers(mapping: dict[str, str]) -> dict[str, set[str]]:
    answer: dict[str, set[str]] = {}
    for source, target in mapping.items():
        answer.setdefault(target, set()).add(source)
    return answer


def is_connected(graph: dict[str, set[str]], vertices: set[str]) -> bool:
    if not vertices:
        return False
    start = next(iter(vertices))
    seen = {start}
    stack = [start]
    while stack:
        vertex = stack.pop()
        for neighbor in graph[vertex]:
            if neighbor in vertices and neighbor not in seen:
                seen.add(neighbor)
                stack.append(neighbor)
    return seen == vertices


def assert_monotone(
    graph: dict[str, set[str]], mapping: dict[str, str]
) -> None:
    for point_fiber in fibers(mapping).values():
        assert is_connected(graph, point_fiber)


def run() -> None:
    # Positive control.  The edge x0a--x0b is one connected collapsed
    # fiber over y0.  The selected root y1 has the singleton fiber {x1}.
    # Removing x1 and y1 gives exactly corresponding left/right sides.
    source = {
        "x0a": {"x0b"},
        "x0b": {"x0a", "x1"},
        "x1": {"x0b", "x2"},
        "x2": {"x1"},
    }
    target = {
        "y0": {"y1"},
        "y1": {"y0", "y2"},
        "y2": {"y1"},
    }
    projection = {
        "x0a": "y0",
        "x0b": "y0",
        "x1": "y1",
        "x2": "y2",
    }
    assert_monotone(source, projection)
    assert fibers(projection)["y1"] == {"x1"}

    source_sides = {
        frozenset(projection[x] for x in side)
        for side in components(source, {"x1"})
    }
    target_sides = set(components(target, {"y1"}))
    assert source_sides == target_sides

    model_terminal = {"y2"}
    physical_terminal = {
        x for x, y in projection.items() if y in model_terminal
    }
    marked_continuum = {"x2"}
    assert marked_continuum <= physical_terminal

    # Quotient-level typing control.  The geometric model continuum
    # bar_K={m2,m3} is not a point.  Only the later finite-tree quotient
    # r collapses it to the abstract vertex vK.  The physical K is
    # contained in the full geometric preimage without being a point
    # fiber of pi.
    geometric_source = {
        "s0": {"s1"},
        "s1": {"s0", "s2"},
        "s2": {"s1", "s3"},
        "s3": {"s2", "s4"},
        "s4": {"s3"},
    }
    geometric_model = {
        "m0": {"m1"},
        "m1": {"m0", "m2"},
        "m2": {"m1", "m3"},
        "m3": {"m2"},
    }
    geometric_projection = {
        "s0": "m0",
        "s1": "m1",
        "s2": "m2",
        "s3": "m2",
        "s4": "m3",
    }
    assert_monotone(geometric_source, geometric_projection)
    physical_k = {"s3", "s4"}
    model_k = {"m2", "m3"}
    assert is_connected(geometric_model, model_k)
    selected_model_predecessor = set(model_k)
    selected_physical_predecessor = {
        x
        for x, y in geometric_projection.items()
        if y in selected_model_predecessor
    }
    assert {
        geometric_projection[x] for x in physical_k
    } == model_k
    assert physical_k <= selected_physical_predecessor
    tree_quotient = {"m0": "v0", "m1": "v1", "m2": "vK", "m3": "vK"}
    assert {
        tree_quotient[geometric_projection[x]] for x in physical_k
    } == {"vK"}
    assert len({geometric_projection[x] for x in physical_k}) == 2

    # Failure control 1: a two-to-one fold has disconnected non-root
    # fibers.  A single model side then has two physical sides.
    folded_source = {
        "a": {"r"},
        "r": {"a", "b"},
        "b": {"r"},
    }
    folded_projection = {"a": "tip", "b": "tip", "r": "root"}
    assert not is_connected(
        folded_source, fibers(folded_projection)["tip"]
    )
    assert len(components(folded_source, {"r"})) == 2

    # Failure control 2: even a monotone quotient can have an extra
    # physical side if the selected root is only one point of a
    # non-singleton root fiber.
    thick_root_source = {
        "u": {"v"},
        "v": {"u", "w"},
        "w": {"v"},
    }
    thick_root_projection = {"u": "root", "v": "root", "w": "tip"}
    assert_monotone(thick_root_source, thick_root_projection)
    assert fibers(thick_root_projection)["root"] == {"u", "v"}
    thick_root_sides = set(components(thick_root_source, {"v"}))
    assert thick_root_sides == {
        frozenset({"u"}),
        frozenset({"w"}),
    }

    print("PASS: monotone singleton-root quotient preserves finite-tree sides")
    print("PASS: geometric continuum lift preserves marked containment")
    print("PASS: only the second tree quotient collapses the model continuum")
    print("PASS: nonmonotone fold produces a two-side collision")
    print("PASS: nonsingleton root fiber produces an extra physical side")


if __name__ == "__main__":
    run()
