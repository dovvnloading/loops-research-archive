"""Finite regression tests for the transfer and language counterexamples.

These checks are diagnostic only. Passing them does not prove any uniform analytic
statement or MLC. Their purpose is to prevent already-refuted finite claims from
silently re-entering the manuscripts.
"""

from __future__ import annotations

from cmath import exp as complex_exp
from itertools import permutations, product
from math import exp, isclose, log, pi, sqrt, tanh

from validate_push5_contact_welding_no_go import (
    bypass_certificate,
    circle_atom_certificate,
    pseudoinverse_cutoff_certificate,
    welding_conjugacy_certificate,
)
from audit_stationary_two_occurrence_binder_schema import (
    test_broken_cartesian_synchronization_is_rejected,
    test_endpoint_labels_do_not_erase_homotopy_word,
    test_filter_loss_is_rejected,
    test_independent_stage_parameters_are_rejected,
    test_merged_complete_components_are_rejected,
    test_missing_parent_access_is_rejected,
    test_nonpositive_horizon_is_rejected,
    test_nonproper_core_is_rejected,
    test_unmarked_base_trace_is_rejected,
    test_expanded_route_uses_endpoint_semantics,
    test_terminal_noncollision_is_a_separate_positive_check,
    test_valid_binder_does_not_imply_terminal_noncollision,
)
from audit_stationary_segmented_binder_schema import (
    test_filter_failure_is_rejected as test_segmented_filter_failure_is_rejected,
    test_invalid_window_is_rejected,
    test_missing_full_extension_is_rejected,
    test_nonproper_full_extension_is_rejected,
    test_pair_validity_does_not_imply_terminal_noncollision,
    test_predecessor_mismatch_is_rejected,
    test_proper_window_is_allowed,
    test_valid_nested_chain,
)
from audit_stationary_quantitative_defect_schema import (
    test_degree_two_horizon_radius_and_collar_bound,
    test_disjoint_B_survivors_are_short,
    test_qualitative_positive_modulus_is_not_uniform,
    test_relative_width_cannot_absorb_fixed_constant,
    test_selected_crossing_does_not_equal_all_continuation_failures,
    test_strict_shortness_slack,
    test_terminal_constant_is_admissible_and_charges_vertical_term,
    test_theta_transfers_shortness_and_terminality,
)
from audit_stationary_route_exit_schema import (
    main as run_stationary_route_exit_schema,
)
from audit_stationary_paired_wave_response import (
    main as run_stationary_paired_wave_response,
)
from audit_ledger_tooling_regressions import (
    main as run_ledger_tooling_regressions,
)


Matrix = tuple[tuple[int, ...], ...]


def matmul(left: Matrix, right: Matrix) -> Matrix:
    rows = len(left)
    inner = len(right)
    cols = len(right[0])
    assert len(left[0]) == inner
    return tuple(
        tuple(
            sum(left[i][k] * right[k][j] for k in range(inner))
            for j in range(cols)
        )
        for i in range(rows)
    )


def transpose(matrix: Matrix) -> Matrix:
    return tuple(tuple(matrix[i][j] for i in range(len(matrix))) for j in range(len(matrix[0])))


def support(matrix: Matrix) -> Matrix:
    return tuple(tuple(int(entry > 0) for entry in row) for row in matrix)


def boolean_product(left: Matrix, right: Matrix) -> Matrix:
    rows = len(left)
    inner = len(right)
    cols = len(right[0])
    return tuple(
        tuple(
            int(any(left[i][k] and right[k][j] for k in range(inner)))
            for j in range(cols)
        )
        for i in range(rows)
    )


def spectral_radius_2x2(matrix: Matrix) -> float:
    (a, b), (c, d) = matrix
    trace = a + d
    determinant = a * d - b * c
    discriminant = trace * trace - 4 * determinant
    assert discriminant >= 0
    return max(
        abs((trace + sqrt(discriminant)) / 2),
        abs((trace - sqrt(discriminant)) / 2),
    )


def prefixes(words: set[str]) -> set[str]:
    return {word[:i] for word in words for i in range(len(word) + 1)}


def future(language: set[str], prefix: str) -> frozenset[str]:
    return frozenset(word[len(prefix) :] for word in language if word.startswith(prefix))


def tree_path(
    adjacency: dict[str, set[str]],
    start: str,
    end: str,
) -> tuple[str, ...]:
    """Return the unique vertex path in a finite tree."""
    parent: dict[str, str | None] = {start: None}
    frontier = [start]
    while frontier:
        vertex = frontier.pop()
        if vertex == end:
            break
        for neighbor in adjacency[vertex]:
            if neighbor not in parent:
                parent[neighbor] = vertex
                frontier.append(neighbor)
    assert end in parent
    reverse_path = []
    vertex: str | None = end
    while vertex is not None:
        reverse_path.append(vertex)
        vertex = parent[vertex]
    return tuple(reversed(reverse_path))


def tree_hull(
    adjacency: dict[str, set[str]],
    selected: set[str],
) -> frozenset[str]:
    """Vertex set of the least subtree containing a nonempty package."""
    assert selected
    root = next(iter(selected))
    vertices = {root}
    for target in selected - {root}:
        vertices.update(tree_path(adjacency, root, target))
    return frozenset(vertices)


def test_product_orientation() -> None:
    a = ((0, 0), (1, 1))
    b = ((0, 0), (0, 1))
    c = ((0, 1), (0, 1))
    abc = matmul(matmul(a, b), c)
    cba = matmul(c, matmul(b, a))
    assert abc == ((0, 0), (0, 1))
    assert cba == ((1, 1), (1, 1))
    assert spectral_radius_2x2(abc) == 1
    assert spectral_radius_2x2(cba) == 2


def test_typed_kkl_incidence_and_value_weights() -> None:
    n = ((1, 2), (1, 1))  # raw rows=sources, columns=targets
    b = transpose(n)       # project rows=targets, columns=sources
    assert b == ((1, 1), (2, 1))

    n2 = ((1, 1), (0, 1))
    b2 = transpose(n2)
    assert matmul(b2, b) == transpose(matmul(n, n2))

    eigenvalue = 1 + sqrt(2)
    v = (sqrt(2), 1.0)     # KKL v = project-left
    w = (1.0, sqrt(2))     # KKL w = project-right
    bt_v = (
        b[0][0] * v[0] + b[1][0] * v[1],
        b[0][1] * v[0] + b[1][1] * v[1],
    )
    b_w = (
        b[0][0] * w[0] + b[0][1] * w[1],
        b[1][0] * w[0] + b[1][1] * w[1],
    )
    assert all(isclose(bt_v[i], eigenvalue * v[i]) for i in range(2))
    assert all(isclose(b_w[i], eigenvalue * w[i]) for i in range(2))
    value = (v[0] ** 2 * w[0], v[1] ** 2 * w[1])
    swapped = (w[0] ** 2 * v[0], w[1] ** 2 * v[1])
    assert value != swapped


def test_open_endpoint_gauge() -> None:
    shear = ((1, 1), (0, 1))
    swap = ((0, 1), (1, 0))
    relabeled_target = matmul(swap, shear)
    assert spectral_radius_2x2(shear) == 1
    assert isclose(
        spectral_radius_2x2(relabeled_target),
        (1 + sqrt(5)) / 2,
    )


def test_boolean_support_functor() -> None:
    entries = range(3)
    matrices = [
        ((a, b), (c, d))
        for a, b, c, d in product(entries, repeat=4)
    ]
    for left in matrices:
        for right in matrices:
            assert support(matmul(left, right)) == boolean_product(
                support(left), support(right)
            )


def test_zero_scc_and_extinction_examples() -> None:
    transient = ((1, 0), (0, 0))
    nilpotent = ((0, 1), (0, 0))
    shear = ((1, 1), (0, 1))
    assert spectral_radius_2x2(transient) == 1
    assert matmul(nilpotent, nilpotent) == ((0, 0), (0, 0))
    assert matmul(shear, shear) == ((1, 2), (0, 1))


def test_future_index_obstructions() -> None:
    for m in range(1, 7):
        binary_words = {"".join(bits) for bits in product("01", repeat=m)}
        copy_language = prefixes({f"{word}#{word}" for word in binary_words})
        residuals = {future(copy_language, word) for word in binary_words}
        assert len(residuals) == 2**m

        exact_exit = prefixes({"a" * m + "b"})
        exit_residuals = {
            future(exact_exit, "a" * i)
            for i in range(m + 1)
        }
        assert len(exit_residuals) == m + 1


def test_counter_fiber_is_not_global_invariance() -> None:
    predicate = lambda value: value in {0, 1}
    start = 0
    loop_increment = 1
    continuation_increment = 0
    assert predicate(start + continuation_increment)
    assert predicate(start + loop_increment + continuation_increment)
    assert predicate(1) != predicate(2)


def test_memory_projection_does_not_license_pumping() -> None:
    for m in range(2, 8):
        exact_exit = prefixes({"a" * m + "b"})
        # A one-state projection repeats after every a, but deleting any positive
        # number of a's changes the sole admissible b-exit time.
        for deleted in range(1, m + 1):
            assert "a" * (m - deleted) + "b" not in exact_exit


def test_wad_output_is_not_transport_compatibility() -> None:
    # P=(1,1), R=diag(1,2). Equal compressed inputs can have unequal compressed
    # successors even when every declared terminal output is identically zero.
    z1 = (1, 0)
    z2 = (0, 1)
    assert sum(z1) == sum(z2)
    p_r_z1 = z1[0] + 2 * z1[1]
    p_r_z2 = z2[0] + 2 * z2[1]
    assert p_r_z1 != p_r_z2


def test_signature_count_does_not_bound_dimension() -> None:
    # One state and one identity-loop signature exist in every dimension.
    for dimension in range(1, 12):
        identity = tuple(
            tuple(int(i == j) for j in range(dimension))
            for i in range(dimension)
        )
        assert len({("one-state", "identity-loop")}) == 1
        assert len(identity) == dimension


def test_corrected_clone_exponent_and_multiplier() -> None:
    # For the audited three-vertex base graph, the literal clone Perron root obeys
    # lambda^(n+3)=lambda+1. The source's +k reduced equation fails, while the
    # independently proved literal-clone reduction uses the exact -k equation.
    for n in range(1, 21):
        lo, hi = 1.0, 2.0
        for _ in range(100):
            lam = (lo + hi) / 2
            if lam ** (n + 3) - lam - 1 < 0:
                lo = lam
            else:
                hi = lam
        lam = (lo + hi) / 2
        assert isclose(lam ** (n + 3), lam + 1, rel_tol=1e-12)
        h_plus = lam**2 + lam**3
        h_minus = lam**-2 + lam**-3
        assert not isclose(h_plus, lam**n, rel_tol=1e-8)
        assert isclose(h_minus, lam**n, rel_tol=1e-10)
        # Here the gate dimension is one, rho(R)=2, and K=3.
        assert lam**n >= 2 ** (n / (n + 3))
        if n > 3:
            assert lam**n > sqrt(2)


def test_virtual_limb_tree_bound() -> None:
    # Exhaust all labelled reduced anchored trees through seven vertices.
    # This is a finite regression for the exact handshaking proof, not a
    # substitute for the open analytic construction of the virtual carrier.
    saw_sharp_anchor_charge = False
    for vertex_count in range(2, 8):
        for prufer in product(range(vertex_count), repeat=vertex_count - 2):
            degrees = [1] * vertex_count
            for vertex in prufer:
                degrees[vertex] += 1

            for marked_mask in range(1, 1 << vertex_count, 2):
                marked = {
                    vertex
                    for vertex in range(vertex_count)
                    if marked_mask & (1 << vertex)
                }
                m = len(marked) - 1  # vertex 0 is the anchor
                if m < 1:
                    continue
                if any(degrees[v] == 1 and v not in marked for v in range(vertex_count)):
                    continue
                if any(degrees[v] < 3 and v not in marked for v in range(vertex_count)):
                    continue

                unmarked_count = vertex_count - len(marked)
                edge_count = vertex_count - 1
                assert unmarked_count <= m - 1
                assert edge_count <= 2 * m - 1

                # Two oriented sides per edge and up to two local ideal sides
                # at every prescribed vertex, including the anchor.
                complete_marking_count = 2 * edge_count + 2 * len(marked)
                assert complete_marking_count <= 6 * m
                saw_sharp_anchor_charge |= complete_marking_count == 6 * m

    assert saw_sharp_anchor_charge


def test_branch_parameter_mismatch() -> None:
    # Static alternatives at every parameter plus branch implications at two
    # unrelated parameters need not produce amplification.
    parameters = range(1, 7)
    tame_input = 2
    wave_input = 5
    amplification = {parameter: False for parameter in parameters}
    tame = {parameter: parameter != tame_input for parameter in parameters}
    wave = {parameter: parameter == tame_input for parameter in parameters}
    assert not tame[tame_input]       # tame closure is vacuous
    assert not wave[wave_input]       # wave closure is vacuous
    assert all(
        amplification[p] or tame[p] or wave[p]
        for p in parameters
    )
    assert not any(amplification.values())


def test_dyadic_fast_forward_fan_degree() -> None:
    # A selected branch with m quadratic encounters has degree 2^m.
    # One branch for each m=0,...,M therefore has total degree
    # 2^(M+1)-1, strictly below KKL's safe 2^(M+1) bound.
    for terminal_depth in range(0, 13):
        branch_degrees = [
            2 ** sum(critical_word)
            for critical_word in (
                (1,) * encounters + (0,) * (terminal_depth - encounters)
                for encounters in range(terminal_depth + 1)
            )
        ]
        assert branch_degrees == [
            2**encounters for encounters in range(terminal_depth + 1)
        ]
        assert sum(branch_degrees) == 2 ** (terminal_depth + 1) - 1
        assert sum(branch_degrees) < 2 ** (terminal_depth + 1)


def test_endpoint_birth_accounting() -> None:
    # Exhaust small degree-one/quadratic strings and genuine endpoint births.
    for horizon in range(1, 7):
        for degrees in product((1, 2), repeat=horizon):
            for births in product(range(3), repeat=horizon):
                for terminal_count in range(4):
                    recursive_count = terminal_count
                    for degree, birth in reversed(tuple(zip(degrees, births))):
                        recursive_count = degree * recursive_count + birth

                    total_degree = 1
                    for degree in degrees:
                        total_degree *= degree
                    weighted_births = 0
                    prefix_degree = 1
                    for degree, birth in zip(degrees, births):
                        weighted_births += prefix_degree * birth
                        prefix_degree *= degree

                    assert recursive_count == (
                        total_degree * terminal_count + weighted_births
                    )

    # One new endpoint per degree-one corridor stage accumulates linearly.
    for horizon in range(1, 50):
        terminal_count = 3
        assert terminal_count + sum([1] * horizon) == terminal_count + horizon


def test_attachment_support_reduction() -> None:
    # Empty attachment support in a long degree-one interior must make the
    # weighted charge depend only on the bounded terminal defect window.
    for horizon in range(1, 25):
        for window in range(0, min(6, horizon) + 1):
            interior = horizon - window
            for terminal_degrees in product((1, 2), repeat=window):
                degrees = (1,) * interior + terminal_degrees
                for birth_cap in range(4):
                    births = (0,) * interior + (birth_cap,) * window
                    prefix_degree = 1
                    weighted_births = 0
                    for degree, birth in zip(degrees, births):
                        weighted_births += prefix_degree * birth
                        prefix_degree *= degree
                    assert weighted_births <= birth_cap * (2**window - 1)

    # One hidden attachment at each central stage defeats period independence.
    for horizon in range(1, 50):
        degrees = (1,) * horizon
        births = (1,) * horizon
        prefix_degree = 1
        weighted_births = 0
        for degree, birth in zip(degrees, births):
            weighted_births += prefix_degree * birth
            prefix_degree *= degree
        assert weighted_births == horizon


def test_corridor_attachment_transport() -> None:
    # A marked-pair natural transition acts by a bijection on the finite
    # interval model, so support cardinality and emptiness are invariant.
    interval_count = 7
    for horizon in range(1, 25):
        for support_mask in range(1 << interval_count):
            support = {
                interval
                for interval in range(interval_count)
                if support_mask & (1 << interval)
            }
            anchor_support = set(support)
            for stage in range(horizon):
                shift = (2 * stage + 1) % interval_count
                transported = {
                    (interval + shift) % interval_count
                    for interval in support
                }
                assert len(transported) == len(support)
                assert (not transported) == (not support)
                support = transported

            # If every persistent attachment exposes one genuine endpoint,
            # its degree-one birth charge is at least the corridor length.
            if anchor_support:
                birth_charge = horizon * len(anchor_support)
                assert birth_charge >= horizon

    # Carrier-only label preservation is insufficient when attachment
    # incidence is not respected by the ambient/prime-end map.
    carrier_map = {"a": "a", "b": "b"}
    ambient_map = {"a": "a", "b": "b", "x": "x"}
    source_attachment = {"x": "a"}
    target_attachment = {"x": "b"}
    assert all(ambient_map[vertex] == carrier_map[vertex] for vertex in carrier_map)
    transported_source = {
        ambient_map[branch]: carrier_map[interval]
        for branch, interval in source_attachment.items()
    }
    assert transported_source != target_attachment


def test_univalent_pair_transport_certificate() -> None:
    # A finite ribbon model of one anchor pair is transported by bijections.
    # The same permutation must act on the ambient carrier, embedded carrier,
    # packages, obstacles, and cyclic access marking.
    ambient = {0, 1, 2, 3, 4, 5}
    carrier = {0, 1, 2, 3}
    packages = {0, 2}
    obstacles = {4, 5}
    cyclic_marking = (0, 1, 2, 3)

    for shift in range(len(ambient)):
        transport = {cell: (cell + shift) % len(ambient) for cell in ambient}
        next_ambient = {transport[cell] for cell in ambient}
        next_carrier = {transport[cell] for cell in carrier}
        next_packages = {transport[cell] for cell in packages}
        next_obstacles = {transport[cell] for cell in obstacles}
        next_marking = tuple(transport[cell] for cell in cyclic_marking)

        assert next_carrier <= next_ambient
        assert next_packages <= next_carrier
        assert next_obstacles.isdisjoint(next_carrier)
        assert len(next_marking) == len(set(next_marking))
        assert next_marking == tuple(
            (cell + shift) % len(ambient) for cell in cyclic_marking
        )


def test_attachment_free_anchor_underdetermination() -> None:
    # The interval and triod contain the same endpoint package and carry the
    # same identity dynamics on the selected interval, but they are not
    # homeomorphic: only the triod has a valence-three point.
    interval_edges = {("a", "m"), ("m", "b")}
    triod_edges = interval_edges | {("m", "x")}
    package = {"a", "b"}

    def degrees(edges: set[tuple[str, str]]) -> dict[str, int]:
        result: dict[str, int] = {}
        for left, right in edges:
            result[left] = result.get(left, 0) + 1
            result[right] = result.get(right, 0) + 1
        return result

    interval_degrees = degrees(interval_edges)
    triod_degrees = degrees(triod_edges)
    assert package <= set(interval_degrees)
    assert package <= set(triod_degrees)
    assert max(interval_degrees.values()) == 2
    assert max(triod_degrees.values()) == 3
    assert sorted(interval_degrees.values()) != sorted(triod_degrees.values())


def test_finite_attachment_orbit_closure() -> None:
    def least_closure(
        start: set[int], implications: dict[int, set[int]]
    ) -> set[int]:
        current = set(start)
        while True:
            successor = current | {
                target
                for source in current
                for target in implications.get(source, set())
            }
            if successor == current:
                return current
            assert len(successor) > len(current)
            current = successor

    for cell_count in range(1, 9):
        implications = {
            cell: {
                target
                for target in range(cell_count)
                if target == cell + 1 or (cell % 2 == 0 and target == cell + 2)
            }
            for cell in range(cell_count)
        }
        implications = {
            cell: {target for target in targets if target < cell_count}
            for cell, targets in implications.items()
        }
        closure = least_closure({0}, implications)
        assert 0 in closure
        assert least_closure(closure, implications) == closure

        # Every fixed point containing the seed contains the least closure.
        full = set(range(cell_count))
        assert least_closure(full, implications) == full
        assert closure <= full

        # Conjugating the completion rule by a permutation transports closure.
        permutation = {cell: cell_count - 1 - cell for cell in range(cell_count)}
        conjugate_implications = {
            permutation[source]: {permutation[target] for target in targets}
            for source, targets in implications.items()
        }
        conjugate_closure = least_closure(
            {permutation[0]}, conjugate_implications
        )
        assert conjugate_closure == {permutation[cell] for cell in closure}

    # A collision in the least closure cannot be removed by further monotone
    # absorption.
    collision_implications = {0: {1}, 1: {2}, 2: set()}
    collision_closure = least_closure({0}, collision_implications)
    forbidden_sheet_cell = 2
    assert forbidden_sheet_cell in collision_closure
    assert forbidden_sheet_cell in least_closure(
        collision_closure | {3}, collision_implications
    )


def test_no_least_connected_carrier() -> None:
    # Two distinct connector choices share only the disconnected package.
    # This finite ribbon model diagnoses the exact inclusion argument in
    # Theorem 5.1; it is not a substitute for its planar proof.
    upper_edges = {("a", "u"), ("u", "b")}
    lower_edges = {("a", "l"), ("l", "b")}
    package = {"a", "b"}

    def vertices(edges: set[tuple[str, str]]) -> set[str]:
        return {vertex for edge in edges for vertex in edge}

    def connected(
        selected_vertices: set[str], edges: set[tuple[str, str]]
    ) -> bool:
        if not selected_vertices:
            return False
        reached = {next(iter(selected_vertices))}
        while True:
            successor = reached | {
                right
                for left, right in edges
                if left in reached and right in selected_vertices
            } | {
                left
                for left, right in edges
                if right in reached and left in selected_vertices
            }
            if successor == reached:
                return reached == selected_vertices
            reached = successor

    assert package <= vertices(upper_edges)
    assert package <= vertices(lower_edges)
    assert connected(vertices(upper_edges), upper_edges)
    assert connected(vertices(lower_edges), lower_edges)
    common_vertices = vertices(upper_edges) & vertices(lower_edges)
    common_edges = upper_edges & lower_edges
    assert common_vertices == package
    assert not common_edges
    assert not connected(common_vertices, common_edges)


def test_protected_access_collision() -> None:
    # Absorbing the first half-disk excess forces an access-erasing cell.
    # Further monotone absorption cannot remove the collision.
    implications = {
        "interval": {"upper_half_disk"},
        "upper_half_disk": set(),
        "later_cell": set(),
    }

    def closure(start: set[str]) -> set[str]:
        current = set(start)
        while True:
            successor = current | {
                target
                for source in current
                for target in implications.get(source, set())
            }
            if successor == current:
                return current
            current = successor

    protected_access = "upper_midpoint"
    access_destroyers = {"upper_half_disk": {protected_access}}
    least = closure({"interval"})
    destroyed = {
        access
        for cell in least
        for access in access_destroyers.get(cell, set())
    }
    assert least == {"interval", "upper_half_disk"}
    assert destroyed == {protected_access}

    enlarged = closure(least | {"later_cell"})
    enlarged_destroyed = {
        access
        for cell in enlarged
        for access in access_destroyers.get(cell, set())
    }
    assert protected_access in enlarged_destroyed


def test_quadratic_univalent_corridor_model() -> None:
    # Diagnostic sampling of the exact model f(z)=z^2 on
    # U^- = D(3/2,1), which lies in Re(z)>1/2.
    center = 1.5 + 0j
    radius = 1.0
    # Use an explicit rational grid to avoid trigonometric roundoff in the
    # injectivity check.
    samples = [
        complex(real, imag)
        for real in (0.75, 1.0, 1.5, 2.0, 2.25)
        for imag in (-0.5, -0.25, 0.0, 0.25, 0.5)
        if abs(complex(real, imag) - center) < radius
    ]
    assert samples
    assert all(point.real > 0.5 for point in samples)
    assert all(2 * point != 0 for point in samples)
    images = [point * point for point in samples]
    assert len(images) == len(set(images))

    # The protected vertical access at m=3/2 enters the absorbed half-disk
    # for every sufficiently short positive segment.
    midpoint = 1.5
    for height in (0.1, 0.2, 0.4):
        point = complex(midpoint, height)
        assert abs(point - center) <= 0.5
        assert point.imag >= 0


def test_uptcr_record_threshold() -> None:
    # Diagnostic arithmetic form of the record contradiction:
    # if L > E0/(lambda-1), then lambda*L-E0 > L.
    for numerator, denominator in ((3, 2), (2, 1), (5, 2)):
        assert numerator > denominator
        for error in range(9):
            for threshold in range(7):
                for value in range(1, 80):
                    above_error_threshold = (
                        (numerator - denominator) * value
                        > error * denominator
                    )
                    if value > threshold and above_error_threshold:
                        predecessor_numerator = numerator * value - error * denominator
                        assert predecessor_numerator > denominator * value


def test_uptcr_six_clause_gate() -> None:
    # No proper subset of the named clauses is allowed to set the UPTCR gate.
    required = frozenset(
        {
            "protected_carrier",
            "analytic_realization",
            "finite_response",
            "backward_transition",
            "marked_compactness",
            "tower_rigidity",
        }
    )

    def closes_uptcr(proved: frozenset[str]) -> bool:
        return required <= proved

    assert closes_uptcr(required)
    for clause in required:
        assert not closes_uptcr(required - {clause})


def test_uptcr_parameter_basis_gate() -> None:
    # A singleton fiber is not a connected relative-neighborhood basis unless
    # every additional topological clause is present.
    required = frozenset(
        {
            "nested",
            "nonempty_compact",
            "connected",
            "relative_neighborhood",
            "intersection_is_full_fiber",
            "fiber_is_singleton",
        }
    )

    def licenses_local_connectivity(certificate: frozenset[str]) -> bool:
        return required <= certificate

    assert licenses_local_connectivity(required)
    for clause in required:
        assert not licenses_local_connectivity(required - {clause})

    diameters = [2.0 / (index + 1) for index in range(1, 101)]
    assert all(later < earlier for earlier, later in zip(diameters, diameters[1:]))
    assert diameters[-1] < 0.02


def test_uptcr_spine_fan_degree_quantifier() -> None:
    # Exactly one quadratic stage belongs to the selected return spine, not
    # to every auxiliary Wave branch.
    spine_stage_degrees = (1, 1, 2, 1, 1)
    assert spine_stage_degrees.count(2) == 1

    terminal_depth = 4
    auxiliary_branch_degrees = {
        critical_count: 2**critical_count
        for critical_count in range(terminal_depth + 1)
    }
    assert auxiliary_branch_degrees[0] == 1
    assert auxiliary_branch_degrees[1] == 2
    assert auxiliary_branch_degrees[terminal_depth] == 16
    assert max(auxiliary_branch_degrees.values()) > 2


def test_uptcr_fatal_collision_is_not_window_charge() -> None:
    coordinates = ("sheet", "critical", "obstacle", "access", "localization")

    def protected_core_is_admissible(collision: dict[str, bool]) -> bool:
        return not any(collision[coordinate] for coordinate in coordinates)

    zero = {coordinate: False for coordinate in coordinates}
    raw_window_defect = dict(zero)
    raw_window_defect["access"] = True

    assert protected_core_is_admissible(zero)
    assert not protected_core_is_admissible(raw_window_defect)

    # A replacement model may be charged only after the fatal coordinate is
    # actually resolved, not because the raw model was assigned to a window.
    replacement = dict(zero)
    assert protected_core_is_admissible(replacement)


def test_uptcr_block_routes_are_inclusive() -> None:
    routes = ("entropy", "pseudo_siegel", "transient_shear")

    def has_certified_route(certified: set[str]) -> bool:
        return any(route in certified for route in routes)

    overlapping = {"entropy", "pseudo_siegel"}
    assert has_certified_route(overlapping)
    assert len(overlapping) == 2

    priority = {route: index for index, route in enumerate(routes)}
    selected = min(overlapping, key=priority.__getitem__)
    assert selected == "entropy"


def ribbon_boundary_cycle(
    rotation: dict[str, tuple[str, ...]],
    start: tuple[str, str],
) -> tuple[tuple[str, str], ...]:
    """Return the oriented boundary walk of a finite ribbon tree."""
    directed_edge_count = sum(len(neighbors) for neighbors in rotation.values())
    current = start
    cycle: list[tuple[str, str]] = []
    for _ in range(directed_edge_count):
        assert current not in cycle
        cycle.append(current)
        source, target = current
        neighbors = rotation[target]
        source_index = neighbors.index(source)
        successor = neighbors[(source_index + 1) % len(neighbors)]
        current = (target, successor)
    assert current == start
    return tuple(cycle)


def cyclically_equal(left: tuple[object, ...], right: tuple[object, ...]) -> bool:
    if len(left) != len(right):
        return False
    return any(left == right[index:] + right[:index] for index in range(len(right)))


def test_protected_ribbon_boundary_naturality() -> None:
    rotation = {
        "center": ("a", "b", "d"),
        "a": ("center",),
        "b": ("center",),
        "d": ("center",),
    }
    boundary = ribbon_boundary_cycle(rotation, ("a", "center"))
    assert len(boundary) == 6
    assert set(boundary) == {
        ("center", "a"),
        ("a", "center"),
        ("center", "b"),
        ("b", "center"),
        ("center", "d"),
        ("d", "center"),
    }

    rename = {"center": "c2", "a": "x", "b": "y", "d": "z"}
    transported_rotation = {
        rename[vertex]: tuple(rename[neighbor] for neighbor in neighbors)
        for vertex, neighbors in rotation.items()
    }
    transported_boundary = ribbon_boundary_cycle(
        transported_rotation,
        (rename["a"], rename["center"]),
    )
    expected = tuple((rename[u], rename[v]) for u, v in boundary)
    assert transported_boundary == expected

    reversed_rotation = dict(transported_rotation)
    reversed_rotation["c2"] = tuple(reversed(reversed_rotation["c2"]))
    reversed_boundary = ribbon_boundary_cycle(
        reversed_rotation,
        (rename["a"], rename["center"]),
    )
    assert not cyclically_equal(expected, reversed_boundary)


def test_protected_connector_trace_gate() -> None:
    def admissible_trace(
        attachment_trace: frozenset[str],
        enters_protected_collar: bool,
    ) -> bool:
        return len(attachment_trace) == 1 and not enters_protected_collar

    assert admissible_trace(frozenset({"free_port"}), False)
    assert not admissible_trace(
        frozenset({"left", "midpoint", "right"}),
        True,
    )
    assert not admissible_trace(frozenset({"port_a", "port_b"}), False)
    assert not admissible_trace(frozenset({"free_port"}), True)


def test_protected_connector_side_bound() -> None:
    # After suppressing degree-two vertices and unlabeled leaves, a tree with
    # s labeled atom leaves has E <= 2s-3 and at most 2E oriented sides.
    for leaves in range(2, 20):
        maximal_edges = 2 * leaves - 3
        maximal_sides = 2 * maximal_edges
        star_edges = 1 if leaves == 2 else leaves
        assert star_edges <= maximal_edges
        assert 2 * star_edges <= maximal_sides


def test_protected_free_component_criterion() -> None:
    # A finite cell graph models components of the free routing domain.
    # This is diagnostic only; the analytic theorem uses planar components
    # and explicit singleton port arcs.
    adjacency = {
        "left_port": {"upper", "lower"},
        "upper": {"left_port", "collar", "right_port"},
        "collar": {"upper", "right_port"},
        "lower": {"left_port", "right_port"},
        "right_port": {"upper", "collar", "lower"},
    }

    def component(start: str, forbidden: set[str]) -> set[str]:
        if start in forbidden:
            return set()
        reached = {start}
        while True:
            successor = reached | {
                neighbor
                for vertex in reached
                for neighbor in adjacency[vertex]
                if neighbor not in forbidden
            }
            if successor == reached:
                return reached
            reached = successor

    # The protected upper collar is forbidden, but the lower route supplies
    # one common free component and hence a connector.
    assert "right_port" in component("left_port", {"collar", "upper"})

    # If both possible routes are protected or separated, the ports occupy
    # distinct components and no monotone connector can avoid the forbidden
    # set.
    assert "right_port" not in component(
        "left_port",
        {"collar", "upper", "lower"},
    )


def test_late_forbidden_insertion_splits_free_component() -> None:
    adjacency = {
        "left_port": {"bridge"},
        "bridge": {"left_port", "right_port"},
        "right_port": {"bridge"},
    }

    def connected(forbidden: set[str]) -> bool:
        reached = {"left_port"}
        while True:
            successor = reached | {
                neighbor
                for vertex in reached
                for neighbor in adjacency[vertex]
                if neighbor not in forbidden
            }
            if successor == reached:
                return "right_port" in reached
            reached = successor

    assert connected(set())
    # A collar or late root-shadow exclusion inserted after routing was
    # selected can destroy the certificate.
    assert not connected({"bridge"})


def test_augmented_atom_common_domain() -> None:
    # Finite square-cell diagnostic for Theorem 4.3 of
    # virtual_common_free_component.md.  The forbidden packets are filled,
    # pairwise disjoint cell disks away from the localization boundary.
    # Passing this test does not prove the planar theorem, which uses
    # compacta Alexander duality.
    cells = {
        (x, y)
        for x in range(-8, 9)
        for y in range(-8, 9)
    }
    first_packet = {
        (x, y)
        for x in range(-5, -2)
        for y in range(-1, 2)
    }
    second_packet = {
        (x, y)
        for x in range(3, 6)
        for y in range(-1, 2)
    }
    obstacle = {
        (x, y)
        for x in range(-1, 2)
        for y in range(4, 7)
    }
    forbidden = first_packet | second_packet | obstacle
    free = cells - forbidden

    def neighbors(cell: tuple[int, int]) -> set[tuple[int, int]]:
        x, y = cell
        return {
            candidate
            for candidate in (
                (x - 1, y),
                (x + 1, y),
                (x, y - 1),
                (x, y + 1),
            )
            if candidate in free
        }

    start = (-2, 0)
    reached = {start}
    while True:
        successor = reached | {
            neighbor
            for cell in reached
            for neighbor in neighbors(cell)
        }
        if successor == reached:
            break
        reached = successor

    first_port = (-2, 0)
    second_port = (2, 0)
    obstacle_side = (2, 5)
    assert first_port in reached
    assert second_port in reached
    assert obstacle_side in reached
    assert reached == free


def test_annular_obstacle_collision_audit() -> None:
    # A square annulus is the finite-cell version of Proposition 7.1.
    # It separates an inner atom from an outer atom.  Fullifying the annulus
    # either collides with the inner atom or, when assigned to that atom,
    # makes the original atom interior and destroys its singleton port.
    cells = {
        (x, y)
        for x in range(-9, 10)
        for y in range(-9, 10)
    }
    inner_atom = {
        (x, y)
        for x in range(-1, 2)
        for y in range(-1, 2)
    }
    outer_atom = {
        (x, y)
        for x in range(6, 8)
        for y in range(-1, 2)
    }
    annulus = {
        (x, y)
        for x, y in cells
        if 3 <= max(abs(x), abs(y)) <= 4
    }
    forbidden = inner_atom | outer_atom | annulus
    free = cells - forbidden

    def component(start: tuple[int, int]) -> set[tuple[int, int]]:
        reached = {start}
        while True:
            successor = reached | {
                candidate
                for x, y in reached
                for candidate in (
                    (x - 1, y),
                    (x + 1, y),
                    (x, y - 1),
                    (x, y + 1),
                )
                if candidate in free
            }
            if successor == reached:
                return reached
            reached = successor

    inner_port = (2, 0)
    outer_port = (5, 0)
    assert outer_port not in component(inner_port)

    filled_annulus = {
        (x, y)
        for x, y in cells
        if max(abs(x), abs(y)) <= 4
    }
    assert filled_annulus & inner_atom

    boundary_of_filled_annulus = {
        (x, y)
        for x, y in filled_annulus
        if max(abs(x), abs(y)) == 4
    }
    assert inner_atom.isdisjoint(boundary_of_filled_annulus)

    collision = {
        "coverage": False,
        "connected_seed": False,
        "merge": bool(filled_annulus & inner_atom),
        "localization": False,
        "port": inner_atom.isdisjoint(boundary_of_filled_annulus),
    }
    assert collision["merge"]
    assert collision["port"]


def test_augmented_packet_closure_order_independence() -> None:
    # Finite-cell diagnostic for the absorption identity in the fixed-packet
    # closure audit.  It checks every order of four pieces whose union is a
    # square annulus.  This does not prove the continuum theorem.
    universe = {
        (x, y)
        for x in range(-8, 9)
        for y in range(-8, 9)
    }

    def cell_fill(seed: set[tuple[int, int]]) -> set[tuple[int, int]]:
        free = universe - seed
        boundary = {
            (x, y)
            for x, y in free
            if abs(x) == 8 or abs(y) == 8
        }
        exterior = set(boundary)
        while True:
            successor = exterior | {
                candidate
                for x, y in exterior
                for candidate in (
                    (x - 1, y),
                    (x + 1, y),
                    (x, y - 1),
                    (x, y + 1),
                )
                if candidate in free
            }
            if successor == exterior:
                return universe - exterior
            exterior = successor

    top = {(x, 4) for x in range(-4, 5)}
    bottom = {(x, -4) for x in range(-4, 5)}
    left = {(-4, y) for y in range(-4, 5)}
    right = {(4, y) for y in range(-4, 5)}
    pieces = (top, bottom, left, right)
    expected = cell_fill(set().union(*pieces))
    assert (0, 0) in expected

    for order in permutations(pieces):
        current: set[tuple[int, int]] = set()
        for piece in order:
            current = cell_fill(current | piece)
        assert current == expected

    # Discrete absorption: fill(fill(K) union L)=fill(K union L).
    k = top | left | bottom
    assert cell_fill(cell_fill(k) | right) == cell_fill(k | right)


def test_augmented_packet_collision_and_port_persistence() -> None:
    # A finite-cell diagnostic for monotone persistence.  The analytic proof
    # is the monotonicity of planar Fill and inclusion of admissible arc
    # families.
    universe = {
        (x, y)
        for x in range(-9, 10)
        for y in range(-9, 10)
    }

    def cell_fill(seed: set[tuple[int, int]]) -> set[tuple[int, int]]:
        free = universe - seed
        exterior = {
            (x, y)
            for x, y in free
            if abs(x) == 9 or abs(y) == 9
        }
        while True:
            successor = exterior | {
                candidate
                for x, y in exterior
                for candidate in (
                    (x - 1, y),
                    (x + 1, y),
                    (x, y - 1),
                    (x, y + 1),
                )
                if candidate in free
            }
            if successor == exterior:
                return universe - exterior
            exterior = successor

    atom = {
        (x, y)
        for x in range(-1, 2)
        for y in range(-1, 2)
    }
    ring = {
        (x, y)
        for x, y in universe
        if max(abs(x), abs(y)) == 4
    }
    filled_ring = cell_fill(ring)
    assert filled_ring & atom

    enlarged_ring = ring | {(5, 0), (6, 0)}
    enlarged_atom = atom | {(2, 0)}
    assert filled_ring <= cell_fill(enlarged_ring)
    assert cell_fill(enlarged_ring) & enlarged_atom

    # Connect the atom to its surrounding ring and fill.  The seed is now
    # connected, but the original atom is strictly interior to the completed
    # packet and has no cell-side exposure.  Enlargement does not restore it.
    bridge = {(x, 0) for x in range(2, 5)}
    packet = cell_fill(atom | bridge | ring)
    packet_boundary = {
        (x, y)
        for x, y in packet
        if any(
            neighbor in universe - packet
            for neighbor in (
                (x - 1, y),
                (x + 1, y),
                (x, y - 1),
                (x, y + 1),
            )
        )
    }
    assert atom.isdisjoint(packet_boundary)

    enlarged_packet = cell_fill(packet | {(5, 0), (6, 0)})
    enlarged_boundary = {
        (x, y)
        for x, y in enlarged_packet
        if any(
            neighbor in universe - enlarged_packet
            for neighbor in (
                (x - 1, y),
                (x + 1, y),
                (x, y - 1),
                (x, y + 1),
            )
        )
    }
    assert atom.isdisjoint(enlarged_boundary)


def test_individual_ports_localize_disjointly() -> None:
    # Individual cell ports may be represented by long crossing trial paths,
    # but each has a one-cell initial segment in a disjoint packet
    # neighborhood.  This mirrors Lemma 5.2; it is diagnostic only.
    first_packet = {
        (x, y)
        for x in range(-5, -2)
        for y in range(-1, 2)
    }
    second_packet = {
        (x, y)
        for x in range(3, 6)
        for y in range(-1, 2)
    }
    first_endpoint, first_free = (-3, 0), (-2, 0)
    second_endpoint, second_free = (3, 0), (2, 0)
    assert first_endpoint in first_packet
    assert first_free not in first_packet | second_packet
    assert second_endpoint in second_packet
    assert second_free not in first_packet | second_packet
    first_local_port = {first_endpoint, first_free}
    second_local_port = {second_endpoint, second_free}
    assert first_local_port.isdisjoint(second_local_port)


def test_horizon_first_inventory_extension() -> None:
    # Finite dependency-graph diagnostic for Theorem 4.1 of the VAAPC-I
    # source audit.  An edge x -> y means that retaining x forces y.
    def closure(
        seeds: set[str], edges: set[tuple[str, str]]
    ) -> set[str]:
        result = set(seeds)
        while True:
            successor = result | {
                target
                for source, target in edges
                if source in result
            }
            if successor == result:
                return result
            result = successor

    old_universe = {"a", "b"}
    old_inventory = closure({"a"}, set())
    assert old_inventory == {"a"}

    extended_universe = old_universe | {"c"}
    extended_inventory = closure({"a", "c"}, {("c", "b")})
    assert extended_inventory == {"a", "b", "c"}
    assert extended_inventory & old_universe == {"a", "b"}
    assert extended_inventory & old_universe != old_inventory
    assert extended_universe >= extended_inventory


def test_horizon_slice_stability_criterion() -> None:
    # The old slice is stable precisely when no extended seed reaches an
    # omitted old record.  This checks positive and negative finite models;
    # it is not an analytic virtual-horizon construction.
    def reachable(
        seeds: set[str], edges: set[tuple[str, str]]
    ) -> set[str]:
        result = set(seeds)
        changed = True
        while changed:
            changed = False
            for source, target in edges:
                if source in result and target not in result:
                    result.add(target)
                    changed = True
        return result

    old_universe = {"root", "latent"}
    old_inventory = reachable({"root"}, set())
    stable = reachable(
        {"root", "terminal"},
        {("terminal", "new_only")},
    )
    assert stable & old_universe == old_inventory

    unstable = reachable(
        {"root", "terminal"},
        {("terminal", "new_only"), ("new_only", "latent")},
    )
    assert "latent" in unstable & old_universe
    assert unstable & old_universe != old_inventory


def test_inventory_graph_does_not_choose_packet_labels() -> None:
    # The same unlabelled dependency graph admits different label data.
    # Actual attachment geometry must select between them.
    vertices = {"x", "y"}
    edges: set[tuple[str, str]] = set()
    separated = {"x": "atom-1", "y": "obstacle-1"}
    absorbed = {"x": "atom-1", "y": "atom-1"}
    assert vertices == set(separated) == set(absorbed)
    assert edges == set()
    assert separated != absorbed


def test_kkl_native_visit_stopping_index() -> None:
    # If no chain of N waves linked by critical visits exists, then starting
    # from A_1 there can be at most N-2 successful successor selections.
    # The next theorem call must take its terminal alternative.  This is an
    # off-by-one diagnostic for Proposition 4.1; it does not prove KKL's
    # analytic bounded-visits lemma.
    parabolic_bound = 3
    forbidden_wave_count = 216 * parabolic_bound**2
    maximal_successful_relations = forbidden_wave_count - 2
    resulting_wave_count = 1 + maximal_successful_relations
    assert resulting_wave_count == forbidden_wave_count - 1
    assert resulting_wave_count < forbidden_wave_count
    assert 1 + (maximal_successful_relations + 1) == forbidden_wave_count


def test_resolved_wave_program_maximal_iterate_horizon() -> None:
    # A finite decision DAG carries exact iterate lengths.  Its dynamical
    # horizon is the largest path sum, not the number of theorem calls.
    edges = {
        "start": [("short", 1), ("terminal-a", 2)],
        "short": [("visit", 7), ("terminal-b", 3)],
        "visit": [("terminal-c", 5)],
        "terminal-a": [],
        "terminal-b": [],
        "terminal-c": [],
    }

    def path_sums(vertex: str, total: int = 0) -> list[int]:
        if not edges[vertex]:
            return [total]
        return [
            horizon
            for successor, span in edges[vertex]
            for horizon in path_sums(successor, total + span)
        ]

    assert sorted(path_sums("start")) == [2, 4, 13]
    assert max(path_sums("start")) == 13


def test_wave_final_root_closure_order_independence() -> None:
    # Each implication is one root/attachment/access dependency.  Every fair
    # processing order reaches the same least fixed point.  This finite
    # model tests the algorithm only, not an analytic virtual carrier.
    implications = (
        ("root", "parent"),
        ("parent", "access"),
        ("access", "collar"),
        ("parent", "obstacle"),
    )

    def saturate(order: tuple[tuple[str, str], ...]) -> set[str]:
        result = {"root"}
        changed = True
        while changed:
            changed = False
            for source, target in order:
                if source in result and target not in result:
                    result.add(target)
                    changed = True
        return result

    expected = {"root", "parent", "access", "collar", "obstacle"}
    for order in permutations(implications):
        assert saturate(order) == expected


def test_wave_program_extension_requires_reaudit() -> None:
    # A fixed-point closure for the old proof program does not protect
    # against a genuinely new proof seed.  The new path to an omitted old
    # record must be detected by the extension criterion.
    old_records = {"root", "latent"}
    old_seeds = {"root"}
    old_edges: set[tuple[str, str]] = set()

    def closure(
        seeds: set[str], edges: set[tuple[str, str]]
    ) -> set[str]:
        result = set(seeds)
        while True:
            successor = result | {
                target for source, target in edges if source in result
            }
            if successor == result:
                return result
            result = successor

    old_inventory = closure(old_seeds, old_edges)
    assert old_inventory == {"root"}

    new_inventory = closure(
        old_seeds | {"late-wave"},
        old_edges | {("late-wave", "latent")},
    )
    assert new_inventory & old_records == {"root", "latent"}
    assert new_inventory & old_records != old_inventory


def test_unresolved_wave_branch_is_rejected() -> None:
    # The compiler requires an actual finite iterate and all analytic branch
    # fields.  A component label with an unknown iterate is not a resolved
    # edge.
    required = {
        "source_surface",
        "target_surface",
        "cover",
        "immersion",
        "iterate",
        "degree_word",
        "marking_refinement",
        "properness",
        "enlargement_stability",
    }
    label_only = {
        "source_surface": "virtual-source",
        "target_surface": "virtual-target",
        "component_label": "central",
    }
    native_pair = {
        "source_surface": "U^r\\T^r",
        "target_surface": "U\\T",
        "cover": "f^r",
        "immersion": "iota_r",
        "iterate": 11,
        "degree_word": (1, 1, 2),
        "marking_refinement": True,
        "properness": "end-proper-on-used-intervals",
        "enlargement_stability": "identity-root-positive-control",
    }
    assert not required <= set(label_only)
    assert required <= set(native_pair)
    assert isinstance(native_pair["iterate"], int)
    assert native_pair["iterate"] > 0


def test_return_path_language_is_prefix_closed() -> None:
    # A typed branch graph generates words before any stopping execution.
    # Each stored path must retain every prefix and sum actual edge iterates.
    edges = {
        "root": (("central", "a", 3), ("terminal", "b", 5)),
        "a": (("critical", "c", 7),),
        "b": (),
        "c": (),
    }

    def paths(vertex: str, word: tuple[str, ...] = (), span: int = 0):
        yield word, span
        for label, target, iterate in edges[vertex]:
            yield from paths(target, word + (label,), span + iterate)

    language = {word for word, _ in paths("root")}
    spans = {word: span for word, span in paths("root")}
    for word in language:
        for length in range(len(word) + 1):
            assert word[:length] in language
    assert spans[("central", "critical")] == 10
    assert spans[("terminal",)] == 5


def test_prime_end_endpoint_refinement_criterion() -> None:
    # On a circle, more endpoints mean a finer ideal marking.  Thus the
    # covering-pulled marking refines the immersion-pulled marking exactly
    # when the latter endpoint set is contained in the former.
    covering_endpoints = {0.0, 0.5}
    valid_immersion_endpoints = {0.0}
    invalid_immersion_endpoints = {0.25}
    assert valid_immersion_endpoints <= covering_endpoints
    assert not invalid_immersion_endpoints <= covering_endpoints


def test_marked_pair_boundary_phase_countermodel() -> None:
    # For g(z)=z^2 and iota_alpha(z)=exp(i alpha)z on the exterior disk,
    # target endpoint 1 pulls back to {1,-1} under g and exp(-i alpha)
    # under iota.  In normalized turns a=alpha/(2*pi), action holds only
    # for a=0 or 1/2.
    covering_endpoints = {0.0, 0.5}

    def immersion_endpoint(a: float) -> float:
        return (-a) % 1.0

    assert immersion_endpoint(0.0) in covering_endpoints
    assert immersion_endpoint(0.5) in covering_endpoints
    assert immersion_endpoint(0.25) not in covering_endpoints
    assert immersion_endpoint(1 / 3) not in covering_endpoints


def test_access_orbit_closure_requires_phase_record() -> None:
    # The affine boundary transition beta_a(t)=2t-2a is conjugate to
    # doubling by h_a(t)=t-2a.  This finite check verifies the conjugacy
    # algebra and contrasts a periodic endpoint with a long nonrepeating
    # orbit.  It is diagnostic only and does not prove density.
    def beta(t: float, a: float) -> float:
        return (2 * t - 2 * a) % 1.0

    def h(t: float, a: float) -> float:
        return (t - 2 * a) % 1.0

    def circle_distance(left: float, right: float) -> float:
        difference = abs(left - right) % 1.0
        return min(difference, 1.0 - difference)

    for a in (0.0, 0.125, 0.2, 0.314159):
        for t in (0.0, 0.1, 0.37, 0.9):
            assert circle_distance(
                h(beta(t, a), a),
                (2 * h(t, a)) % 1.0,
            ) < 1e-12

    periodic = 0.0
    periodic_orbit = []
    for _ in range(12):
        periodic_orbit.append(periodic)
        periodic = (2 * periodic) % 1.0
    assert set(periodic_orbit) == {0.0}

    # 1/31 has doubling period five, illustrating that a phase changes the
    # complete endpoint orbit even when carrier and degree data are fixed.
    phased = 1 / 31
    phased_orbit = []
    for _ in range(5):
        phased_orbit.append(phased)
        phased = (2 * phased) % 1.0
    assert len(set(phased_orbit)) == 5
    assert isclose(phased, 1 / 31)


def test_marked_enlargement_endpoint_naturality() -> None:
    # A finite endpoint model of the commuting-square proof.  Exact inverse
    # image marking, rather than coarse label equality, transports the
    # endpoint-containment condition.
    target_p = {"upper", "lower"}
    cover_p = {"u0", "u1", "l0", "l1"}
    immersion_p = {"u0", "l0"}
    assert immersion_p <= cover_p

    a_target = {"U": "upper", "L": "lower"}
    a_source = {"U0": "u0", "U1": "u1", "L0": "l0", "L1": "l1"}
    target_q = {x for x, image in a_target.items() if image in target_p}
    cover_q = {x for x, image in a_source.items() if image in cover_p}
    immersion_q = {x for x, image in a_source.items() if image in immersion_p}
    assert target_q == {"U", "L"}
    assert immersion_q <= cover_q

    # A newly born endpoint violates exact inverse-image transport even if
    # its coarse side label agrees.
    coarse_only = immersion_q | {"NEW"}
    assert not coarse_only <= cover_q


def test_return_base_changes_first_return_time() -> None:
    # Exact witness from RETURN_BASE_UNDERDETERMINATION.  For f(z)=z^2-1,
    # the seed -1 has return time two to the small disk and return time one
    # to the larger disk.  Thus a compact seed does not specify a return
    # branch until its open return base is fixed.
    def f(z: complex) -> complex:
        return z * z - 1

    seed = -1 + 0j

    def in_disk(z: complex, center: complex, radius: float) -> bool:
        return abs(z - center) < radius

    small = (-1 + 0j, 0.25)
    large = (-0.5 + 0j, 0.75)
    assert in_disk(seed, *small)
    assert not in_disk(f(seed), *small)
    assert in_disk(f(f(seed)), *small)
    assert in_disk(seed, *large)
    assert in_disk(f(seed), *large)


def test_analytic_prefix_iterate_composition() -> None:
    # Diagnostic check of equation (4.6): extending an actual q1-prefix by
    # an actual q2-branch gives the q1+q2 iterate.  The proof is algebraic;
    # this finite calculation prevents an accidental order reversal.
    def f(z: complex) -> complex:
        return z * z - 1

    def iterate(z: complex, count: int) -> complex:
        for _ in range(count):
            z = f(z)
        return z

    z = 0.13 + 0.07j
    q1, q2 = 2, 3
    chronological = iterate(iterate(z, q1), q2)
    summed = iterate(z, q1 + q2)
    assert abs(chronological - summed) < 1e-12

    first_degree_word = (2, 1)
    second_degree_word = (1, 2, 1)
    assert first_degree_word + second_degree_word == (2, 1, 1, 2, 1)


def test_demand_closed_unfolding_keeps_word_and_sheet() -> None:
    # Terminal geometry alone is not a node identity.  Two words reaching
    # the same terminal label on different sheets remain distinct nodes in
    # the rooted unfolding.
    children = {
        (): (("central", "left", 2), ("central", "right", 2)),
        (("central", "left"),): (("terminal", "left", 3),),
        (("central", "right"),): (("terminal", "right", 3),),
    }

    nodes: set[tuple[tuple[str, str], ...]] = {()}
    frontier = [()]
    spans = {(): 0}
    while frontier:
        prefix = frontier.pop()
        for label, sheet, iterate in children.get(prefix, ()):
            child = prefix + ((label, sheet),)
            nodes.add(child)
            spans[child] = spans[prefix] + iterate
            frontier.append(child)

    left = (("central", "left"), ("terminal", "left"))
    right = (("central", "right"), ("terminal", "right"))
    assert left in nodes and right in nodes and left != right
    assert spans[left] == spans[right] == 5
    for word in nodes:
        for length in range(len(word) + 1):
            assert word[:length] in nodes


def test_injective_atlas_enlargement_does_not_prove_no_birth() -> None:
    # An injective child map preserves all old demands but does not establish
    # complete language stability when the enlarged package has a new child.
    old_children = {"central", "terminal"}
    enlarged_children = {"CENTRAL", "TERMINAL", "LATE_ROOT"}
    transport = {"central": "CENTRAL", "terminal": "TERMINAL"}
    assert set(transport) == old_children
    assert set(transport.values()) <= enlarged_children
    assert set(transport.values()) != enlarged_children

    # The demand-bijective criterion is the exact finite no-birth check.
    collision_free_children = {"CENTRAL", "TERMINAL"}
    assert set(transport.values()) == collision_free_children


def test_isotopic_return_bases_change_return_time() -> None:
    # Proposition ISOTOPY_CLASS_RETURN_UNDERDETERMINATION uses concentric
    # disks.  Scaling about -1 is an ambient affine isotopy fixing the seed,
    # yet the return time changes when the disk first contains 0.
    def f(z: complex) -> complex:
        return z * z - 1

    seed = -1 + 0j
    small_radius = 0.25
    large_radius = 1.25

    def h(t: float, z: complex) -> complex:
        return -1 + (1 + 4 * t) * (z + 1)

    assert h(0, seed) == seed == h(1, seed)
    assert isclose(abs(h(1, -1 + small_radius) + 1), large_radius)
    assert abs(f(seed) + 1) == 1 > small_radius
    assert abs(f(f(seed)) + 1) == 0 < small_radius
    assert abs(f(seed) + 1) == 1 < large_radius


def test_principal_return_critical_chronology() -> None:
    # In a first-return itinerary to a base containing the unique critical
    # point, an intermediate critical hit would already be an early return.
    # Hence a noncentral word is all degree one and a central word has its
    # sole degree-two entry first.
    base = {"critical", "terminal"}
    central_itinerary = (
        {"critical"},
        {"outside-left"},
        {"outside-right"},
        {"terminal"},
    )
    noncentral_itinerary = (
        {"sheet-a"},
        {"outside-left"},
        {"outside-right"},
        {"terminal"},
    )
    for itinerary in (central_itinerary, noncentral_itinerary):
        assert all(not (stage & base) for stage in itinerary[1:-1])

    central_word = tuple(2 if "critical" in stage else 1 for stage in central_itinerary[:-1])
    noncentral_word = tuple(2 if "critical" in stage else 1 for stage in noncentral_itinerary[:-1])
    assert central_word == (2, 1, 1)
    assert noncentral_word == (1, 1, 1)


def test_virtual_scale_selector_is_a_real_gate() -> None:
    # A parameter-copy index and a terminal native atlas do not fill the
    # selector row.  All analytic and marking fields must be present before
    # the row can instantiate a virtual return base.
    required = {
        "scale",
        "puzzle_level",
        "embedded_base",
        "carrier",
        "components",
        "critical_orbit",
        "accesses",
        "obstacles",
        "demands",
    }
    source_row = {"scale": 3}
    terminal_native_row = {
        "puzzle_level": 17,
        "embedded_base": "V17",
        "components": ("central", "lateral"),
    }
    attempted = source_row | terminal_native_row
    assert required - set(attempted) == {
        "carrier",
        "critical_orbit",
        "accesses",
        "obstacles",
        "demands",
    }
    completed = attempted | {
        "carrier": "H3",
        "critical_orbit": ("c0", "c1"),
        "accesses": ("a0",),
        "obstacles": (),
        "demands": ("wave-entry",),
    }
    assert required <= set(completed)


def test_first_decoration_escape_selector_is_least_event() -> None:
    # The first direct-decoration selector is not chosen from a width or
    # stopping estimate.  It is the least q-return at which the critical
    # itinerary enters an off-critical Z-piece.
    q = 3
    q_return_pieces = ("Y1", "Y1", "Y1", "Z_kappa")
    escape_indices = [
        index
        for index, piece in enumerate(q_return_pieces, start=1)
        if piece.startswith("Z_")
    ]
    n = min(escape_indices)
    assert n == 4
    assert all(piece == "Y1" for piece in q_return_pieces[: n - 1])
    assert q_return_pieces[n - 1] == "Z_kappa"
    assert n * q + 1 == 13


def test_critical_return_base_excludes_intermediate_cycle() -> None:
    # A primitive terminal branch is a first return.  Hence every
    # intermediate image of its central domain, and therefore every
    # intermediate little Julia set, is outside the open return base.
    period = 5
    base = {"K0", "base-buffer"}
    cycle = tuple(f"K{i}" for i in range(period))
    intermediate_images = tuple({cycle[i]} for i in range(1, period))
    assert all(not (image & base) for image in intermediate_images)
    assert cycle[1] == "K1"

    # The unique quadratic step occurs at the source containing the unique
    # critical point; all later selected component maps are univalent.
    contains_critical = (True,) + (False,) * (period - 1)
    degree_word = tuple(2 if critical else 1 for critical in contains_critical)
    assert degree_word == (2, 1, 1, 1, 1)


def test_raw_decoration_fan_has_exponential_access_growth() -> None:
    # Kahn--Lyubich's quadratic decoration puzzle has one pairwise-disjoint
    # pullback Q^v for each of the 2^n vertices.  Finiteness at each n does
    # not give a uniform access bound.
    sizes = [2**n for n in range(1, 9)]
    assert sizes == [2, 4, 8, 16, 32, 64, 128, 256]
    assert all(next_size > size for size, next_size in zip(sizes, sizes[1:]))
    proposed_universal_bound = 100
    assert any(size > proposed_universal_bound for size in sizes)


def test_native_hubbard_vertex_package_has_unique_hull() -> None:
    # A finite tree package has a unique convex hull: the union of unique
    # paths between selected vertices.  Adding an unselected ambient branch
    # does not enlarge that hull.
    adjacency = {
        "K0": {"b"},
        "b": {"K0", "K1", "x"},
        "K1": {"b"},
        "x": {"b", "K2"},
        "K2": {"x"},
    }
    assert tree_hull(adjacency, {"K0", "K1"}) == frozenset({"K0", "b", "K1"})
    assert tree_hull(adjacency, {"K0", "K2"}) == frozenset(
        {"K0", "b", "x", "K2"}
    )


def test_injective_tree_transport_gives_exact_hull() -> None:
    # Diagnostic finite version of Theorem 5.1.  The selected path is
    # transported injectively, so the image path equals the hull of the
    # transported selected vertices.
    adjacency = {
        "v0": {"v1"},
        "v1": {"v0", "v2"},
        "v2": {"v1", "v3"},
        "v3": {"v2"},
    }
    selected = {"v0", "v2"}
    transport = {"v0": "v1", "v1": "v2", "v2": "v3"}
    source_hull = tree_hull(adjacency, selected)
    image_hull = frozenset(transport[vertex] for vertex in source_hull)
    transported_selected = {transport[vertex] for vertex in selected}
    assert image_hull == tree_hull(adjacency, transported_selected)


def test_folded_tree_transport_retains_excess() -> None:
    # Endpoint labels alone can hide a folded excursion.  Both selected
    # endpoints map to a, while the middle of their path maps to b.  The
    # image of the source hull is therefore strictly larger than the hull
    # of the image package.
    target = {"a": {"b"}, "b": {"a"}}
    selected_image = {"a"}
    image_of_source_hull = {"a", "b"}
    assert tree_hull(target, selected_image) == frozenset({"a"})
    assert image_of_source_hull - set(tree_hull(target, selected_image)) == {"b"}


def test_hubbard_hull_enlargement_has_one_gate() -> None:
    # Enlarging the selected package adds a branch attached to the old hull
    # at one gate.  A two-gate attachment would create a cycle.
    adjacency = {
        "K0": {"g"},
        "g": {"K0", "K1", "u"},
        "K1": {"g"},
        "u": {"g", "K2"},
        "K2": {"u"},
    }
    old_hull = set(tree_hull(adjacency, {"K0", "K1"}))
    new_hull = set(tree_hull(adjacency, {"K0", "K1", "K2"}))
    added = new_hull - old_hull
    gates = {
        neighbor
        for vertex in added
        for neighbor in adjacency[vertex]
        if neighbor in old_hull
    }
    assert added == {"u", "K2"}
    assert gates == {"g"}


def test_ambient_hubbard_tree_does_not_select_virtual_package() -> None:
    # The same ambient terminal tree and critical root admit distinct
    # virtual subtrees until the scale-to-vertex-package map is supplied.
    adjacency = {
        "K0": {"K1"},
        "K1": {"K0", "K2"},
        "K2": {"K1"},
    }
    short_package = {"K0", "K1"}
    long_package = {"K0", "K1", "K2"}
    assert tree_hull(adjacency, short_package) != tree_hull(
        adjacency, long_package
    )


def test_finite_terminal_labels_do_not_enumerate_cantor_addresses() -> None:
    # A finite terminal-tree code can only quotient an expanding address
    # family.  Already at binary depth three, eight distinct cylinders
    # cannot be injectively assigned to the three available terminal labels.
    addresses = {
        f"{value:03b}"
        for value in range(8)
    }
    terminal_labels = ("K0", "K1", "K2")
    code = {
        address: terminal_labels[int(address, 2) % len(terminal_labels)]
        for address in addresses
    }
    assert len(addresses) == 8
    assert len(set(code.values())) == 3
    assert len(code) > len(set(code.values()))


def test_cantor_quotient_requires_joint_observable_constancy() -> None:
    # Quotienting by the first binary digit preserves the present observable
    # "first digit" but loses the future observable "second digit".  Hence
    # equality of the coarse label does not license a future-faithful trace.
    addresses = ("00", "01", "10", "11")
    quotient = {address: address[0] for address in addresses}
    present = {address: address[0] for address in addresses}
    future = {address: address[1] for address in addresses}

    for left in addresses:
        for right in addresses:
            if quotient[left] == quotient[right]:
                assert present[left] == present[right]

    collisions = {
        (left, right)
        for left in addresses
        for right in addresses
        if quotient[left] == quotient[right] and future[left] != future[right]
    }
    assert collisions


def test_pullback_nesting_parent_differs_from_dynamic_shift() -> None:
    # A cylinder is nested by appending a symbol on the right, whereas the
    # actual f^q branch deletes the first symbol.  Conflating these two maps
    # corrupts the return itinerary as soon as the word has length at least
    # three.
    word = "011"
    geometric_parent = word[:-1]
    dynamic_shift = word[1:]
    inverse_sheet = word[0]
    assert geometric_parent == "01"
    assert dynamic_shift == "11"
    assert geometric_parent != dynamic_shift
    assert inverse_sheet == "0"


def test_bigraded_parent_shift_square_commutes() -> None:
    # The operations are distinct but commute on a word awb:
    # delete the last symbol then the first, or first then last.
    for middle_length in range(0, 8):
        for symbols in product("01", repeat=middle_length + 2):
            word = "".join(symbols)
            parent_then_shift = word[:-1][1:]
            shift_then_parent = word[1:][:-1]
            assert parent_then_shift == shift_then_parent

    # Neither operation may be replaced by the other on a general word.
    witness = "011"
    assert witness[:-1] != witness[1:]


def test_binder_ledger_reachability_and_extension() -> None:
    # Finite source-occurrence graph, oriented use -> prerequisite.
    graph = {
        "use": {"family", "call"},
        "family": {"interval"},
        "call": {"hypothesis"},
        "hypothesis": {"call"},  # one nontrivial SCC
        "interval": set(),
        "new_requirement": set(),
    }

    def reachable(
        adjacency: dict[str, set[str]],
        seeds: set[str],
    ) -> set[str]:
        seen = set(seeds)
        work = list(seeds)
        while work:
            node = work.pop()
            for dependency in adjacency[node]:
                if dependency not in seen:
                    seen.add(dependency)
                    work.append(dependency)
        return seen

    old = reachable(graph, {"use"})
    assert old == {"use", "family", "interval", "call", "hypothesis"}

    # Adding an outgoing edge from an old reachable token creates a new
    # syntactic demand even though no new seed is added.
    enlarged = {node: set(deps) for node, deps in graph.items()}
    enlarged["family"].add("new_requirement")
    new = reachable(enlarged, {"use"})
    assert new == old | {"new_requirement"}
    assert new != old


def test_pullback_end_compactification_prefix_convergence() -> None:
    # Finite vertices are terminated by #.  Increasing prefixes converge to
    # the binary end because every fixed coordinate eventually agrees.
    end = "010110101101"
    finite_vertices = [end[:depth] + "#" for depth in range(1, len(end) + 1)]
    for fixed_depth in range(1, 8):
        assert all(
            vertex[:fixed_depth] == end[:fixed_depth]
            for vertex in finite_vertices[fixed_depth:]
        )


def test_pullback_gap_enlargement_and_collision_ledger() -> None:
    # The abstract labels model three disjoint first-level regions:
    # the safe root gap G and the two pullback cylinders Q0,Q1.  Enlargement
    # inside G preserves disjointness.  Adding a point already present in a
    # child produces an actual root/child collision, rather than merely a
    # gap-warning.
    root = {"k"}
    enlarged_safe = {"k", "connector"}
    child_zero = {"z0"}
    child_one = {"z1"}
    assert enlarged_safe.isdisjoint(child_zero | child_one)

    enlarged_collision = enlarged_safe | {"z0"}
    collision_ledger = {
        ("root", "0")
        for point in enlarged_collision & child_zero
    }
    assert collision_ledger == {("root", "0")}


def test_finite_cylinder_commuting_iterate_lift() -> None:
    # On the positive real branch of f(z)=z^2, h=f^N is a homeomorphism of
    # (0,1) onto itself.  Equal cylinder depths make the conjugacy identity
    # h^{-1} f^r h = f^r exact.
    def iterate_square(value: float, count: int) -> float:
        for _ in range(count):
            value *= value
        return value

    depth = 3
    return_time = 2
    point = 0.83
    h_point = iterate_square(point, depth)
    base_image = iterate_square(h_point, return_time)
    inverse_h_image = base_image ** (1 / (2**depth))
    lifted_image = iterate_square(point, return_time)
    assert abs(inverse_h_image - lifted_image) < 1e-12


def test_target_address_requires_actual_uniqueness() -> None:
    # Closed target cylinders can share a boundary label.  An image reduced
    # to that boundary point has two candidate addresses, so the commuting
    # formula cannot itself select a target cylinder.
    target_zero = {-1, 0}
    target_one = {0, 1}
    image_component = {0}
    candidates = [
        name
        for name, cylinder in (("0", target_zero), ("1", target_one))
        if image_component <= cylinder
    ]
    assert candidates == ["0", "1"]
    assert len(candidates) != 1


def test_future_observable_coordinate_shift() -> None:
    # Finite diagnostic for the future-observable construction.  The
    # transition is partial at 4, and None is the isolated undefined
    # symbol.  Shifting the exact future table of x must give the table of
    # T(x) on the declared domain.
    states = range(5)

    def transition(state: int) -> int | None:
        return state + 1 if state < 4 else None

    def future_table(state: int, horizon: int = 5) -> tuple[tuple[int, int] | None, ...]:
        table: list[tuple[int, int] | None] = []
        current: int | None = state
        for _ in range(horizon):
            table.append(None if current is None else (current, current % 2))
            current = None if current is None else transition(current)
        return tuple(table)

    for state in states:
        table = future_table(state)
        image = transition(state)
        if image is None:
            assert table[1] is None
        else:
            assert table[1:] == future_table(image)[:-1]


def test_direct_decoration_gap_cells_separate_ancestors() -> None:
    # Ternary cylinders model the two inverse children, while the middle
    # third models the root gap cell.  Pulling the middle cell through
    # every word makes ancestor and descendant cells disjoint.
    def cylinder(word: str) -> tuple[float, float]:
        left, right = 0.0, 1.0
        for symbol in word:
            width = (right - left) / 3
            if symbol == "0":
                right = left + width
            else:
                left = right - width
        return left, right

    def gap_cell(word: str) -> tuple[float, float]:
        left, right = cylinder(word)
        width = (right - left) / 3
        return left + width, right - width

    words = [
        "".join(symbols)
        for length in range(5)
        for symbols in product("01", repeat=length)
    ]
    cells = {word: gap_cell(word) for word in words}
    for index, word in enumerate(words):
        a0, a1 = cells[word]
        for other in words[index + 1 :]:
            b0, b1 = cells[other]
            assert a1 <= b0 or b1 <= a0


def test_component_forcing_does_not_supply_authorization() -> None:
    # Interior containment forces a unique ambient open component, but an
    # incomplete authorized family can still omit it.  This distinguishes
    # the proved component lemma from the open virtual authorization gate.
    ambient_components = {
        "left": (-2.0, -1.0),
        "right": (1.0, 2.0),
    }
    image = (1.25, 1.5)
    reached = [
        name
        for name, (left, right) in ambient_components.items()
        if left < image[0] and image[1] < right
    ]
    assert reached == ["right"]

    authorized = {"left"}
    assert reached[0] not in authorized


def test_critical_cut_pointwise_word_conservation() -> None:
    # The critical orbit of f(z)=z^2-1 alternates 0,-1,0,-1,... .
    # Its local-degree word therefore alternates 2,1.  Moving the cut
    # between commuting iterates changes no absolute-time entry.
    def f(value: float) -> float:
        return value * value - 1

    def iterate(value: float, count: int) -> float:
        for _ in range(count):
            value = f(value)
        return value

    def word(value: float, count: int) -> tuple[int, ...]:
        entries: list[int] = []
        for _ in range(count):
            entries.append(2 if isclose(value, 0.0) else 1)
            value = f(value)
        return tuple(entries)

    start = 0.0
    return_time = 3
    cylinder_time = 4
    full_word = word(start, return_time + cylinder_time)
    first_cut = word(start, return_time) + word(
        iterate(start, return_time), cylinder_time
    )
    second_cut = word(start, cylinder_time) + word(
        iterate(start, cylinder_time), return_time
    )
    assert first_cut == second_cut == full_word


def test_critical_time_shear_degree_ladder() -> None:
    # The z^2-1 example has root word (2,1), lifted word (1,2), and
    # transverse degrees e=(1,2,1).  Both squares satisfy
    # lift_j*e_(j+1)=e_j*root_j, while endpoint degree sees no difference.
    root = (2, 1)
    lifted = (1, 2)
    transverse = [1]
    for root_degree, lift_degree in zip(root, lifted, strict=True):
        numerator = transverse[-1] * root_degree
        assert numerator % lift_degree == 0
        transverse.append(numerator // lift_degree)
    assert transverse == [1, 2, 1]
    assert root[0] * root[1] == lifted[0] * lifted[1] == 2
    assert root != lifted


def test_retimed_iterate_identity_is_only_algebraic() -> None:
    # Polynomial iterates commute, so the retimed exponent identity is
    # exact.  The Boolean `authorized` flag models the separate source
    # theorem that the arithmetic cannot supply.
    def f(value: complex) -> complex:
        return value * value - 1

    def iterate(value: complex, count: int) -> complex:
        for _ in range(count):
            value = f(value)
        return value

    point = 0.27 + 0.11j
    cylinder_time = 3
    root_time = 2
    assert abs(
        iterate(point, cylinder_time + root_time)
        - iterate(iterate(point, cylinder_time), root_time)
    ) < 1e-12
    source_catalog = {"direct_decoration_cylinders", "terminal_root"}
    assert "virtual_scale_two_root_portrait" not in source_catalog


def test_arbitrary_prime_end_marking_can_fail() -> None:
    # For (z^2,id) on the disk, the immersion pullback of angle 1/3 is
    # 1/3, while the covering pullbacks are 1/6 and 2/3.  Endpoint
    # containment fails, so a finite marking is not automatically valid.
    immersion_pullback = {1 / 3}
    covering_pullback = {1 / 6, 2 / 3}
    assert not immersion_pullback <= covering_pullback


def test_interior_univalence_does_not_force_jordan_image() -> None:
    # z^2 is injective on the open right half-disk, but opposite points on
    # the imaginary boundary are identified.  A closure embedding is a
    # genuine extra hypothesis in the planar telescope.
    upper = 0.5j
    lower = -0.5j
    assert upper != lower
    assert upper**2 == lower**2


def test_quadratic_base_change_loses_degree_off_spine() -> None:
    # The sample target point 1/2 avoids the critical value 0 of z^2 and
    # has two distinct preimages.  A small disk around it therefore has
    # two univalent pullback components; selecting one loses degree two.
    target = 0.5
    roots = {sqrt(target), -sqrt(target)}
    assert len(roots) == 2
    selected_component_degree = 1
    assert selected_component_degree != 2


def test_prime_end_embedding_uses_image_circle_not_target_circle() -> None:
    # The embedding z -> z/2 sends the unit source circle to an interior
    # circle.  It does not induce a homeomorphism onto the target unit
    # circle, which is the precise flaw in the broad marked-assembly claim.
    source_boundary_point = complex(1, 0)
    image_boundary_point = source_boundary_point / 2
    assert isclose(abs(source_boundary_point), 1)
    assert isclose(abs(image_boundary_point), 0.5)
    assert not isclose(abs(image_boundary_point), 1)


def test_fixed_iterate_nested_set_extension() -> None:
    # C_n=[-1/n,1/n], D_n=[0,1/n^2], and F(x)=x^2 give exact levelwise
    # surjectivity and equal singleton intersections.
    for n in range(1, 20):
        source_endpoints = (-1 / n, 1 / n)
        target_endpoints = (0.0, 1 / (n * n))
        images = (source_endpoints[0] ** 2, source_endpoints[1] ** 2)
        assert isclose(max(images), target_endpoints[1])
    source_intersection = {0.0}
    target_intersection = {0.0}
    assert {value * value for value in source_intersection} == target_intersection


def test_retention_boolean_is_not_a_geometric_certificate() -> None:
    # The same Boolean word can label a valid Jordan base and a slit base.
    # A finite script that accepts only the word cannot distinguish them.
    jordan_record = {
        "retention": (True, True),
        "geometry": ("embedded", "proper", "critical-contained"),
    }
    slit_record = {
        "retention": (True, True),
        "geometry": ("prime-end-lift-only", "non-jordan", "critical-contained"),
    }
    assert jordan_record["retention"] == slit_record["retention"]
    assert jordan_record["geometry"] != slit_record["geometry"]


def test_boundary_critical_value_is_not_strict_exterior() -> None:
    # For z^2, the critical value 0 lies on the boundary of the disk
    # D(1/2,1/2).  This is neither the retained-interior case nor the
    # strict-exterior case certified by the unbranched-collar dichotomy.
    critical_value = 0.0
    center = 0.5
    radius = 0.5
    distance = abs(critical_value - center)
    assert isclose(distance, radius)
    assert not distance < radius
    assert not distance > radius


def test_nested_compact_equality_needs_hausdorff_gate() -> None:
    # Symbolic core of the cofinite-topology counterexample:
    # C_n={n,n+1,...} is nonempty at every finite level, but every fixed
    # integer x is excluded by C_(x+1), so the infinite intersection is
    # empty.  In the cofinite topology every C_n is compact.
    def in_tail(value: int, level: int) -> bool:
        return value >= level

    for level in range(1, 100):
        assert in_tail(level, level)
    for value in range(100):
        assert not in_tail(value, value + 1)


def test_normalized_end_direct_limit_coordinate() -> None:
    # Linear toy charts have the exact compatibility used by the analytic
    # direct-limit proof: h_(m+1) o t_m = h_m.  The test checks only the
    # coordinate algebra, not existence of a virtual planar component.
    for level in range(0, 20):
        h_level = lambda value, level=level: (2**level) * value
        h_next = lambda value, level=level: (2 ** (level + 1)) * value
        transition = lambda value: value / 2
        for numerator in range(-8, 9):
            value = numerator / 7
            assert isclose(
                h_next(transition(value)),
                h_level(value),
                rel_tol=1e-12,
                abs_tol=1e-12,
            )


def test_shift_grading_conflict_requires_unfolding() -> None:
    # A presentation path from u to v has net shift zero, while a second path
    # has net shift one.  One physical depth assignment would require both
    # s(u)=s(v) and s(u)=s(v)+1.
    presentation_shift_count = 0
    dynamical_shift_count = 1
    assert presentation_shift_count != dynamical_shift_count
    for source_grade in range(-5, 6):
        target_from_presentation = source_grade
        target_from_shift = source_grade - 1
        assert target_from_presentation != target_from_shift


def test_scalar_neck_trace_mode_no_go() -> None:
    # On [0,L] x S^1, the constant-mode conductance is 2*pi/L.  The
    # Dirichlet energy of cos(k theta) against zero is pi*k*coth(kL).
    # Since osc(cos)=2, the scalar estimate proposed in Push III would bound
    # this by 4 times the constant conductance, which fails for long necks.
    for length in (8.0, 16.0, 32.0, 64.0):
        scalar_conductance = 2 * pi / length
        scalar_oscillation_bound = 4 * scalar_conductance
        for mode in range(1, 6):
            trace_energy = pi * mode / tanh(mode * length)
            assert trace_energy >= pi * mode
            assert trace_energy > scalar_oscillation_bound


def test_full_trace_rectangle_sharp_mode_bound() -> None:
    # On a positive Fourier mode, the normalized difference from the two
    # half-cylinder responses has eigenvalues 2/(e^t-1) and -2/(e^t+1).
    # The worst absolute value must occur at the first mode.
    for length in (0.5, 1.0, 2.0, 4.0):
        eta = 2 / (exp(pi * length) - 1)
        observed = []
        for mode in range(1, 12):
            t = mode * pi * length
            eigenvalues = (
                2 / (exp(t) - 1),
                -2 / (exp(t) + 1),
            )
            observed.append(max(abs(value) for value in eigenvalues))
        assert isclose(observed[0], eta, rel_tol=1e-12, abs_tol=1e-12)
        assert all(value <= eta for value in observed)
        assert all(
            observed[index + 1] < observed[index]
            for index in range(len(observed) - 1)
        )


def test_pulled_equipotential_arcs_do_not_form_serial_rectangle() -> None:
    # Under z -> z^(2^q), a chosen inverse branch divides angular width by
    # 2^q. Opposite equipotential sides bounded by the same two rays must
    # have equal angular widths, so a full parent arc and its full pulled
    # child cannot be those two sides unless the arc is degenerate.
    for q in range(1, 13):
        degree = 2**q
        for parent_width in (1 / 3, 1 / 7, 0.01, 0.4):
            child_width = parent_width / degree
            assert child_width > 0
            assert child_width < parent_width
            assert not isclose(
                parent_width,
                child_width,
                rel_tol=1e-12,
                abs_tol=1e-15,
            )


def test_positive_cell_resistance_does_not_force_finite_depth_margin() -> None:
    # Positivity of each cell resistance is insufficient for a claimed
    # finite-depth strictness choice: a positive summable sequence can have
    # total resistance below the required threshold forever.
    mu = 0.82
    target_eta = 0.5 * (1 - mu) / (1 + mu)
    required_resistance = log(1 + 2 / target_eta) / pi
    total = 0.0
    for level in range(1, 200):
        total += 2 ** (-(level + 4))
        # Floating-point summation eventually rounds the increasing partial
        # sums to their exact limit 1/16.
        assert total <= 1 / 16
        assert total < required_resistance


def test_one_sided_transition_stability_needs_input_alignment() -> None:
    # L(z)=z on the nonnegative line satisfies the one-sided output estimate.
    # A root contraction does not imply a physical contraction when the
    # physical input is unrelated to the root input.
    mu = 0.5
    root_input = 2.0
    root_output = 1.0
    assert root_output <= mu * root_input

    physical_input = 0.1
    physical_output = root_output
    output_perturbation = 0.0
    assert physical_output <= root_output + output_perturbation
    assert physical_output > mu * physical_input + output_perturbation


def test_push5_contact_welding_no_go() -> None:
    # These are exact finite/topological falsification certificates.  They
    # do not promote an analytic response or MLC obligation.
    assert circle_atom_certificate()["passes"]
    assert bypass_certificate()["passes"]
    assert welding_conjugacy_certificate()["passes"]
    assert pseudoinverse_cutoff_certificate()["passes"]


def test_contact_pair_graph_loses_atom_incidence() -> None:
    # One physical atom incident to three cells and three distinct pairwise
    # atoms have the same projected cell-pair graph.  They impose different
    # trace identifications, so the pair graph is not a complete response
    # state.
    shared_atom_state = [
        {"atom": "J", "incidence": frozenset({0, 1, 2})},
    ]
    distinct_pair_state = [
        {"atom": "J01", "incidence": frozenset({0, 1})},
        {"atom": "J02", "incidence": frozenset({0, 2})},
        {"atom": "J12", "incidence": frozenset({1, 2})},
    ]

    def pair_projection(state: list[dict[str, object]]) -> set[tuple[int, int]]:
        pairs: set[tuple[int, int]] = set()
        for record in state:
            incidence = sorted(record["incidence"])
            for left_index, left in enumerate(incidence):
                for right in incidence[left_index + 1 :]:
                    pairs.add((left, right))
        return pairs

    assert pair_projection(shared_atom_state) == pair_projection(distinct_pair_state)
    assert len(shared_atom_state) == 1
    assert len(distinct_pair_state) == 3
    assert shared_atom_state != distinct_pair_state


def test_parametrized_lollipop_does_not_exhaust_geometric_trace() -> None:
    # The identity fiber product remembers one chronological traversal,
    # whereas KKL restriction is defined from every proper path contained
    # in the geometric trace.
    parametrized_word = (
        "left",
        "upper_forward",
        "lower_reverse",
        "lower_forward",
        "right",
    )
    lower_route = ("left", "lower_forward", "right")

    def trace(word: tuple[str, ...]) -> set[str]:
        return {
            token.replace("_forward", "").replace("_reverse", "")
            for token in word
        }

    assert trace(lower_route) < trace(parametrized_word)
    assert lower_route != parametrized_word


def test_exponential_immersion_retains_infinite_phase_labels() -> None:
    # Finite sampling of the exact family
    # K(z)=exp(-(1+z)/(1-z)), z_k(t)=(u_k-1)/(u_k+1).
    endpoints: list[complex] = []
    for k in range(-8, 9):
        endpoint = (2j * pi * k - 1) / (2j * pi * k + 1)
        assert isclose(abs(endpoint), 1.0, abs_tol=1e-12)
        endpoints.append(endpoint)
        for t in (0.03, 0.2, 0.6, 0.97):
            u = -log(t) + 2j * pi * k
            z = (u - 1) / (u + 1)
            cayley = (1 + z) / (1 - z)
            assert abs(complex_exp(-cayley) - t) < 2e-12
            assert abs(z) < 1
    assert len({(round(z.real, 12), round(z.imag, 12)) for z in endpoints}) == 17


def test_raw_sheetwise_crossing_width_has_no_label_only_bound() -> None:
    # This is the compact interior-rectangle model only; it is not a
    # complete KKL-marked lamination regression.
    a, b, theta = 0.8, 2.3, 0.7
    single_width = 2 * theta / (b - a)
    totals = [(2 * m + 1) * single_width for m in range(10)]
    assert all(right > left for left, right in zip(totals, totals[1:]))
    assert isclose(
        totals[-1],
        sum(single_width for _ in range(19)),
        abs_tol=1e-12,
    )


def test_pql_raw_untagged_path_image_collision() -> None:
    # Exact finite samples from the analytic collision model.  This checks
    # the formulas only; it does not promote the paths to KKL Waves.
    beta = pi / 50
    discriminant = 16 + 4 * 10004 * 5624
    t_star = (4 + sqrt(discriminant)) / 20008
    assert 0.5 < t_star < 1

    def z0(t: float) -> complex:
        return -1 + 2 * t + 100j * t

    def z_minus_one(t: float) -> complex:
        return -1 + 2 * t + 100j * (t - 1)

    for s in (0.01, 0.2, 0.49, 0.75 * t_star):
        assert 0 < s < t_star
        upper = z0(s)
        lower = z_minus_one(1 - s)
        assert abs(upper) < 75
        assert abs(lower) < 75
        assert abs(lower + upper) < 1e-12
        assert abs(lower * lower - upper * upper) < 1e-10
        assert upper.imag > 0
        assert lower.imag < 0


def test_singleton_untagged_image_does_not_bind_two_occurrences() -> None:
    retained_components = {
        ("minus", "sheet-0"): "terminal-wave",
        ("plus", "sheet-1"): "terminal-wave",
    }
    assert len(set(retained_components.values())) == 1
    assert len(retained_components) == 2
    # The singleton image remembers neither which occurrence was used nor
    # whether stagewise choices assemble into complete fiber-product paths.
    assert set(retained_components) != set(retained_components.values())


def test_endpoint_pair_does_not_determine_collar_path_class() -> None:
    endpoint_pair = ("inner-access", "outer-access")
    collar_paths = {
        (endpoint_pair, 0),  # zero winding
        (endpoint_pair, 1),  # one winding
    }
    assert len({pair for pair, _ in collar_paths}) == 1
    assert len(collar_paths) == 2


def main() -> None:
    tests = [
        test_product_orientation,
        test_typed_kkl_incidence_and_value_weights,
        test_open_endpoint_gauge,
        test_boolean_support_functor,
        test_zero_scc_and_extinction_examples,
        test_future_index_obstructions,
        test_counter_fiber_is_not_global_invariance,
        test_memory_projection_does_not_license_pumping,
        test_wad_output_is_not_transport_compatibility,
        test_signature_count_does_not_bound_dimension,
        test_corrected_clone_exponent_and_multiplier,
        test_virtual_limb_tree_bound,
        test_branch_parameter_mismatch,
        test_dyadic_fast_forward_fan_degree,
        test_endpoint_birth_accounting,
        test_attachment_support_reduction,
        test_corridor_attachment_transport,
        test_univalent_pair_transport_certificate,
        test_attachment_free_anchor_underdetermination,
        test_finite_attachment_orbit_closure,
        test_no_least_connected_carrier,
        test_protected_access_collision,
        test_quadratic_univalent_corridor_model,
        test_uptcr_record_threshold,
        test_uptcr_six_clause_gate,
        test_uptcr_parameter_basis_gate,
        test_uptcr_spine_fan_degree_quantifier,
        test_uptcr_fatal_collision_is_not_window_charge,
        test_uptcr_block_routes_are_inclusive,
        test_protected_ribbon_boundary_naturality,
        test_protected_connector_trace_gate,
        test_protected_connector_side_bound,
        test_protected_free_component_criterion,
        test_late_forbidden_insertion_splits_free_component,
        test_augmented_atom_common_domain,
        test_annular_obstacle_collision_audit,
        test_augmented_packet_closure_order_independence,
        test_augmented_packet_collision_and_port_persistence,
        test_individual_ports_localize_disjointly,
        test_horizon_first_inventory_extension,
        test_horizon_slice_stability_criterion,
        test_inventory_graph_does_not_choose_packet_labels,
        test_kkl_native_visit_stopping_index,
        test_resolved_wave_program_maximal_iterate_horizon,
        test_wave_final_root_closure_order_independence,
        test_wave_program_extension_requires_reaudit,
        test_unresolved_wave_branch_is_rejected,
        test_return_path_language_is_prefix_closed,
        test_prime_end_endpoint_refinement_criterion,
        test_marked_pair_boundary_phase_countermodel,
        test_access_orbit_closure_requires_phase_record,
        test_marked_enlargement_endpoint_naturality,
        test_return_base_changes_first_return_time,
        test_analytic_prefix_iterate_composition,
        test_demand_closed_unfolding_keeps_word_and_sheet,
        test_injective_atlas_enlargement_does_not_prove_no_birth,
        test_isotopic_return_bases_change_return_time,
        test_principal_return_critical_chronology,
        test_virtual_scale_selector_is_a_real_gate,
        test_first_decoration_escape_selector_is_least_event,
        test_critical_return_base_excludes_intermediate_cycle,
        test_raw_decoration_fan_has_exponential_access_growth,
        test_native_hubbard_vertex_package_has_unique_hull,
        test_injective_tree_transport_gives_exact_hull,
        test_folded_tree_transport_retains_excess,
        test_hubbard_hull_enlargement_has_one_gate,
        test_ambient_hubbard_tree_does_not_select_virtual_package,
        test_finite_terminal_labels_do_not_enumerate_cantor_addresses,
        test_cantor_quotient_requires_joint_observable_constancy,
        test_pullback_nesting_parent_differs_from_dynamic_shift,
        test_bigraded_parent_shift_square_commutes,
        test_binder_ledger_reachability_and_extension,
        test_pullback_end_compactification_prefix_convergence,
        test_pullback_gap_enlargement_and_collision_ledger,
        test_finite_cylinder_commuting_iterate_lift,
        test_target_address_requires_actual_uniqueness,
        test_future_observable_coordinate_shift,
        test_direct_decoration_gap_cells_separate_ancestors,
        test_component_forcing_does_not_supply_authorization,
        test_critical_cut_pointwise_word_conservation,
        test_critical_time_shear_degree_ladder,
        test_retimed_iterate_identity_is_only_algebraic,
        test_arbitrary_prime_end_marking_can_fail,
        test_interior_univalence_does_not_force_jordan_image,
        test_quadratic_base_change_loses_degree_off_spine,
        test_prime_end_embedding_uses_image_circle_not_target_circle,
        test_fixed_iterate_nested_set_extension,
        test_retention_boolean_is_not_a_geometric_certificate,
        test_boundary_critical_value_is_not_strict_exterior,
        test_nested_compact_equality_needs_hausdorff_gate,
        test_normalized_end_direct_limit_coordinate,
        test_shift_grading_conflict_requires_unfolding,
        test_scalar_neck_trace_mode_no_go,
        test_full_trace_rectangle_sharp_mode_bound,
        test_pulled_equipotential_arcs_do_not_form_serial_rectangle,
        test_positive_cell_resistance_does_not_force_finite_depth_margin,
        test_one_sided_transition_stability_needs_input_alignment,
        test_push5_contact_welding_no_go,
        test_contact_pair_graph_loses_atom_incidence,
        test_parametrized_lollipop_does_not_exhaust_geometric_trace,
        test_exponential_immersion_retains_infinite_phase_labels,
        test_raw_sheetwise_crossing_width_has_no_label_only_bound,
        test_pql_raw_untagged_path_image_collision,
        test_singleton_untagged_image_does_not_bind_two_occurrences,
        test_endpoint_pair_does_not_determine_collar_path_class,
        test_valid_binder_does_not_imply_terminal_noncollision,
        test_broken_cartesian_synchronization_is_rejected,
        test_independent_stage_parameters_are_rejected,
        test_filter_loss_is_rejected,
        test_missing_parent_access_is_rejected,
        test_merged_complete_components_are_rejected,
        test_endpoint_labels_do_not_erase_homotopy_word,
        test_nonpositive_horizon_is_rejected,
        test_nonproper_core_is_rejected,
        test_unmarked_base_trace_is_rejected,
        test_expanded_route_uses_endpoint_semantics,
        test_terminal_noncollision_is_a_separate_positive_check,
        test_valid_nested_chain,
        test_proper_window_is_allowed,
        test_missing_full_extension_is_rejected,
        test_nonproper_full_extension_is_rejected,
        test_segmented_filter_failure_is_rejected,
        test_predecessor_mismatch_is_rejected,
        test_invalid_window_is_rejected,
        test_pair_validity_does_not_imply_terminal_noncollision,
        test_strict_shortness_slack,
        test_terminal_constant_is_admissible_and_charges_vertical_term,
        test_relative_width_cannot_absorb_fixed_constant,
        test_theta_transfers_shortness_and_terminality,
        test_disjoint_B_survivors_are_short,
        test_degree_two_horizon_radius_and_collar_bound,
        test_qualitative_positive_modulus_is_not_uniform,
        test_selected_crossing_does_not_equal_all_continuation_failures,
        run_stationary_route_exit_schema,
        run_stationary_paired_wave_response,
        run_ledger_tooling_regressions,
    ]
    for test in tests:
        test()
        print(f"PASS {test.__name__}")
    print("diagnostic transfer regressions: all passed")


if __name__ == "__main__":
    main()
