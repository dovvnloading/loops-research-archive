"""Finite diagnostic for the marked-tree pruning lemma.

The analytic proof is in kkl_stationary_n2_selected_predecessor_endpoint.md.
This script only exhausts small finite labelled trees and marked subsets.
"""

from __future__ import annotations

from itertools import product


def edges_from_prufer(word: tuple[int, ...], n: int) -> list[tuple[int, int]]:
    degree = [1] * n
    for vertex in word:
        degree[vertex] += 1

    edges: list[tuple[int, int]] = []
    for vertex in word:
        leaf = min(index for index, value in enumerate(degree) if value == 1)
        edges.append((leaf, vertex))
        degree[leaf] -= 1
        degree[vertex] -= 1

    leaves = [index for index, value in enumerate(degree) if value == 1]
    edges.append((leaves[0], leaves[1]))
    return edges


def adjacency(n: int, edges: list[tuple[int, int]]) -> list[set[int]]:
    graph = [set() for _ in range(n)]
    for left, right in edges:
        graph[left].add(right)
        graph[right].add(left)
    return graph


def component(
    graph: list[set[int]], start: int, removed_vertex: int | None = None
) -> set[int]:
    seen = {start}
    stack = [start]
    while stack:
        vertex = stack.pop()
        for neighbor in graph[vertex]:
            if neighbor == removed_vertex or neighbor in seen:
                continue
            seen.add(neighbor)
            stack.append(neighbor)
    return seen


def full_marked_hull(
    n: int, edges: list[tuple[int, int]], graph: list[set[int]], marks: set[int]
) -> bool:
    for left, right in edges:
        # Delete this edge without mutating the shared graph.
        stack = [left]
        left_side = {left}
        while stack:
            vertex = stack.pop()
            for neighbor in graph[vertex]:
                if {vertex, neighbor} == {left, right} or neighbor in left_side:
                    continue
                left_side.add(neighbor)
                stack.append(neighbor)
        right_side = set(range(n)) - left_side
        if not (marks & left_side) or not (marks & right_side):
            return False
    return True


def check_tree(n: int, edges: list[tuple[int, int]]) -> int:
    graph = adjacency(n, edges)
    checked = 0
    for mask in range(1, 1 << n):
        marks = {vertex for vertex in range(n) if mask & (1 << vertex)}
        if not full_marked_hull(n, edges, graph, marks):
            continue
        checked += 1

        # Vertex points.
        for removed in range(n):
            remaining = set(range(n)) - {removed}
            while remaining:
                start = next(iter(remaining))
                side = component(graph, start, removed_vertex=removed)
                assert side & marks
                remaining -= side

        # Interior points of edges: deleting an edge gives the two sides.
        for left, right in edges:
            left_side = {left}
            stack = [left]
            while stack:
                vertex = stack.pop()
                for neighbor in graph[vertex]:
                    if {vertex, neighbor} == {left, right} or neighbor in left_side:
                        continue
                    left_side.add(neighbor)
                    stack.append(neighbor)
            right_side = set(range(n)) - left_side
            assert left_side & marks
            assert right_side & marks
    return checked


def run() -> None:
    tree_count = 0
    marked_hull_count = 0
    for n in range(2, 8):
        for word in product(range(n), repeat=n - 2):
            edges = edges_from_prufer(word, n)
            tree_count += 1
            marked_hull_count += check_tree(n, edges)

    # Sharpness witness: a connected middle subpath can contain no mark.
    path_edges = [(0, 1), (1, 2), (2, 3)]
    path_graph = adjacency(4, path_edges)
    marks = {0, 3}
    assert full_marked_hull(4, path_edges, path_graph, marks)
    middle_subpath_vertices = {1, 2}
    assert not (middle_subpath_vertices & marks)

    # One-gate pullback incidence is still insufficient.  Vertices
    # 0--1--2 form the original marked tree, with marks only at 0 and 2.
    # Vertex 3 is a pulled edge attached at the unmarked interior gate 1.
    # The selected pulled component {1,3} has exactly one attachment to
    # the original tree but no marked-core contact.
    original_tree = {0, 1, 2}
    core_marks = {0, 2}
    pulled_component = {1, 3}
    attachments = pulled_component & original_tree
    assert attachments == {1}
    assert not (pulled_component & core_marks)

    print("PASS: every tested terminal side contains a marked vertex")
    print("PASS: connected middle-subpath counterexample has no marked vertex")
    print("PASS: one-gate attachment at an unmarked vertex has no marked contact")
    print(f"trees checked: {tree_count}")
    print(f"full marked hulls checked: {marked_hull_count}")


if __name__ == "__main__":
    run()
