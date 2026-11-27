#!/usr/bin/env python3
"""Regenerate exact global real-tip isolation certificates.

The decimal constants locate small candidate intervals only. Their endpoint
signs, derivatives and complete critical words are verified by integer interval
arithmetic. Every point of [-2, 0] is covered by a recursively checked binary
tree. The generated Lean declarations recheck all arithmetic in the kernel;
this Python program is not part of the logical trust base.

Default execution is read-only. Use --write to replace the generated Lean file.
"""

from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
OUTPUT_DIR = ROOT / "formalization/weighted"
MODULES = {
    3: "GlobalTipCertificates3To4",
    5: "GlobalTipCertificates5To6",
    7: "GlobalTipCertificates7To8",
    9: "GlobalTipCertificates9To10",
    11: "GlobalTipCertificates",
}
SCALE = 1 << 128
SEEDS = {
    3: "-1.786510544544324757385260673471213673058457671889172800031923968334629798587697269507048968639156733",
    4: "-1.942554171494761905319728559547351970316877794253756256973061644721007908220533846556129430732097156",
    5: "-1.985528169705348810408255730556821748277263841949252553593917274749073066379677891609603820336856318",
    6: "-1.996382511718412027950049688816515039904858979750298286593034926678792080923860935932139817781617068",
    7: "-1.99909607830917598002359967040562747450315031202203453414490734530886689705706443584075484634242529",
    8: "-1.99977407339705875086923341331568799685514252038080974798691863676382684508119126543885186585434088",
    9: "-1.99994352330879102254975391082738335395352978817090499897525072423167823633706849247069259463644468",
    10: "-1.99998588123682174254843383503975840503292143775299401058889825653946965600383848213765034339890565",
    11: "-1.999996470341035272735632678015004938386461804580811692099169946758788547010051826504894628853093167",
    12: "-1.999999117587637481776828101553703232713431093876163616822020428055010613627327045591565019864984472",
}

Bounds = tuple[int, int]


def floor_fraction(x: Fraction) -> int:
    return x.numerator // x.denominator


def ceil_fraction(x: Fraction) -> int:
    return -((-x.numerator) // x.denominator)


def add(a: Bounds, b: Bounds) -> Bounds:
    return a[0] + b[0], a[1] + b[1]


def mul(a: Bounds, b: Bounds) -> Bounds:
    products = tuple(x * y for x in a for y in b)
    return min(products) // SCALE, -((-max(products)) // SCALE)


def square(a: Bounds) -> Bounds:
    products = a[0] ** 2, a[1] ** 2
    lower = 0 if a[0] <= 0 <= a[1] else min(products)
    return lower // SCALE, -((-max(products)) // SCALE)


def positive(p: int, j: int) -> bool:
    if j % p == 0:
        return j // p in (1, 4, 6)
    return j % p != 1


def required_sign_fails(p: int, j: int, b: Bounds) -> bool:
    return b[1] <= 0 if positive(p, j) else 0 <= b[0]


def required_sign_holds(p: int, j: int, b: Bounds) -> bool:
    return 0 < b[0] if positive(p, j) else b[1] < 0


def excludes_zero(b: Bounds) -> bool:
    return 0 < b[0] or b[1] < 0


def trace(c: Bounds, n: int, derivative: bool = False) -> tuple[list[Bounds], list[Bounds]]:
    xs: list[Bounds] = [(0, 0)]
    ds: list[Bounds] = [(0, 0)]
    for _ in range(n):
        if derivative:
            ds.append(add(mul((2 * xs[-1][0], 2 * xs[-1][1]), ds[-1]), (SCALE, SCALE)))
        xs.append(add(square(xs[-1]), c))
    return xs, ds


def deflated(xs: list[Bounds], p: int) -> Bounds:
    result = SCALE, SCALE
    for j in range(3 * p):
        result = mul(result, add(xs[3 * p + j], xs[j]))
    return add(result, (2 * SCALE, 2 * SCALE))


def seed_box(p: int) -> Bounds:
    locator = Fraction(SEEDS[p])
    halfwidth = Fraction(1, 32 * 16 ** p)
    return floor_fraction((locator - halfwidth) * SCALE), ceil_fraction((locator + halfwidth) * SCALE)


@dataclass(frozen=True)
class Node:
    kind: str
    value: int = 0
    left: Node | None = None
    right: Node | None = None


def build_tree(p: int, seed: Bounds, c: Bounds, depth: int = 0) -> Node:
    if seed[0] <= c[0] and c[1] <= seed[1]:
        return Node("keep")
    xs: list[Bounds] = [(0, 0)]
    for j in range(1, 6 * p + 1):
        xs.append(add(square(xs[-1]), c))
        if required_sign_fails(p, j, xs[-1]):
            return Node("wrongSign", j)
        # A failed exploration is subdivided, never certified. This cap only
        # prevents unneeded huge integer squarings on very broad boxes.
        if max(abs(x) for x in xs[-1]) > 8 * SCALE:
            break
    if len(xs) == 6 * p + 1:
        if excludes_zero(add(xs[3 * p], xs[6 * p])):
            return Node("nonzero")
        if excludes_zero(deflated(xs, p)):
            return Node("deflated")
    if depth >= 120 or c[1] - c[0] <= 1:
        raise AssertionError(f"Unresolved parameter interval p={p}, depth={depth}, C={c}")
    if c[0] < seed[0] < c[1]:
        midpoint = seed[0]
    elif c[0] < seed[1] < c[1]:
        midpoint = seed[1]
    else:
        midpoint = (c[0] + c[1]) // 2
    return Node("split", midpoint,
                build_tree(p, seed, (c[0], midpoint), depth + 1),
                build_tree(p, seed, (midpoint, c[1]), depth + 1))


def check_tree(p: int, seed: Bounds, c: Bounds, tree: Node) -> None:
    if tree.kind == "split":
        assert c[0] <= tree.value <= c[1]
        assert tree.left is not None and tree.right is not None
        check_tree(p, seed, (c[0], tree.value), tree.left)
        check_tree(p, seed, (tree.value, c[1]), tree.right)
    elif tree.kind == "keep":
        assert seed[0] <= c[0] and c[1] <= seed[1]
    elif tree.kind == "wrongSign":
        assert 1 <= tree.value <= 6 * p
        xs, _ = trace(c, tree.value)
        assert required_sign_fails(p, tree.value, xs[-1])
    else:
        xs, _ = trace(c, 6 * p)
        if tree.kind == "nonzero":
            assert excludes_zero(add(xs[3 * p], xs[6 * p]))
        elif tree.kind == "deflated":
            assert excludes_zero(deflated(xs, p))
        else:
            raise AssertionError(f"Unknown leaf {tree.kind}")


def check_seed(p: int, seed: Bounds) -> None:
    assert 0 < SCALE and -2 * SCALE < seed[0] < seed[1] < 0
    xs, ds = trace(seed, 6 * p, derivative=True)
    assert all(required_sign_holds(p, j, xs[j]) for j in range(1, 6 * p + 1))
    assert 0 < add(xs[p], xs[2 * p])[0]
    assert add(ds[3 * p], ds[6 * p])[1] < 0
    left, _ = trace((seed[0], seed[0]), 6 * p)
    right, _ = trace((seed[1], seed[1]), 6 * p)
    assert 0 < add(left[3 * p], left[6 * p])[0]
    assert add(right[3 * p], right[6 * p])[1] < 0


def render_tree(tree: Node, indent: int = 2) -> str:
    prefix = " " * indent
    if tree.kind == "split":
        assert tree.left is not None and tree.right is not None
        return (f"{prefix}(.split ({tree.value})\n"
                f"{render_tree(tree.left, indent + 2)}\n"
                f"{render_tree(tree.right, indent + 2)})")
    if tree.kind == "wrongSign":
        return f"{prefix}(.wrongSign {tree.value})"
    return f"{prefix}.{tree.kind}"


def statistics(tree: Node) -> tuple[Counter[str], int]:
    if tree.kind == "split":
        assert tree.left is not None and tree.right is not None
        left, dl = statistics(tree.left)
        right, dr = statistics(tree.right)
        return left + right, 1 + max(dl, dr)
    return Counter({tree.kind: 1}), 0


def module_header(dependency: str) -> list[str]:
    return [
        f"import {dependency}\n",
        "/-!\n# Exhaustive real parameter certificates for the selected tips, periods 3 through 12\n\n",
        "Generated by `contributions/global_tip_kneading_20261126/generate_certificates.py`.\n",
        "The trees cover the entire closed interval [-2, 0]. Their leaves prove either\n",
        "a wrong critical-orbit sign, a nonzero critical relation, a nonzero exact\n",
        "deflated relation, or membership in the retained root interval.\n",
        "Every numerical certificate below is rechecked by kernel reduction.\n-/\n\n",
        "namespace LoopsGlobalTip\n\n",
        "open LoopsFormal.Period27 LoopsFormal.DepthThree\n\n",
        "set_option maxRecDepth 32768\nset_option maxHeartbeats 0\n\n",
    ]


def generate() -> dict[str, str]:
    outputs: dict[str, str] = {}
    module = MODULES[3]
    parts = module_header("GlobalTipIsolation") + [
        f"def tipScale : Int := {SCALE}\n\n",
        "/-- The common exact arithmetic scale is positive. -/\n",
        "theorem tipScale_pos : 0 < tipScale := by decide +kernel\n\n",
    ]
    for p in range(3, 13):
        if p in MODULES and p != 3:
            parts.append("end LoopsGlobalTip\n")
            outputs[module] = "".join(parts)
            previous = module
            module = MODULES[p]
            parts = module_header(previous)
        seed = seed_box(p)
        check_seed(p, seed)
        tree = build_tree(p, seed, (-2 * SCALE, 0))
        check_tree(p, seed, (-2 * SCALE, 0), tree)
        counts, depth = statistics(tree)
        print(f"p={p}: {sum(counts.values())} certified leaves; maximum depth {depth}; "
              f"{dict(sorted(counts.items()))}")
        parts.extend([
            f"/-- The retained period-{p} interval in units of `1 / tipScale`. -/\n",
            f"def seed{p} : Bounds := ⟨{seed[0]}, {seed[1]}⟩\n\n",
            f"/-- Complete parameter cover for period {p}; {sum(counts.values())} leaves. -/\n",
            f"def cover{p} : CoverTree :=\n{render_tree(tree)}\n\n",
            f"/-- Kernel verification of every exclusion and every covering split. -/\n",
            f"theorem cover{p}_checked :\n",
            f"    coverCheck tipScale {p} ⟨-2 * tipScale, 0⟩ seed{p} cover{p} = true := by\n",
            "  decide +kernel\n\n",
            f"/-- Opposite endpoint signs and a strict derivative bound on the entire interval. -/\n",
            f"theorem seed{p}_root : RootCertificate tipScale {p} seed{p} := by\n",
            "  decide +kernel\n\n",
            f"/-- Every intermediate critical iterate has the prescribed strict sign. -/\n",
            f"theorem seed{p}_signs : signBoxCheck tipScale {p} seed{p} = true := by\n",
            "  decide +kernel\n\n",
            f"/-- The endpoint return stays strictly above the reflected critical value. -/\n",
            f"theorem seed{p}_invariant :\n",
            f"    0 < (addBounds (orbitBound tipScale {p} seed{p} {p})\n",
            f"      (orbitBound tipScale {p} seed{p} {2*p})).lo := by\n",
            "  decide +kernel\n\n",
            f"/-- The root interval lies strictly inside the globally covered parameter interval. -/\n",
            f"theorem seed{p}_inside : -2 * tipScale < seed{p}.lo ∧ seed{p}.hi < 0 := by\n",
            "  decide +kernel\n\n",
        ])
    parts.append("end LoopsGlobalTip\n")
    outputs[module] = "".join(parts)
    return outputs


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="write the generated Lean source")
    args = parser.parse_args()
    outputs = generate()
    for module, expected in outputs.items():
        output = OUTPUT_DIR / (module + ".lean")
        if args.write:
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_text(expected, encoding="utf-8")
            print(f"Wrote {output.relative_to(ROOT)}")
        elif not output.is_file() or output.read_text(encoding="utf-8") != expected:
            raise SystemExit(f"Generated {module} differs; run with --write after reviewing the change.")
    if not args.write:
        print("PASS: exact root, full-word, and complete [-2,0] cover certificates reproduced.")


if __name__ == "__main__":
    main()
