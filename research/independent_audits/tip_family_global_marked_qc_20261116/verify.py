#!/usr/bin/env python3
"""Read-only finite regression for the *unproved* global marked-QC interface.

Re-executes the archived depth-two nine-case grid and the distinct (3,3,3)
packet with exact Fraction/2^-512 intervals.  It NEVER constructs a QC map,
identifies prime ends, proves a KKL Wave bijection, or evaluates a numerical K'.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as Q
import hashlib
import importlib.util
from pathlib import Path
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
AUDITS = HERE.parent
DEPTH_TWO = AUDITS / "tip_family_renormalization_depth_20261116" / "verify.py"
DEPTH_THREE = AUDITS / "tip_family_all_depths_20261116" / "verify.py"
PREVIOUS_QC = AUDITS / "tip_family_depth_uniform_qc_20261116" / "verify.py"

# Every value is an integer, on the explicitly identified indicated grid.
# Entry: two *strict* 1/100000 enclosures (radial witness, plane envelope),
# then strict 1/1000000 lower bounds for the three Rouché margins.
# These numbers are from the unchanged merged depth-two NOTE/verify.py.
GRID = {
    (3, 3): ((25224, 25225), (76475, 76476), (127464, 6308, 170868)),
    (3, 4): ((25854, 25855), (77250, 77251), (114089, 1837, 243878)),
    (3, 5): ((25999, 26000), (77430, 77431), (110133, 8030, 261699)),
    (4, 3): ((25179, 25180), (76418, 76419), (45190, 2828, 174909)),
    (4, 4): ((25848, 25849), (77243, 77244), (41404, 978, 245444)),
    (4, 5): ((25999, 26000), (77431, 77432), (40344, 2609, 262575)),
    (5, 3): ((25170, 25171), (76406, 76407), (111807, 817, 175214)),
    (5, 4): ((25847, 25848), (77242, 77243), (110887, 286, 245758)),
    (5, 5): ((26000, 26001), (77431, 77432), (110632, 698, 262640)),
}
THREE_FLOORS = {
    "rouche1": 127470,
    "rouche2": 6346,
    "rouche3": 3900,
    "normalized_third": 172673,
    "radial_width_lower": 252105,
}
THREE_CEILING = 764704
EXPECTED_BLOCKS = (
    (18, 19, 0, 1, 2), (3, 4), (5,), (6,), (7, 8, 9),
    (10,), (11, 12, 13), (14,), (15,), (16, 17),
)


class CertificateError(AssertionError):
    """Finite data changed; NOT an analytic counterexample."""


def require(ok: bool, message: str) -> None:
    if not ok:
        raise CertificateError(message)


def exact(x: Q | int | str) -> Q:
    require(not isinstance(x, (bool, float)), "inexact/boolean input")
    try:
        return Q(x)
    except (ValueError, TypeError, ZeroDivisionError) as error:
        raise CertificateError("invalid rational") from error


def conditional_widths(lower: Q | int | str,
                       upper: Q | int | str,
                       K: Q | int | str,
                       depth: int = 1) -> tuple[Q, Q]:
    """Algebra ONLY: two-sided family transport at one level is a HYPOTHESIS."""
    lo, hi, k = exact(lower), exact(upper), exact(K)
    require(type(depth) is int and depth > 0, "invalid depth")
    require(Q(0) < lo < hi and k >= 1, "invalid widths or K")
    return lo / k, hi * k


def conditional_crest(lower: Q | int | str,
                      upper: Q | int | str,
                      K: Q | int | str) -> tuple[Q, Q]:
    """Both positive parent and descendant families are assumed transported."""
    lo, hi, k = exact(lower), exact(upper), exact(K)
    require(Q(0) < lo < hi and k >= 1, "invalid crest ratio or K")
    return lo / (k*k), hi * k*k


def annulus_forced_K(source_modulus: Q | int | str,
                     target_modulus: Q | int | str) -> Q:
    """QC modulus obstruction for boundary-component-preserving ANNULI.

    Abstract countermodel to a modulus-only global bound, not a KKL example.
    """
    a, b = exact(source_modulus), exact(target_modulus)
    require(a > 0 and b > 0, "annulus moduli must be positive")
    return max(a / b, b / a)


def check_algebra() -> None:
    for k in (Q(1), Q(5, 4), Q(2), Q(17, 3)):
        for period, lower in ((3, Q(1, 4)), (12, Q(1, 4)),
                              (13, Q(13, 50)), (300, Q(13, 50))):
            bound = conditional_widths(lower, Q(39, 50), k)
            require(bound == conditional_widths(lower, Q(39, 50), k, 99999),
                    "depth was multiplied into K")
            require(bound == (lower/k, Q(39, 50)*k),
                    "wrong conditional width constant")
        require(conditional_crest(Q(5676, 10000), Q(5684, 10000), k) ==
                (Q(5676, 10000)/(k*k), Q(5684, 10000)*k*k),
                "a crest ratio loses K squared")
    for n in (2, 3, 20, 10000):
        require(annulus_forced_K(1, n) == n, "modulus obstruction lost")


def _strict_interval(value: object, numbers: tuple[int, int],
                     scale: int, label: str) -> None:
    require(isinstance(value, (tuple, list)) and len(value) == 2,
            label + ": missing interval")
    lo, hi = value
    require(type(lo) is Q and type(hi) is Q,
            label + ": not exact Fractions")
    require(Q(numbers[0], scale) < lo <= hi < Q(numbers[1], scale),
            label + ": outside locked strict interval")


def check_row(pair: tuple[int, int], record: dict) -> None:
    """Validate an archived exact output; no float conversions or new geometry."""
    require(type(pair) is tuple and len(pair) == 2
            and all(type(n) is int for n in pair) and pair in GRID,
            "unsupported depth-two grid key")
    require(type(record) is dict, "invalid depth-two record")
    require(record.get("pair") == pair, "wrong grid row/period")
    rad5, plane5, gaps = GRID[pair]
    _strict_interval(record.get("radial"), rad5, 100000, "radial witness")
    _strict_interval(record.get("qplane"), plane5, 100000, "plane envelope")
    rad_bins, plane_bins = record.get("radial5"), record.get("qplane5")
    require(type(rad_bins) in (tuple, list) and tuple(rad_bins) == rad5,
            "radial grid bins drifted")
    require(type(plane_bins) in (tuple, list) and tuple(plane_bins) == plane5,
            "plane grid bins drifted")
    for key, floor in zip(
            ("rouche1", "rouche2", "rouche3_normalized_lower"), gaps):
        x = record.get(key)
        require(type(x) is Q and x > Q(floor, 1000000),
                "Rouché gap drifted: " + key)
    require(record["radial"][0] > Q(1, 4)
            and record["qplane"][1] < Q(31, 40)
            and record["radial"][1] < record["qplane"][0],
            "depth-two physical width sandwich failed")
    require(record.get("root_chart_radius") == Q(1, 10**80),
            "depth-two isolating chart changed")


def check_three(record: dict) -> None:
    for key, floor in THREE_FLOORS.items():
        x = record.get(key)
        require(type(x) is Q and x > Q(floor, 1000000),
                "depth-three strict lower margin changed: " + key)
    upper = record.get("plane_width_upper")
    require(type(upper) is Q and upper < Q(THREE_CEILING, 1000000),
            "depth-three upper envelope changed")
    require(record.get("root_chart") == Q(1, 10**80),
            "depth-three chart changed")
    require(record["radial_width_lower"] < upper < Q(31, 40),
            "depth-three physical sandwich contradicted")
    # Deliberately do NOT claim that W* is exactly either bound, or >0.26.


def _load(name: str, path: Path):
    require(path.is_file(), "missing unchanged archived verifier: " + str(path))
    spec = importlib.util.spec_from_file_location(name, path)
    require(spec is not None and spec.loader is not None, "bad import spec")
    mod = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = mod  # needed for dataclass annotation resolution
    spec.loader.exec_module(mod)
    return mod


def _digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_marking(d2, d3, qc) -> None:
    for source in (d2, d3, qc):
        require(source.BLOCKS == EXPECTED_BLOCKS,
                "archived 10/20 immersion table disagreement")
    d2.proper_atom_tables()
    d3.check_marked_tables()
    qc.marked_table_check()
    cover = tuple(s % 10 for s in range(20))
    immersion = tuple(next(i for i, block in enumerate(EXPECTED_BLOCKS)
                           if s in block) for s in range(20))
    require(cover != immersion and cover[10] == 0 and immersion[10] == 5,
            "covering f_* incorrectly identified with immersion iota*")
    require(qc.PAIRS == ((3, 1), (19, 17), (3, 17))
            and qc.marked_table_check()["source_spans"] == (3, 3, 7)
            and qc.marked_table_check()["target_spans"] == (3, 3, 5),
            "proper path source/target spans changed")
    require(qc.EDGE_SIDES == ((1, "E0"), (9, "E0")),
            "opposite accesses to same edge miscounted")


def verify_archives() -> None:
    paths = (DEPTH_TWO, DEPTH_THREE, PREVIOUS_QC)
    before = tuple(_digest(p) for p in paths)
    d2 = _load("_global_qc_depth_two", DEPTH_TWO)
    d3 = _load("_global_qc_depth_three", DEPTH_THREE)
    qc = _load("_global_qc_previous", PREVIOUS_QC)
    check_marking(d2, d3, qc)
    require(set(d2.SEEDS) == set(GRID), "nine-case depth-two seed grid drifted")
    for pair in sorted(GRID):
        row = d2.verify_case(*pair)  # full original rational/interval calculations
        check_row(pair, row)
        require(row["seed"] == Q(d2.SEEDS[pair]), "unexpected parameter locator")
        print("PASS exact depth-two", pair, "strict radial/plane/gap grid")
    require(d3.PERIODS == (3, 9, 27), "wrong depth-three periods")
    require(d3.RADII == (Q(1, 4), Q(1, 40), Q(1, 250)),
            "depth-three disks changed")
    check_three(d3.verify())
    print("PASS exact depth-three (3,3,3) distinct strict rational packet")
    require(tuple(_digest(p) for p in paths) == before,
            "archived source modified during audit")


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--quick", action="store_true",
                    help="only conditional algebra and abstract modulus obstruction")
    args = ap.parse_args()
    check_algebra()
    print("PASS exact conditional K' and K'^2 arithmetic, no depth exponent")
    print("PASS annular countermodel: no global K'(mu) from local data alone")
    if not args.quick:
        verify_archives()
    print("NOT CERTIFIED: global marked KKL QC map or numerical K',")
    print("prime-end/Wave transport, infinite-depth Wave convergence")


if __name__ == "__main__":
    main()
