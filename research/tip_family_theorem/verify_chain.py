#!/usr/bin/env python3
"""Read-only, hostile cross-source audit for the near-minus-two real tip family.

Default: run EVERY listed upstream certificate/verifier, then independently check
cross-file conventions, interval overlap, typed marking, widths and boundaries.
--consistency-only: fast structural audit, intended for mutation tests.
--with-tests: also run all upstream adversarial Python suites.

This does NOT formally verify the named analytic/topological theorems.
It never invokes a source verifier's --write option and checks immutable-file
SHA-256 snapshots before and after all subprocesses. Python stdlib only.
"""
from __future__ import annotations

import argparse
import copy
import hashlib
import json
import os
from fractions import Fraction as F
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
AUDITS = ROOT / "research" / "independent_audits"
NATIVE = ROOT / "research" / "native_wave_transfer"
DIRS = {
    "uniform": "real_primitive_tip_family_uniform_20261116",
    "finite": "real_primitive_tip_family_unconditional_20261116",
    "large": "real_primitive_tip_family_all_p_20261116",
    "prime": "real_primitive_tip_family_prime_end_identification_20261116",
    "canonical": "real_primitive_tip_family_canonical_width_20261116",
    "crest_fixed": "crest_transport_tip_family_20261116",
    "crest_opt": "crest_transport_asymptotics_20261116",
}
TARGET_CUTS = ["x5p", "x3p", "x6p", "alpha", "x4p"]
SOURCE_CUTS = [
    "-x4p", "x2p", "x5p", "-alpha", "x3p", "x6p",
    "alpha", "-x5p", "-x2p", "x4p",
]
TARGET_NAMES = [
    "K2_terminal", "edge_K2_K0_upper", "K0_upper",
    "edge_K0_alpha_upper", "edge_alpha_K1_upper", "K1_terminal",
    "edge_alpha_K1_lower", "edge_K0_alpha_lower", "K0_lower",
    "edge_K2_K0_lower",
]
BLOCKS = [
    [18, 19, 0, 1, 2], [3, 4], [5], [6], [7, 8, 9],
    [10], [11, 12, 13], [14], [15], [16, 17],
]
COVER = [i % 10 for i in range(20)]
MATRIX = [[0, 0, 1], [1, 0, 1], [1, 1, 0]]
ATTACHED = [19, 0, 1]
CROSSING = [[3, 1], [19, 17]]
AVOIDING = [3, 17]
PUSHED_CROSSING = [[3, 1], [9, 7]]
PUSHED_AVOIDING = [3, 7]
TARGET_ZERO = [0, 2, 5, 8]
SOURCE_ZERO = [0, 1, 2, 5, 10, 15, 18, 19]
COVER_ZERO = [0, 2, 5, 8, 10, 12, 15, 18]
MANIFESTS = {
    3: NATIVE / "experiment_manifests" / "tip_pr68.json",
    4: NATIVE / "experiment_manifests" / "primitive4_tip12.json",
}
SCRIPT_COMMANDS = [
    ("native p=3 PR68", "research/native_wave_transfer/regenerate.py", ["--check"]),
    ("native p=4", "research/native_wave_transfer/regenerate_period4.py", ["--check"]),
    ("original KKL p=3", "research/independent_audits/verify_tip_KKL_tree_marked_breakage.py",
     ["--check-manifest"]),
] + [
    (key, f"research/independent_audits/{name}/verify.py", [])
    for key, name in DIRS.items()
]
READ_ONLY_SUFFIXES = {".py", ".md", ".json", ".lean", ".toml", ".yml", ".yaml"}
READ_ONLY_TREES = [NATIVE] + [AUDITS / name for name in DIRS.values()]
READ_ONLY_FILES = [
    ROOT / "results/tip_root_interval_geometry.json",
    ROOT / "results/tip_KKL_tree_marked_breakage_20261109.json",
]


def need(ok: bool, label: str) -> None:
    if not ok:
        raise AssertionError(f"TIP FAMILY CHAIN FAILED: {label}")


def packet(path: Path) -> dict:
    need(path.is_file(), f"missing dependency {path}")
    return json.loads(path.read_text(encoding="utf-8"))


def source_file(name: str, file: str = "results.json") -> Path:
    return AUDITS / DIRS[name] / file


def spans(n: int, a: int, b: int) -> int:
    """Inclusive shortest-arc length; this counts both endpoint atoms."""
    need(0 <= a < n and 0 <= b < n and a != b, "invalid arc endpoints")
    return 1 + min((b - a) % n, (a - b) % n)


def interval_from_bracket(row: dict, key: str) -> tuple[F, F]:
    obj = row[key]
    if isinstance(obj, list) and key.startswith("parameter_bracket_2pow"):
        k = int(key.removeprefix("parameter_bracket_2pow"))
        need(len(obj) == 2, f"{key}: wrong dyadic list length")
        lo, hi = obj
    else:
        k = obj["denominator_power_of_two"]
        lo, hi = obj["lower_numerator"], obj["upper_numerator"]
    need(isinstance(k, int) and k > 0, f"{key}: invalid dyadic scale")
    need(isinstance(lo, int) and isinstance(hi, int) and hi == lo + 1,
         f"{key}: not an adjacent dyadic bracket")
    return F(lo, 2**k), F(hi, 2**k)


def intervals_overlap(a: tuple[F, F], b: tuple[F, F]) -> bool:
    return max(a[0], b[0]) < min(a[1], b[1])


def numeric_interval(lo: int, hi: int, scale: int) -> tuple[F, F]:
    need(isinstance(lo, int) and isinstance(hi, int) and lo < hi, "bad numeric enclosure")
    return F(lo, scale), F(hi, scale)


def substitute_cut(s: str, p: int) -> str:
    # The symbol x_j always means f^j(0), not G^j(0).
    if "x" not in s:
        return s
    neg = s.startswith("-")
    token = s[1:] if neg else s
    need(token.startswith("x") and token.endswith("p"), f"unrecognized cut {s}")
    integer = int(token[1:-1]) * p
    return ("-" if neg else "") + "x" + str(integer)


def matmul(a: list[list[int]], b: list[list[int]]) -> list[list[int]]:
    return [[sum(a[i][k] * b[k][j] for k in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]


def edge_occurrences() -> list[list[int]]:
    """Derive M from images of five ordered cut positions; count physical edges."""
    cut_images = [2, 4, 4, 3, 0]
    old_edges = [(0, 1), (2, 3), (3, 4)]
    m = [[0] * 3 for _ in range(3)]
    for j, (a, b) in enumerate(old_edges):
        lo, hi = sorted([cut_images[a], cut_images[b]])
        for i, (c, d) in enumerate(old_edges):
            m[i][j] = int(lo <= c and d <= hi)
    return m


def verify_common(common: dict) -> None:
    need(common["target_cuts"] == TARGET_CUTS, "five target cuts/index conventions")
    need(common["source_cuts"] == SOURCE_CUTS, "ten ordered inverse source cuts")
    need((common["target_atoms"], common["source_atoms"],
          common["outer_component_atom"]) == (10, 20, 1),
         "inner atom counts or one whole outer atom")
    need(common["covering_f_star"] == COVER, "degree-two covering action")
    need(common["immersion_iota_pullback_blocks"] == BLOCKS, "distinct immersion blocks")
    need(common["attached_source_sides"] == ATTACHED, "one attachment source sides")
    need(common["proper_crossing_pairs"] == CROSSING, "crossing pair sequence")
    need(common["proper_avoiding_pair"] == AVOIDING, "avoiding pair")
    need(common["cover_pushed_crossing_pairs"] == PUSHED_CROSSING,
         "covering-pushed crossing pairs")
    need(common["cover_pushed_avoiding_pair"] == PUSHED_AVOIDING,
         "covering-pushed avoiding pair")
    need(common["old_edge_matrix_output_rows_input_cols"] == MATRIX, "edge matrix")
    need(common["target_zero_edge_atoms"] == TARGET_ZERO, "atomic zero-edge target")
    need((common["parent_crest"], common["child_crests"]) == (0, [2, 8]),
         "zero-edge closed crests")
    need(common["perron_root"] == "(1+sqrt(5))/2", "Perron expression")
    need(common["harmonic_width_coefficients"] == {"parent": "1/2", "each_child": "1"},
         "symbolic harmonic coefficients")

    need(sum((len(row) for row in BLOCKS)) == 20, "immersion lengths total")
    need([len(row) for row in BLOCKS] == [5, 2, 1, 1, 3, 1, 3, 1, 1, 2],
         "immersion block lengths")
    need(sorted(x for row in BLOCKS for x in row) == list(range(20)),
         "blocks must partition all 20 atoms exactly once")
    need(all(any(x in BLOCKS[i] for x in ATTACHED) == (i == 0)
             for i in range(10)), "only P0 hosts attachment")
    need(all(x not in (BLOCKS[0][0], BLOCKS[0][-1]) for x in ATTACHED),
         "attached sides must not be P0 end atoms")
    need(COVER != [next(i for i, b in enumerate(BLOCKS) if x in b)
                   for x in range(20)], "covering and immersion were conflated")
    need([[COVER[a], COVER[b]] for a, b in CROSSING] == PUSHED_CROSSING,
         "cover-pushed crossing endpoints")
    need([COVER[a] for a in AVOIDING] == PUSHED_AVOIDING,
         "cover-pushed avoiding endpoints")
    need([spans(20, a, b) for a, b in CROSSING + [AVOIDING]] == [3, 3, 7],
         "CORRECTED source arc lengths MUST be 3,3,7")
    need([spans(10, a, b) for a, b in PUSHED_CROSSING + [PUSHED_AVOIDING]]
         == [3, 3, 5], "CORRECTED pushed arc lengths MUST be 3,3,5")
    host = {x: i for i, b in enumerate(BLOCKS) for x in b}
    need(all(host[a] != host[b] for a, b in CROSSING + [AVOIDING]),
         "path endpoints must escape one immersion block")
    need(edge_occurrences() == MATRIX, "matrix must follow cut endpoint images")
    power = MATRIX
    for _ in range(3):
        power = matmul(power, MATRIX)
    need(all(x > 0 for row in power for x in row), "M^4 must be positive")
    # In Q(phi) with phi^2 = phi+1: (phi,1,phi) * M = phi*(phi,1,phi).
    # LHS = (1+phi, phi, 1+phi), RHS = (phi^2,phi,phi^2).
    need(MATRIX == [[0, 0, 1], [1, 0, 1], [1, 1, 0]], "phi matrix")
    need(len(TARGET_ZERO) == 4 and len(SOURCE_ZERO) == len(COVER_ZERO) == 8,
         "typed zero-edge census")
    need(SOURCE_ZERO != COVER_ZERO, "source inclusion vs cover-pushed zero types")


def verify_manifest(p: int, manifest: dict, finite_row: dict) -> None:
    out = manifest["outputs"]
    ret = out["return"]
    need(ret["physical_iterate"] == p and ret["restricted_degree"] == 2
         and ret["global_degree"] == 2**p, f"p={p} physical vs global degree")
    marks = out["ideal_boundary"]
    need((marks["target_atom_count"], marks["covering_source_atom_count"],
          marks["outer_component_atom_count"]) == (10, 20, 1),
         f"p={p} source-locked atom counts")
    need(marks["target_atom_names"] == TARGET_NAMES, f"p={p} target atom names")
    need(marks["target_real_cuts"] == [substitute_cut(x, p) for x in TARGET_CUTS],
         f"p={p} target orbit indices")
    need(marks["source_real_cuts"] == [substitute_cut(x, p) for x in SOURCE_CUTS],
         f"p={p} source inverse indices")
    tree = out["marked_tree"]
    need(tree["hull"] == f"[x{2*p},x{p}]", f"p={p} correct physical hull")
    need(tree["preimage_in_V" + str(p)] == f"[-x{p},x{p}]",
         f"p={p} correct preimage tree")
    attach = out["attachment_census"]["components"]
    need(len(attach) == 1 and attach[0]["boundary_atoms"] == ATTACHED,
         f"p={p} one attachment")
    need(attach[0]["interval"] == f"[-x{p},x{2*p})"
         and attach[0]["root"] == f"x{2*p}", f"p={p} attached interval")
    need(attach[0]["immersion_boundary_destination"] == "target_interior_not_I0_boundary",
         f"p={p} no pointwise proper image of attachment")
    op = out["operations"]
    fstar = op["covering_f_star"]
    iota = op["immersion_iota_star"]
    need(fstar["source_to_target"] == COVER and fstar["degree"] == 2,
         f"p={p} covering table")
    need(iota["connected_blocks"] == BLOCKS and
         iota["block_lengths"] == [len(x) for x in BLOCKS] and
         iota["nonproper_target_atoms"] == [0] and iota["end_proper_inner"] is True,
         f"p={p} typed immersion/properness")
    expected_host = [next(i for i, b in enumerate(BLOCKS) if s in b)
                     for s in range(20)]
    need(iota["source_to_pullback"] == expected_host, f"p={p} inverse blocks")
    paths = out["sheet_paths"]
    need(paths["counts"] == [2, 1], f"p={p} 2 vs 1 restriction count")
    need(paths["homotopy"] == "same_target_relative_ideal_endpoints",
         f"p={p} target relative endpoint class")
    instances = paths["instances"]
    need(instances["crossing"]["source_restrictions"] == CROSSING
         and instances["avoiding"]["source_restrictions"] == [AVOIDING],
         f"p={p} path restrictions")
    need(instances["crossing"]["covering_pushforward_pairs"] == PUSHED_CROSSING
         and instances["avoiding"]["covering_pushforward_pairs"] == [PUSHED_AVOIDING],
         f"p={p} covering pushed pairs")
    need(all(obj["filters"]["A1_short_span"] and
             obj["filters"]["A3_2_not_in_one_pullback"]
             for obj in instances.values()), f"p={p} both path filters")
    wave = out["wave"]
    ratios = {3: "4/3", 4: "3/2"}
    centers = {3: "-9/64", 4: "-17/512"}
    radii = {3: ["3/256", "1/64"], 4: ["1/256", "3/512"]}
    need(wave["center"] == centers[p] and wave["open_radii"] == radii[p]
         and wave["ratio"] == ratios[p], f"p={p} native—not canonical—Wave")
    need(wave["target_base"] == [9, 0, 1] and wave["target_crest"] == 0
         and wave["pushed_bases"] == [[1, 2, 3], [7, 8, 9]]
         and wave["pushed_crests"] == [2, 8], f"p={p} parent child crest types")
    need(wave["harmonic_series_equality"] is True
         and wave["symbolic_width_coefficients_in_log_ratio_over_pi"]
         == {"target": "1/2", "each_child": "1"},
         f"p={p} symbolic (not canonical) harmonic equality")
    source_bracket = interval_from_bracket(out["polynomial"], "parameter_bracket")
    finite_bracket = interval_from_bracket(finite_row, "parameter_bracket")
    need(intervals_overlap(source_bracket, finite_bracket),
         f"p={p} native and later dyadic root charts inconsistent")
    if p == 4:
        zero = out["zero_edge_sectors"]
        need(zero["target_zero_old_edge_atoms"] == TARGET_ZERO
             and zero["source_inclusion_zero_old_edge_atoms"] == SOURCE_ZERO
             and zero["cover_pushforward_zero_old_edge_atoms"] == COVER_ZERO
             and zero["parent_and_child_wave_crests_zero_old_edge"] is True,
             "p4 native typed zero-edge labels")


def period_rows(rows: list[dict], first: int, last: int, label: str) -> dict[int, dict]:
    need(isinstance(rows, list), f"{label} must be a list")
    ids = [row["p"] for row in rows]
    need(ids == list(range(first, last + 1)),
         f"{label}: missing, duplicated or unordered periods; got {ids}")
    return {row["p"]: row for row in rows}


def verify_packets(large_stdout: str | None = None) -> None:
    uniform = packet(source_file("uniform"))
    finite = packet(source_file("finite"))
    canon = packet(source_file("canonical"))
    crest_f = packet(source_file("crest_fixed"))
    crest_c = packet(source_file("crest_opt"))

    verify_common(uniform["common_discrete_output_checked_each_period"])
    need(finite["source_avoiding_short_arc_atoms"] == 7
         and finite["cover_pushed_avoiding_short_arc_atoms"] == 5,
         "p3..12 explicit hostile-review short-arc correction")
    u = period_rows(uniform["results"], 3, 8, "uniform 3..8")
    f = period_rows(finite["periods"], 3, 12, "unconditional 3..12")
    c = period_rows(canon["finite"], 3, 12, "canonical finite 3..12")
    a = period_rows(crest_f["results"], 3, 8, "crest fixed 3..8")
    b = period_rows(crest_c["results"], 3, 16, "crest opt 3..16")
    need(crest_f["immersion_iota_star_blocks"] == BLOCKS
         and crest_c["immersion_iota_star_blocks"] == BLOCKS,
         "crest audits must use the same typed immersion")
    need(crest_f["covering_G_star"] == crest_c["covering_G_star"]
         == "S_s -> I_(s mod 10)", "crest audit covering is not immersion")
    need("NOT computed" in canon["scope"], "canonical max Wave must remain open")
    need("numerical conjecture" in crest_c["uniform_p_asymptotics"],
         "crest all-p ratio is conjecture only")
    need(canon["large_p_radial_result"]["from_period"] == 13,
         "radial all-p estimate must start at p13")
    need(canon["large_p_radial_result"]["radial_width_difference_bound"]
         == "7000000*4^(-p)", "radial convergence rate provenance")
    model_rad = numeric_interval(*canon["model_limit_radial_width_1e-7_strict"], 10**7)
    model_ratio = numeric_interval(*canon["model_limit_radial_ratio_1e-7_strict"], 10**7)
    model_upper = numeric_interval(
        *canon["model_limit_full_path_upper_envelope_1e-7_strict"], 10**7)
    need(F(2604925, 10**7) == model_rad[0] and
         F(51383080, 10**7) == model_ratio[0] and
         model_rad[1] < model_upper[0], "round limit vs upper envelope")
    for p in range(3, 13):
        r = f[p]
        need(r["parameter_bracket"]["denominator_power_of_two"] == 256
             and r["parameter_bracket"]["unique_in_seed_window"] is True,
             f"p={p} finite local uniqueness/256-cell")
        interval_from_bracket(r, "parameter_bracket")
        need(r["complex_phase_disks_pairwise_disjoint"] is True,
             f"p={p} primitive complex phase disks")
        need(F(r["central_degree_two_Rouche_margin_lower_2^-64"]) > F(1, 25),
             f"p={p} p-return Rouché margin >1/25")
        need(F(r["radial_whole_disk_margin_lower_2^-64"]) > 0,
             f"p={p} orbit-centred round gate whole-disk margin")
        need(r["radial_active_upper_gate"] == "right_-alpha",
             f"p={p} physical round gate")
        r6 = numeric_interval(*r["radial_ratio_millionth_strict_bracket"], 10**6)
        r7 = numeric_interval(*c[p]["radial_ratio_1e-7_strict"], 10**7)
        need(intervals_overlap(r6, r7), f"p={p} two independent radial ratios")
        cw = numeric_interval(*c[p]["radial_wave_width_1e-7_strict"], 10**7)
        upper = numeric_interval(*c[p]["full_lift_path_width_upper_1e-7_strict"],
                                 10**7)
        need(0 < cw[0] < cw[1] < upper[0] < upper[1],
             f"p={p} strict lower witness and distinct upper envelope")
        need(c[p]["NOT_a_canonical_width_certificate"] is True
             and c[p]["source_gate_disk_margin_over_R_gt_2_5"] is True,
             f"p={p} honest canonical-width status")
        need(interval_from_bracket(r, "parameter_bracket") ==
             interval_from_bracket(b[p], "parameter_bracket_2pow256"),
             f"p={p} crest and finite independent dyadic packet")
    for p in range(3, 9):
        urow = u[p]
        need(intervals_overlap(interval_from_bracket(urow, "parameter_root_bracket"),
                               interval_from_bracket(f[p], "parameter_bracket")),
             f"p={p} old 192-bit and new 256-bit root isolation")
        need(urow["real_and_complex_primitive_phase_balls_disjoint"] is True,
             f"p={p} old phase disk check")
        need(F(urow["selected_wave_ratio"]) == F(2 * (p - 1), p),
             f"p={p} old *chosen* ratio, not canonical")
        if p >= 4:
            need(urow["central_degree_two"]["method"] == "complex_Rouche",
                 f"p={p} degree-two source")
        else:
            need(urow["central_degree_two"]["method"] == "prior_source_p3",
                 "old p3 was an imported result, superseded by new direct proof")
        fixed = a[p]
        need(fixed["collar"]["whole_bins"] == 512 and
             fixed["first_image_angular_derivative_margin_positive"] is True
             and fixed["full_disk_images_in_target"] is True,
             f"p={p} fixed-collar full bins and whole disks")
        ratio_old = (F(fixed["certified_ratio_lower"]),
                     F(fixed["certified_ratio_upper"]))
        ratio_new = numeric_interval(*b[p]["original_fixed_subcollar"]
                                     ["ratio_bracket_1e5"], 10**5)
        need(intervals_overlap(ratio_old, ratio_new),
             f"p={p} fixed subcollar regression mismatch")
        if p >= 6:
            need(F(fixed["collar"]["u_min_lower"]) < 0,
                 f"p={p} negative angular cosine case lost")
    for p in range(3, 17):
        row = b[p]
        need(row["central_Rouche_margin_gt_1_25"] is True
             and row["complex_primitive_phase_disks_pairwise_disjoint"] is True,
             f"p={p} crest optimum phase and central degree")
        opt = numeric_interval(*row["ratio_bracket_1e5"], 10**5)
        orig = numeric_interval(*row["original_fixed_subcollar"]
                                ["ratio_bracket_1e5"], 10**5)
        need(opt[0] > 0 and orig[0] > 0 and opt[1] <= 1
             and opt[1] >= orig[0] and opt[0] > orig[0],
             f"p={p} optimum must beat selected old subcollar")
        parent = row["parent"]
        if p == 3:
            need(parent["center"] == "-9/64" and
                 parent["range"] == ["3/256", "1/64"] and
                 parent["radius_variable"] == "absolute radius",
                 "p3 actual source Wave, not x_p-normalized Wave")
        else:
            need(parent["center"] == "-3*x_p/4"
                 and [F(v) for v in parent["range"]]
                 == [F(1, 16), F(p - 1, 8 * p)]
                 and parent["radius_variable"] == "s=r/x_p",
                 f"p={p} chosen circular parent denominator")
        need(row["two_selected_terminal_crests"] == [
            "upper: S0,S3 -> I0,I3; closed I1,I2 with E0 upper",
            "lower: S17,S0 -> I7,I0; closed I8,I9 with E0 lower",
        ], f"p={p} fourth-push upper/lower same old edge")
        need("conditional" in row["width_interpretation"],
             f"p={p} no unconditional conformal optimizer claim")
        if p >= 9:
            need(row["parameter_bracket_2pow256"][1] ==
                 row["parameter_bracket_2pow256"][0] + 1,
                 f"p={p} crest 256-bit adjacent root bracket")
    for p, path in MANIFESTS.items():
        verify_manifest(p, packet(path), f[p])
    need(F(3, 20) - 12 * F(1, 4**13) - F(1, 128) -
         F(1, 2**13) > F(1, 25), "p13 worst-case analytic Rouché margin")

    if large_stdout is not None:
        model = json.loads(large_stdout)
        k = model["p13"]
        need(k["denominator_power_of_two"] == "256"
             and k["chart_tau_in_J"] == "true",
             "p13 independent analytic chart witness")
        lo = int(k["parameter_lower_numerator"])
        hi = int(k["parameter_upper_numerator"])
        need(hi == lo + 1 and
             b[13]["parameter_bracket_2pow256"] == [lo, hi],
             "p12/p13 seam: analytic p13 and finite crest p13 disagree")


def snapshot() -> dict[str, str]:
    files = set(READ_ONLY_FILES)
    for tree in READ_ONLY_TREES:
        need(tree.is_dir(), f"missing dependency directory {tree}")
        files.update(x for x in tree.rglob("*") if x.is_file() and
                     x.suffix in READ_ONLY_SUFFIXES)
    return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(files)}


def execute(label: str, argv: list[str]) -> str:
    need("--write" not in argv, f"forbidden write action in {label}")
    env = dict(os.environ)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    proc = subprocess.run([sys.executable, "-B", *argv], cwd=ROOT, env=env,
                          stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          text=True, timeout=2700, check=False)
    if proc.returncode:
        raise AssertionError(f"upstream verifier {label!r} failed (code "
                             f"{proc.returncode})\nstdout:\n{proc.stdout[-6000:]}"
                             f"\nstderr:\n{proc.stderr[-6000:]}")
    print(f"PASS upstream: {label}", flush=True)
    return proc.stdout


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--consistency-only", action="store_true",
                    help="skip upstream subprocesses but audit all saved packets")
    ap.add_argument("--with-tests", action="store_true",
                    help="also run each upstream adversarial unit test suite")
    args = ap.parse_args()
    need(not (args.consistency_only and args.with_tests),
         "--with-tests and --consistency-only conflict")
    before = snapshot()
    large_result = None
    try:
        if not args.consistency_only:
            for label, script, flags in SCRIPT_COMMANDS:
                output = execute(label, [script, *flags])
                if label == "large":
                    large_result = output
            if args.with_tests:
                for key, dirname in DIRS.items():
                    execute("tests " + key,
                            ["-m", "unittest", "discover", "-s",
                             f"research/independent_audits/{dirname}",
                             "-p", "test_*.py", "-v"])
                execute("native wave transfer adversarial tests",
                        ["-m", "unittest", "discover", "-s",
                         "research/native_wave_transfer", "-p", "test_*.py", "-v"])
        verify_packets(large_result)
        print("PASS cross-file: p3/p4 physical, p3..12 finite, p13 signed chart,"
              " p3..16 crest, source/cover arc lengths 3/3/7 vs 3/3/5,"
              " distinct covering/immersion, phi matrix and noncanonical Waves",
              flush=True)
    finally:
        after = snapshot()
        need(before == after, "a dependency verifier mutated an immutable file: " +
             str(sorted(k for k in set(before) | set(after)
                        if before.get(k) != after.get(k))))
    print("PASS all dependency files unchanged; external analytic theorems"
          " require human mathematical verification")


if __name__ == "__main__":
    main()
