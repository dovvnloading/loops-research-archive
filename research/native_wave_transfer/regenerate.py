#!/usr/bin/env python3
"""Independent, source-locked PR #68 native wave-transfer regenerator.

Standard-library rational/interval arithmetic; never imports the PR #68 checker.
Topology/KKL results are *stated dependencies*, not proved by finite code.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from dataclasses import dataclass
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
INPUT = HERE / "physical_examples/tip_pr68.json"
LOCK = HERE / "source_contracts/LOCK.json"
CONTRACT = HERE / "source_contracts/record_fields.json"
MANIFEST = HERE / "experiment_manifests/tip_pr68.json"
ORIGINAL = REPO / "results/tip_root_interval_geometry.json"
REFERENCE = REPO / "results/tip_KKL_tree_marked_breakage_20261109.json"
SCALE = 1 << 256


def ensure(predicate: bool, reason: str) -> None:
    if not predicate:
        raise AssertionError(reason)


def load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def canonical(value: object) -> bytes:
    return (json.dumps(value, sort_keys=True, indent=2, ensure_ascii=True) + "\n").encode("utf-8")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def git_blob(path: Path) -> str:
    data = path.read_bytes()
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


@dataclass(frozen=True)
class Box:
    """Outward 2^-256 dyadic enclosure of a real number (inclusive)."""
    low: int
    high: int

    def __post_init__(self) -> None:
        ensure(self.low <= self.high, "empty interval")

    @classmethod
    def rational(cls, value: Q | int) -> "Box":
        scaled = Q(value) * SCALE
        low = scaled.numerator // scaled.denominator
        high = -((-scaled.numerator) // scaled.denominator)
        return cls(low, high)

    def __add__(self, other: "Box") -> "Box":
        return Box(self.low + other.low, self.high + other.high)

    def __neg__(self) -> "Box":
        return Box(-self.high, -self.low)

    def square(self) -> "Box":
        a, b = self.low**2, self.high**2
        low = 0 if self.low <= 0 <= self.high else min(a, b)
        return Box(low // SCALE, (max(a, b) + SCALE - 1) // SCALE)

    def before(self, other: "Box") -> bool:
        return self.high < other.low

    def center(self) -> Q:
        return Q(self.low + self.high, 2 * SCALE)

    def contains(self, other: "Box") -> bool:
        return self.low <= other.low and other.high <= self.high

    def overlaps(self, other: "Box") -> bool:
        return not (self.before(other) or other.before(self))


def bracket(c: Box, steps: int = 27) -> list[Box]:
    orbit = [Box.rational(0)]
    for _ in range(steps):
        orbit.append(orbit[-1].square() + c)
    return orbit


def iterate3(z: Box, c: Box) -> Box:
    for _ in range(3):
        z = z.square() + c
    return z


def isolate_alpha(c: Box) -> Box:
    """Interval-bisect the dividing real fixed point of G; no guessed decimal."""
    lo, hi = Q(3, 32), Q(1, 10)
    ensure(Box.rational(lo).before(iterate3(Box.rational(lo), c)), "alpha lower sign")
    ensure(iterate3(Box.rational(hi), c).before(Box.rational(hi)), "alpha upper sign")
    for _ in range(88):
        mid = (lo + hi) / 2
        y, x = iterate3(Box.rational(mid), c), Box.rational(mid)
        if x.before(y):
            lo = mid
        elif y.before(x):
            hi = mid
        else:
            raise AssertionError("alpha interval too imprecise for bisection")
    return Box(Box.rational(lo).low, Box.rational(hi).high)


def isolate_negative_preimage(y: Box, c: Box, left: Box) -> Box:
    """Monotone negative branch G:[-x3,0] -> [x6,x3]."""
    lo, hi = Q(left.low, SCALE), Q(0)
    for _ in range(78):
        m = (lo + hi) / 2
        gm = iterate3(Box.rational(m), c)
        if gm.before(y):
            lo = m
        elif y.before(gm):
            hi = m
        else:
            raise AssertionError("source cut not separable at 78 bits")
    return Box(Box.rational(lo).low, Box.rational(hi).high)


def index_of(value: Box, side: int, cuts: list[Box]) -> int:
    """Two boundary sides on a real slit, terminal atom through either tip."""
    n = len(cuts)
    if value.before(cuts[0]):
        return 0
    if cuts[-1].before(value):
        return n
    for j in range(1, n):
        if cuts[j - 1].before(value) and value.before(cuts[j]):
            return j if side == 1 else 2*n - j
    raise AssertionError("point touches a cut or cannot be placed exactly")


def source_sample(s: int, cuts: list[Box], left: Box, right: Box) -> tuple[Q, int]:
    n = len(cuts)
    if s == 0:
        a, b, side = left, cuts[0], 1
    elif s == n:
        a, b, side = cuts[-1], right, 1
    else:
        j, side = (s, 1) if s < n else (2*n-s, -1)
        a, b = cuts[j-1], cuts[j]
    ensure(a.before(b), "sample cell not separated")
    return (2*a.center() + b.center())/3, side


def short_arc(a: int, b: int, size: int) -> list[int]:
    forward = (b-a) % size
    backward = (a-b) % size
    ensure(forward != backward, "ambiguous half-circle arc")
    start, length = (a, forward) if forward < backward else (b, backward)
    return [(start+k) % size for k in range(length+1)]


def cyclic_blocks(labels: list[int], target_count: int) -> list[list[int]]:
    n = len(labels)
    ensure(set(labels) == set(range(target_count)), "missing target cell")
    blocks = []
    for t in range(target_count):
        starts = [s for s in range(n) if labels[s] == t and labels[(s-1)%n] != t]
        ensure(len(starts) == 1, "disconnected immersion pullback cell")
        s, block = starts[0], []
        while labels[s] == t:
            ensure(len(block) < n, "cyclic cell overflow")
            block.append(s)
            s = (s+1) % n
        blocks.append(block)
    ensure(sorted(sum(blocks, [])) == list(range(n)), "pullback not a partition")
    return blocks


def disk_image(center: Q, radius: Q, c0: Q, cr: Q) -> tuple[Q, Q]:
    """Exact rational complex-ball bound for three polynomial applications."""
    d, r = center, radius
    for _ in range(3):
        r = 2*abs(d)*r + r*r + cr
        d = d*d + c0
    return d, r


def certify_circle(q: Q, w: Q, c0: Q, cr: Q, limit: Q,
                   center_in_tree: tuple[Q, Q]) -> dict:
    ensure(w < q, "clockwise/semicircle convention changed")
    mid, radius = (w+q)/2, (q-w)/2
    ensure(center_in_tree[0] < mid < center_in_tree[1], "disk center not in native tree")
    ensure(abs(mid)+radius < Q(1, 4), "physical circle not in target disk")
    d, r = disk_image(mid, radius, c0, cr)
    ensure(abs(d)+r < limit, "whole complex disk bound failed")
    return {"center": str(mid), "radius": str(radius),
            "real_left_intersection": str(w), "real_right_endpoint": str(q),
            "certified_G_disk_image_absolute_bound": str(limit),
            "certified_clearance_to_target_radius_1_over_4": str(Q(1, 4)-limit)}


def restrictions(q: Q, w: Q, source_cuts: list[Box], tleft: Box,
                 tright: Box, attachment_end: Box) -> list[list[int]]:
    """Circle/slit incidence, not a table of expected marked restrictions."""
    Qbox, Wbox = Box.rational(q), Box.rational(w)
    ensure(tleft.before(Qbox) and Qbox.before(tright), "q not on source slit")
    qs = (index_of(Qbox, 1, source_cuts), index_of(Qbox, -1, source_cuts))
    if Wbox.before(tleft):
        return [[qs[0], qs[1]]]
    ensure(Wbox.before(attachment_end) and tleft.before(Wbox),
           "left crossing is not in the new attachment")
    return [[qs[0], index_of(Wbox, 1, source_cuts)],
            [index_of(Wbox, -1, source_cuts), qs[1]]]


def recompute(example: dict, source: dict) -> dict:
    ensure(example["return"]["physical_iterate"] == 3, "wrong physical return time")
    ensure(example["return"]["restricted_degree"] == 2, "wrong central degree")
    ensure(example["domains"]["target"]["radius"] == "1/4", "wrong target disk")
    ensure(example["operations"]["covering"]["ideal_action"] == "f_*", "wrong cover")
    ensure(example["operations"]["immersion"]["ideal_action"] == "iota^*", "wrong immersion")
    ensure(example["operations"]["covering"]["ideal_action"] != example["operations"]["immersion"]["ideal_action"], "operations conflated")
    ensure(source["inner_root_exact_interval"] == "[x9,x18]", "root source drift")
    ensure("x18=-x9" in source["exact_orbit_relations"], "orbit identity missing")
    ensure(source["phase_intervals_pairwise_disjoint"] is True, "small Julia phase separation")
    phases = {a["physical_phase"]: a for a in source["phase_intervals"]}
    for k, val in ((0, "[x9,x18]"), (3, "[x12,x3]"), (6, "[x6,x15]")):
        ensure(phases[k]["exact_interval"] == val and phases[k]["coarse_phase"] == 0,
               "small Julia interval provenance drift")
    p = source["parameter_bracket"]
    den = 1 << p["denominator_power_of_two"]
    clo, chi = Q(p["lower_numerator"], den), Q(p["upper_numerator"], den)
    ensure(clo < chi, "parameter bracket invalid")
    c = Box(Box.rational(clo).low, Box.rational(chi).high)
    orbit = bracket(c)
    x = {"x"+str(k): t for k,t in enumerate(orbit)}
    x["alpha"] = isolate_alpha(c)
    ensure(x["x9"].overlaps(-x["x18"]), "phase root relation not consistent")
    ensure(x["x6"].before(x["x15"]) and x["x15"].before(x["x9"])
           and x["x9"].before(Box.rational(0)) and Box.rational(0).before(x["x18"])
           and x["x18"].before(x["alpha"]) and x["alpha"].before(x["x12"])
           and x["x12"].before(x["x3"]), "orbit and fixed-point order")
    ensure((-x["x3"]).before(x["x6"]), "attachment no longer exists")
    ensure(x["x3"].before(Box.rational(Q(1,4))), "native tree outside U3")
    # G' = 8z f(z) f²(z), so G increases on [-x3,0] and decreases on [0,x3].
    fbox = Box(0,x["x3"].high).square()+c
    f2box = fbox.square()+c
    ensure(fbox.high < 0 < f2box.low, "negative monotone branch uncertified")
    ensure(iterate3(-x["x3"],c).overlaps(x["x6"]), "tree preimage endpoint")
    ensure(iterate3(Box.rational(0),c).overlaps(x["x3"]), "critical return")
    t_symbols = example["marking"]["target_cuts"]
    ensure(t_symbols == ["x15","x9","x18","alpha","x12"], "marking source convention drift")
    target_cuts = [x[key] for key in t_symbols]
    ensure(all(a.before(b) for a,b in zip(target_cuts,target_cuts[1:])), "target cuts overlap")
    # Find all ten cut preimages by strict monotone bisection, instead of
    # supplying a twenty-entry atom map or any table from the old checker.
    candidates = []
    for name, target in zip(t_symbols,target_cuts):
        neg = isolate_negative_preimage(target,c,-x["x3"])
        candidates += [(neg,"G^-1("+name+")_-"),(-neg,"G^-1("+name+")_+")]
    candidates.sort(key=lambda item:item[0].center())
    source_cuts = [v for v,_ in candidates]
    ensure(all(a.before(b) for a,b in zip(source_cuts,source_cuts[1:])), "source cuts overlap")
    # Source-locked exact polynomial orbit identities identify preimages.
    preimage_names = {"x15":"x12", "x9":"x6", "x18":"x15",
                      "alpha":"alpha", "x12":"x9"}
    symcuts = []
    for value, label in candidates:
        for target, src in preimage_names.items():
            if label == "G^-1("+target+")_-":
                candidate = -x[src] if x[src].low > 0 else x[src]
                ensure(value.overlaps(candidate), "negative symbolic preimage not located")
                symcuts.append("-"+src if x[src].low > 0 else src)
                break
            if label == "G^-1("+target+")_+":
                candidate = x[src] if x[src].low > 0 else -x[src]
                ensure(value.overlaps(candidate), "positive symbolic preimage not located")
                symcuts.append(src if x[src].low > 0 else ("x18" if src == "x9" else "-"+src))
                break
        else:
            raise AssertionError("unknown source preimage label")
    # Convert real source cells to two *distinct* boundary operations.
    covering, immersed, attachment_atoms = [], [], []
    for s in range(2*len(source_cuts)):
        real, side = source_sample(s, source_cuts, -x["x3"], x["x3"])
        real_box = Box.rational(real)
        mapped_side = side if real < 0 else -side
        covering.append(index_of(iterate3(real_box,c),mapped_side,target_cuts))
        attached = real_box.before(x["x6"])
        immersed.append(0 if attached else index_of(real_box,side,target_cuts))
        if attached:
            attachment_atoms.append(s)
    blocks = cyclic_blocks(immersed, 2*len(target_cuts))
    attachment_set = set(attachment_atoms)
    ensure(all(b[0] not in attachment_set and b[-1] not in attachment_set for b in blocks),
           "a pulled-back interval is not end-proper")
    nonproper = [i for i,b in enumerate(blocks) if attachment_set.intersection(b)]
    ensure(nonproper == [0], "wrong number of nonproper attachment blocks")
    ensure(all(covering.count(t) == 2 for t in range(len(target_cuts)*2)),
           "covering degree != 2 on ideal atoms")
    # The only new attachment interval follows from T' (two preimages per
    # fiber in V3) and T, *conditional* on the sourced degree-two theorem.
    q = Q(example["paths"][0]["q"])
    ensure(all(Q(path["q"]) == q for path in example["paths"]), "path endpoints differ")
    ensure(x["x15"].before(Box.rational(q)) and Box.rational(q).before(-x["alpha"]),
           "marked target base endpoint left its interval")
    pairs = {}
    circles = []
    c0, cr = (clo+chi)/2, (chi-clo)/2
    for row in example["paths"]:
        w = Q(row["w"])
        bound = Q(row["disk_limit"])
        circle = certify_circle(q,w,c0,cr,bound,((-x["x3"]).center(),x["x3"].center()))
        circle["name"] = row["name"]
        ensure((w < -x["x3"].center()) if row["name"] == "avoiding" else
               (-x["x3"].center() < w < x["x6"].center()), "path/attachment intersection changed")
        rows = restrictions(q,w,source_cuts,-x["x3"],x["x3"],x["x6"])
        for a,b in rows:
            ensure(len(short_arc(a,b,len(covering))) > 2, "A.1 short source path")
            ensure(immersed[a] != immersed[b], "A.3.2 one-cell path")
            ensure(len(short_arc(covering[a],covering[b],len(target_cuts)*2))>2,
                   "A.1 short dynamical image")
        pairs[row["name"]] = {
            "source_restrictions":rows,
            "immersion_endpoint_pairs":[[immersed[a],immersed[b]] for a,b in rows],
            "covering_pushforward_pairs":[[covering[a],covering[b]] for a,b in rows],
            "surviving_count":len(rows),
            "filters":{"A1_short_span":True,"A3_2_not_in_one_pullback":True}}
        circles.append(circle)
    target_endpoints = [index_of(Box.rational(q),s,target_cuts) for s in (1,-1)]
    ensure(len(short_arc(*target_endpoints,2*len(target_cuts)))>2, "A1 target path short")
    # Every concentric wave leaf satisfies the attachment and endpoint
    # inequalities, because the *closed* endpoint ranges are enclosed.
    wave = example["wave"]
    center, r0, r1 = Q(wave["center"]), *map(Q,wave["open_radii"])
    ensure(0 < r0 < r1, "wave radii reversed")
    qr = Box(Box.rational(center+r0).low, Box.rational(center+r1).high)
    wr = Box(Box.rational(center-r1).low, Box.rational(center-r0).high)
    ensure(x["x15"].before(qr) and qr.before(-x["alpha"]), "wave endpoints leave target base")
    ensure((-x["x3"]).before(wr) and wr.before(x["x6"]), "wave misses attachment")
    ensure(source_cuts[0].before(wr) and wr.before(source_cuts[1]), "wave crossing leaves first attachment side")
    # The existing full small closed disk covers the entire family.
    ensure(center == Q(circles[0]["center"]) and r1 == Q(circles[0]["radius"]),
           "wave not covered by the certified small disk")
    ratio = r1/r0
    # In W = coefficient * log(r1/r0)/pi, rectangle height is 2pi
    # for target and pi for each child. Exact rational harmonic law.
    target_height = Q(wave["target_angular_height_pi"])
    child_height = Q(wave["child_angular_height_pi"])
    ensure(target_height == 2*child_height and child_height == 1, "wrong angular split")
    parent_coeff, child_coeff = 1/target_height, 1/child_height
    ensure(1/(1/child_coeff+1/child_coeff) == parent_coeff, "series width law")
    push_bases = [short_arc(*r,2*len(target_cuts)) for r in
                  pairs["crossing"]["covering_pushforward_pairs"]]
    base = short_arc(*target_endpoints,2*len(target_cuts))
    ensure(all(len(v)==3 for v in [base]+push_bases), "wave crest not an atom")
    target_names = ["K2_terminal"] + ["edge_K2_K0_upper", "K0_upper",
        "edge_K0_alpha_upper", "edge_alpha_K1_upper", "K1_terminal",
        "edge_alpha_K1_lower", "edge_K0_alpha_lower", "K0_lower", "edge_K2_K0_lower"]
    return {
        "polynomial":{"family":example["polynomial"]["family"],"parameter_bracket":p,
                      "critical_point":"0","orbit_index_range":[0,27]},
        "return":{"physical_iterate":3,"restricted_degree":2,"global_degree":8},
        "domains":{"source":{"symbol":"V3","definition":"component(G^-1(U3),0)","degree":2},
                   "target":{"symbol":"U3","center":"0","radius":"1/4"}},
        "marked_tree":{"small_julia_intervals":["[x9,x18]","[x12,x3]","[x6,x15]"],
                       "hull":"[x6,x3]","preimage_in_V3":"[-x3,x3]",
                       "dividing_fixed_point":"alpha"},
        "attachment_census":{"complete_in_V3_given_degree_two":True,"components":[{
            "interval":"[-x3,x6)","root":"x6","boundary_atoms":attachment_atoms,
            "immersion_boundary_destination":"target_interior_not_I0_boundary"}]},
        "ideal_boundary":{"target_atom_count":len(target_names),"target_atom_names":target_names,
                          "target_real_cuts":t_symbols,"covering_source_atom_count":len(covering),
                          "source_real_cuts":symcuts,"outer_component_atom_count":1},
        "operations":{
            "covering_f_star":{"action":"f_*","degree":2,"source_to_target":covering},
            "immersion_iota_star":{"action":"iota^*","source_to_pullback":immersed,
                "connected_blocks":blocks,"block_lengths":[len(b) for b in blocks],
                "end_proper_inner":True,"nonproper_target_atoms":nonproper}},
        "sheet_paths":{"endpoint_target_atoms":target_endpoints,"circles":circles,
                       "instances":pairs,"homotopy":"same_target_relative_ideal_endpoints",
                       "counts":[pairs["crossing"]["surviving_count"],pairs["avoiding"]["surviving_count"]]},
        "wave":{"center":str(center),"open_radii":[str(r0),str(r1)],
                "right_endpoint_range":[str(center+r0),str(center+r1)],
                "attachment_crossing_range":[str(center-r1),str(center-r0)],
                "target_base":base,"target_crest":base[1],
                "pushed_bases":push_bases,"pushed_crests":[b[1] for b in push_bases],
                "ratio":str(ratio),"target_width":f"log({ratio})/(2*pi)",
                "each_child_and_pushed_width":f"log({ratio})/pi",
                "child_multiplier":int(child_coeff/parent_coeff),
                "harmonic_series_equality":True,
                "symbolic_width_coefficients_in_log_ratio_over_pi":{"target":"1/2","each_child":"1"}}}


def crosscheck(actual: dict, ref: dict) -> None:
    """Compare independent geometric derivation, not a copied saved output."""
    b = actual["ideal_boundary"]
    op = actual["operations"]
    paths = actual["sheet_paths"]
    wave = actual["wave"]
    expected = {
        "source_parameter":actual["polynomial"]["parameter_bracket"],
        "target_inner_marking_atoms":b["target_atom_names"],
        "target_inner_cut_positions_increasing":b["target_real_cuts"],
        "source_inner_cut_positions_increasing":b["source_real_cuts"],
        "source_f_cover_atom_map":op["covering_f_star"]["source_to_target"],
        "source_inclusion_pullback_atom_map":op["immersion_iota_star"]["source_to_pullback"],
        "inner_pullback_blocks":op["immersion_iota_star"]["connected_blocks"],
        "inner_pullback_lengths":op["immersion_iota_star"]["block_lengths"],
        "attachment_boundary_source_atoms":actual["attachment_census"]["components"][0]["boundary_atoms"],
        "not_proper_on_target_inner_atoms":op["immersion_iota_star"]["nonproper_target_atoms"],
        "end_proper_on_all_ten_inner_intervals":op["immersion_iota_star"]["end_proper_inner"],
        "tree":actual["marked_tree"]["hull"],
        "tree_preimage_in_V3":actual["marked_tree"]["preimage_in_V3"],
        "single_new_attachment":actual["attachment_census"]["components"][0]["interval"],
        "target_endpoint_atom_pair":paths["endpoint_target_atoms"],
        "crossing_circle_source_restrictions":paths["instances"]["crossing"]["source_restrictions"],
        "crossing_circle_coarse_endpoint_pairs":paths["instances"]["crossing"]["immersion_endpoint_pairs"],
        "crossing_circle_F_pushforward_atom_pairs":paths["instances"]["crossing"]["covering_pushforward_pairs"],
        "avoiding_circle_source_restrictions":paths["instances"]["avoiding"]["source_restrictions"],
        "avoiding_circle_F_pushforward_atom_pairs":paths["instances"]["avoiding"]["covering_pushforward_pairs"],
        "same_target_arc_class_different_marked_restriction_counts":paths["counts"],
        "marked_breakable_wave":{
            "center":wave["center"],"open_radius_interval":wave["open_radii"],
            "right_endpoint_range":wave["right_endpoint_range"],
            "attachment_crossing_range":wave["attachment_crossing_range"],
            "target_base_atoms":wave["target_base"],"target_crest_atom":wave["target_crest"],
            "two_pushed_base_atoms":wave["pushed_bases"],"two_pushed_crest_atoms":wave["pushed_crests"],
            "target_extremal_width":wave["target_width"],
            "each_restriction_and_pushforward_width":wave["each_child_and_pushed_width"],
            "child_width_multiplier":wave["child_multiplier"],
            "harmonic_series_inequality_is_equality":wave["harmonic_series_equality"]}}
    for key,value in expected.items():
        if key == "marked_breakable_wave":
            for subkey,subvalue in value.items():
                ensure(ref[key][subkey] == subvalue, "reference mismatch: wave."+subkey)
        else:
            ensure(ref[key] == value, "reference mismatch: "+key)
    for circle, old in zip(paths["circles"],ref["circles"]):
        ensure(circle == old, "reference mismatch: closed complex disk certificate")
    ensure(len(paths["circles"]) == len(ref["circles"]) == 2, "circle count mismatch")
    ensure(ref["both_crossing_restrictions_pass_A1_and_single_pullback_cell_filters"] is True,
           "reference marked filters changed")


def source_lock() -> dict:
    lock = load(LOCK)
    for item in lock["repository_files"]:
        path = REPO / item["path"]
        ensure(git_blob(path) == item["git_blob_sha1"], "source lock mismatch: "+item["path"])
    return lock


def build_manifest() -> dict:
    lock = source_lock()
    example, source, reference = load(INPUT), load(ORIGINAL), load(REFERENCE)
    actual = recompute(example,source)
    crosscheck(actual,reference)
    ensure(example["source_contract"] == "source_contracts/record_fields.json#/records/PhysicalExample",
           "example contract identity drift")
    return {"schema_version":1,"experiment_id":example["id"],
            "inputs":{"source_locks":lock["repository_files"],
                      "arxiv_source":lock["arxiv_source"],
                      "example_sha256":sha256(INPUT),"contracts_sha256":sha256(CONTRACT),
                      "lock_sha256":sha256(LOCK)},
            "code":{"file":"research/native_wave_transfer/regenerate.py",
                    "sha256":sha256(Path(__file__))},
            "outputs":actual,"outputs_sha256":hashlib.sha256(canonical(actual)).hexdigest(),
            "proof_status":{
                "certified_by_exact_arithmetic":["orbit cut strict order","real monotonicity signs",
                    "all ten inverse cut brackets","20 covering and immersed source samples",
                    "unique cyclic blocks and finite marking filters","closed complex disks",
                    "whole wave endpoint intervals","rational symbolic harmonic coefficient equality"],
                "conditional_on_cited_analytic_inputs":["physical quadratic-like V3 degree two",
                    "Misiurewicz dendrite and exact small Julia identifications",
                    "KKL induced ideal marking, attachment Proposition 6.5 and proper restriction definitions",
                    "relative-endpoint prime-end homotopy","extremal width rectangle/conformal-invariance argument"],
                "numeric_only":[],
                "unproved":["canonical-localization transfer","general wave amplification",
                    "global H1-H4 and MLC", "machine formalization of Caratheodory topology"]}}


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--check", action="store_true", help="default: enforce immutable manifest")
    ap.add_argument("--write", action="store_true", help="explicitly re-freeze manifest after review")
    args = ap.parse_args()
    ensure(not (args.check and args.write), "--check and --write are exclusive")
    actual = canonical(build_manifest())
    if args.write:
        MANIFEST.write_bytes(actual)
        print("WROTE", MANIFEST)
    else:
        ensure(MANIFEST.read_bytes() == actual, "immutable experiment manifest mismatch")
        print("PASS: independently regenerated 10/20 atoms, unique attachment, 2/1 filtered paths, exact harmonic Wave widths; source and code hashes locked")


if __name__ == "__main__":
    main()
