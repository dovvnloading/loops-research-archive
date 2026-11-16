#!/usr/bin/env python3
"""Independent primitive period-four / inner-period-three physical tip regenerator.

Uses the same rational Box, ideal-atom and canonical-manifest primitives as the
unchanged PR #68 regenerator. Finite certificates are distinguished from KKL
prime-end, renormalization-straightening, and extremal-width inputs.
"""
from __future__ import annotations

import argparse
import hashlib
from fractions import Fraction as Q
from pathlib import Path

from regenerate import (
    Box, SCALE, HERE, REPO, bracket, canonical, cyclic_blocks, ensure,
    git_blob, index_of, load, restrictions, sha256, short_arc, source_sample,
)

INPUT = HERE / "physical_examples/primitive4_tip12.json"
PARAMETER = HERE / "physical_examples/primitive4_tip12_parameter.json"
CONTRACT = HERE / "source_contracts/primitive4_record_fields.json"
LOCK = HERE / "source_contracts/primitive4_LOCK.json"
MANIFEST = HERE / "experiment_manifests/primitive4_tip12.json"
R4 = Q(1, 16)
R12 = Q(1, 128)
RHO4 = Q(1, 16)
RHO12 = Q(3, 256)
OLD_EDGES = [("x20", "x12"), ("x24", "alpha"), ("alpha", "x16")]
EDGE_NAMES = ["E20", "E0a", "Ea1"]


def mul(a: Box, b: Box) -> Box:
    """Outward dyadic product at the same 2^-256 lattice as regenerate.Box."""
    terms = (a.low*b.low, a.low*b.high, a.high*b.low, a.high*b.high)
    return Box(min(terms)//SCALE, -((-max(terms))//SCALE))


def absolute_upper(a: Box) -> Q:
    return Q(max(abs(a.low), abs(a.high)), SCALE)


def absolute_lower(a: Box) -> Q:
    if a.low > 0:
        return Q(a.low, SCALE)
    if a.high < 0:
        return Q(-a.high, SCALE)
    return Q(0)


def iterate(z: Box, c: Box, count: int) -> Box:
    for _ in range(count):
        z = z.square() + c
    return z


def derivative_parameter(c: Box, n: int) -> Box:
    x, deriv = Box.rational(0), Box.rational(0)
    for _ in range(n):
        deriv = mul(mul(Box.rational(2), x), deriv) + Box.rational(1)
        x = x.square() + c
    return deriv


def certify_parameter(parameter: dict) -> tuple[Box, list[Box]]:
    ensure(parameter["equation"] == "x24+x12=0", "parameter equation changed")
    p = parameter["parameter_bracket"]
    ensure(p["denominator_power_of_two"] == 160, "parameter resolution changed")
    den = 1 << p["denominator_power_of_two"]
    lo = Q(p["lower_numerator"], den)
    hi = Q(p["upper_numerator"], den)
    ensure(hi-lo == Q(1, den), "parameter bracket not adjacent dyadics")
    left = bracket(Box.rational(lo), 24)
    right = bracket(Box.rational(hi), 24)
    ensure((left[24]+left[12]).low > 0, "left parameter sign uncertified")
    ensure((right[24]+right[12]).high < 0, "right parameter sign uncertified")
    c = Box(Box.rational(lo).low, Box.rational(hi).high)
    deriv = derivative_parameter(c, 24) + derivative_parameter(c, 12)
    ensure(deriv.high < 0, "root may not be unique in parameter bracket")
    x = bracket(c, 36)
    ensure(x[12].overlaps(-x[24]), "root orbit identity incompatible")
    ensure(x[36].overlaps(x[24]), "root eventual fixed orbit incompatible")
    return c, x


def rouche_degree_two(c: Box, n: int, rho: Q, target_radius: Q,
                      claimed_margin: Q) -> None:
    """For |z|=rho, f^n(z)=d+A*z^2+E(z), |E(z)|<=tail.

    If |A|*rho^2>|d|+tail+target_radius then Rouché gives exactly
    two preimages for every w in the target disk. Zero is a simple
    critical point of f^n inside the unique central component.
    """
    d, a, tail = Box.rational(0), Box.rational(0), Q(0)
    for j in range(1, n+1):
        tail = 2*absolute_upper(d)*tail + (absolute_upper(a)*rho*rho + tail)**2
        a = Box.rational(1) if j == 1 else mul(mul(Box.rational(2), d), a)
        d = d.square() + c
    margin = absolute_lower(a)*rho*rho - absolute_upper(d) - tail - target_radius
    ensure(margin > claimed_margin, f"f^{n} Rouché lower bound failed")
    ensure(absolute_upper(d) < target_radius, "critical value misses target")
    ensure(rho >= target_radius if n == 4 else rho > target_radius,
           "invalid source boundary radius")


def disk_image_n(center: Q, radius: Q, c0: Q, cr: Q, n: int) -> tuple[Q, Q]:
    d, r = center, radius
    for _ in range(n):
        r = 2*abs(d)*r + r*r + cr
        d = d*d + c0
    return d, r


def primitive_phase_balls(c0: Q, cr: Q) -> None:
    """Disjoint enclosures for f^j(K_G), j=0,1,2,3."""
    disks = [(Q(0), RHO4)]
    d, r = Q(0), RHO4
    for _ in range(3):
        d, r = disk_image_n(d, r, c0, cr, 1)
        disks.append((d, r))
    for i in range(4):
        for j in range(i+1, 4):
            ensure(abs(disks[i][0]-disks[j][0]) > disks[i][1]+disks[j][1],
                   "primitive phase enclosures overlap")


def isolate_alpha(c: Box) -> Box:
    lo, hi = Q(1, 64), Q(1, 32)
    ensure(Box.rational(lo).before(iterate(Box.rational(lo), c, 4)),
           "alpha left sign")
    ensure(iterate(Box.rational(hi), c, 4).before(Box.rational(hi)),
           "alpha right sign")
    for _ in range(88):
        m = (lo+hi)/2
        gm, mm = iterate(Box.rational(m), c, 4), Box.rational(m)
        if mm.before(gm):
            lo = m
        elif gm.before(mm):
            hi = m
        else:
            raise AssertionError("alpha ambiguous at dyadic resolution")
    return Box(Box.rational(lo).low, Box.rational(hi).high)


def negative_inverse(y: Box, c: Box, left: Box) -> Box:
    lo, hi = Q(left.low, SCALE), Q(0)
    for _ in range(78):
        mid = (lo+hi)/2
        image = iterate(Box.rational(mid), c, 4)
        if image.before(y):
            lo = mid
        elif y.before(image):
            hi = mid
        else:
            raise AssertionError("physical source preimage not isolated")
    return Box(Box.rational(lo).low, Box.rational(hi).high)


def circle(q: Q, w: Q, c0: Q, cr: Q, limit: Q, x4: Box) -> dict:
    ensure(w < q, "wrong semicircle orientation")
    mid, radius = (w+q)/2, (q-w)/2
    ensure(Q(-x4.high, SCALE) < mid < Q(x4.low, SCALE),
           "circle center outside physical Tprime")
    ensure(abs(mid)+radius < R4, "circle extends outside U4")
    d, r = disk_image_n(mid, radius, c0, cr, 4)
    ensure(abs(d)+r < limit < R4, "whole 4-iterate complex disk bound failed")
    return {"center":str(mid), "radius":str(radius),
            "real_left_intersection":str(w), "real_right_endpoint":str(q),
            "certified_G_disk_image_absolute_bound":str(limit),
            "certified_clearance_to_target_radius_1_over_16":str(R4-limit)}


def old_edge_for(real: Box, x: dict[str, Box]) -> str | None:
    for name, (start, end) in zip(EDGE_NAMES, OLD_EDGES):
        if x[start].before(real) and real.before(x[end]):
            return name
    return None


def edge_analysis(x: dict[str, Box], c: Box, neg: dict[str, Box],
                  symneg: dict[str, str], sympos: dict[str, str]) -> dict:
    # Endpoint images are certified by the polynomial, not transcribed rows.
    image_names = {"x20":"x24", "x12":"x16", "x24":"x16",
                   "alpha":"alpha", "x16":"x20"}
    cuts = ["x20", "x12", "x24", "alpha", "x16"]
    edge_indices = [(cuts.index(a), cuts.index(b)) for a,b in OLD_EDGES]
    matrix = [[0]*len(OLD_EDGES) for _ in OLD_EDGES]
    for col, (start, end) in enumerate(OLD_EDGES):
        a, b = image_names[start], image_names[end]
        ensure(iterate(x[start], c, 4).overlaps(x[a]), "old edge start image")
        ensure(iterate(x[end], c, 4).overlaps(x[b]), "old edge end image")
        low, high = sorted((cuts.index(a), cuts.index(b)))
        for row, (j, k) in enumerate(edge_indices):
            if low <= j and k <= high:
                matrix[row][col] += 1   # ONCE per physical edge, not per side.
    # Derive the two inverse sheets of each old edge and identify the new one.
    sheets = []
    for name, (start, end) in zip(EDGE_NAMES, OLD_EDGES):
        na, nb = neg[start], neg[end]
        ensure(na.before(nb), "negative inverse edge orientation")
        # A sheet ending at the attachment root is attached in its interior.
        attached = na.before(x["x8"]) and (nb.before(x["x8"]) or nb.overlaps(x["x8"]))
        sheets.append({"edge":name,
                       "physical_source_sheets":[[symneg[start], symneg[end]],
                                                 [sympos[end], sympos[start]]],
                       "new_attachment_sheets":[bool(attached), False]})
    # Exact integer characteristic polynomial: det(t I - T).
    m = matrix
    trace = sum(m[i][i] for i in range(3))
    principal = (m[0][0]*m[1][1]-m[0][1]*m[1][0]
                 + m[0][0]*m[2][2]-m[0][2]*m[2][0]
                 + m[1][1]*m[2][2]-m[1][2]*m[2][1])
    determinant = (m[0][0]*(m[1][1]*m[2][2]-m[1][2]*m[2][1])
                   -m[0][1]*(m[1][0]*m[2][2]-m[1][2]*m[2][0])
                   +m[0][2]*(m[1][0]*m[2][1]-m[1][1]*m[2][0]))
    ensure((trace, principal, determinant) == (0, -2, 1),
           "Perron polynomial differs from physical edge counts")
    power = [row[:] for row in m]
    for _ in range(3):
        power = [[sum(power[i][k]*m[k][j] for k in range(3))
                  for j in range(3)] for i in range(3)]
    ensure(all(v > 0 for row in power for v in row), "edge graph not primitive")
    # For phi^2=phi+1, the positive LEFT eigenvector is (phi,1,phi).
    # Explicitly verify 2-component integer algebra a+b*phi.
    def phi_mul(pair: tuple[int,int]) -> tuple[int,int]:
        a,b = pair
        return (b, a+b)
    weights = [(0,1), (1,0), (0,1)]
    for j in range(3):
        lhs = (sum(weights[i][0]*m[i][j] for i in range(3)),
               sum(weights[i][1]*m[i][j] for i in range(3)))
        ensure(lhs == phi_mul(weights[j]), "Perron left-weight identity")
    ensure(sum(sum(row) for row in m) == 5, "wrong total old edge occurrences")
    return {"edges":EDGE_NAMES,
            "matrix_output_rows_input_columns":matrix,
            "characteristic_polynomial":"t^3-2*t-1=(t+1)*(t^2-t-1)",
            "perron_root":"(1+sqrt(5))/2",
            "strictly_positive_power":4,
            "inverse_edge_sheets":sheets}


def recompute(example: dict, parameter: dict) -> dict:
    ensure(example["return"] == {"physical_iterate":4, "restricted_degree":2,
                                  "global_degree":16}, "not primitive physical p=4")
    ensure(example["domains"]["target"]["radius"] == "1/16", "target radius changed")
    ensure(example["operations"]["covering"]["ideal_action"] == "f_*",
           "cover action not f_*")
    ensure(example["operations"]["immersion"]["ideal_action"] == "iota^*",
           "immersion action not iota^*")
    ensure(example["operations"]["covering"]["ideal_action"]
           != example["operations"]["immersion"]["ideal_action"],
           "cover and immersion actions conflated")
    ensure(example["source_contract"] ==
           "source_contracts/primitive4_record_fields.json#/records/PhysicalExample",
           "physical record contract changed")
    c, orbit = certify_parameter(parameter)
    p = parameter["parameter_bracket"]
    x = {"x"+str(k):a for k,a in enumerate(orbit)}
    x["alpha"] = isolate_alpha(c)
    ensure(x["x8"].before(x["x20"]) and x["x20"].before(x["x12"])
           and x["x12"].before(Box.rational(0))
           and Box.rational(0).before(x["x24"])
           and x["x24"].before(x["alpha"]) and x["alpha"].before(x["x16"])
           and x["x16"].before(x["x4"]), "three physical inner Julia phases overlap")
    ensure((-x["x4"]).before(x["x8"]), "no new attachment")
    ensure(x["x4"].before(Box.rational(R4)), "T not in U4")
    ensure(x["x24"].before(Box.rational(R12)), "K12 not in U12")
    f1 = Box(0, x["x4"].high).square()+c
    f2 = f1.square()+c
    f3 = f2.square()+c
    ensure(f1.high<0 and f2.low>0 and f3.low>0,
           "G derivative is not monotone on each half of Tprime")
    ensure(iterate(-x["x4"], c, 4).overlaps(x["x8"]), "left source tip image")
    ensure(iterate(x["x4"], c, 4).overlaps(x["x8"]), "right source tip image")
    ensure(iterate(Box.rational(0), c, 4).overlaps(x["x4"]), "critical image")
    rouche_degree_two(c, 4, RHO4, R4, Q(1,25))
    rouche_degree_two(c, 12, RHO12, R12, Q(1,100))
    den = 1 << p["denominator_power_of_two"]
    clo, chi = Q(p["lower_numerator"],den), Q(p["upper_numerator"],den)
    c0, cr = (clo+chi)/2, (chi-clo)/2
    primitive_phase_balls(c0, cr)
    # On [-x24,x24], all noncritical phase factors of f^12' have a
    # fixed nonzero sign, so f^12 has precisely the critical minimum at 0.
    span = Box(0, x["x24"].high)
    signs = [-1,1,1,1,-1,1,1,-1,-1,1,1]
    for sign in signs:
        span = span.square()+c
        ensure(span.high<0 if sign<0 else span.low>0,
               "inner Chebyshev interval derivative sign")
    ensure(iterate(x["x12"],c,12).overlaps(x["x24"]), "tip endpoint iteration")
    ensure(iterate(x["x24"],c,12).overlaps(x["x24"]), "tip fixed endpoint")
    names = example["marking"]["target_cuts"]
    ensure(names == ["x20","x12","x24","alpha","x16"],
           "marking order or old-edge convention changed")
    cuts = [x[s] for s in names]
    ensure(all(a.before(b) for a,b in zip(cuts,cuts[1:])),
           "target cuts not disjoint")
    # Strictly monotone inverse-branch bisection, not a saved atom table.
    neg = {name:negative_inverse(y,c,-x["x4"]) for name,y in zip(names,cuts)}
    symbolic_preimage = {"x20":"x16", "x12":"x8", "x24":"x20",
                         "alpha":"alpha", "x16":"x12"}
    symneg, sympos = {}, {}
    candidates = []
    for name in names:
        label = symbolic_preimage[name]
        root = x[label]
        wantneg = -root if root.low > 0 else root
        wantpos = root if root.low > 0 else -root
        ensure(neg[name].overlaps(wantneg), "inverse symbolic orbit mismatch")
        symneg[name] = "-"+label if root.low > 0 else label
        sympos[name] = label if root.low > 0 else ("x24" if label=="x12" else "-"+label)
        candidates += [(neg[name], symneg[name]), (-neg[name], sympos[name])]
    candidates.sort(key=lambda item:item[0].center())
    source_cuts = [a for a,_ in candidates]
    symbols = [n for _,n in candidates]
    ensure(all(a.before(b) for a,b in zip(source_cuts,source_cuts[1:])),
           "source inverse cuts overlap")
    cover, pulled, attached, src_zero = [], [], [], []
    for s in range(2*len(source_cuts)):
        real, side = source_sample(s,source_cuts,-x["x4"],x["x4"])
        box = Box.rational(real)
        mapped_side = side if real < 0 else -side
        cover.append(index_of(iterate(box,c,4),mapped_side,cuts))
        in_attachment = box.before(x["x8"])
        pulled.append(0 if in_attachment else index_of(box,side,cuts))
        if in_attachment:
            attached.append(s)
        if old_edge_for(box,x) is None:
            src_zero.append(s)
    blocks = cyclic_blocks(pulled,2*len(cuts))
    ensure(all(b[0] not in attached and b[-1] not in attached for b in blocks),
           "immersion block not end-proper")
    nonproper = [i for i,b in enumerate(blocks) if set(b)&set(attached)]
    ensure(nonproper == [0], "wrong nonproper immersion blocks")
    attached = [s for s in blocks[0] if s in attached]
    ensure(len(attached)==3, "attachment gate missing a side")
    ensure(all(cover.count(j)==2 for j in range(2*len(cuts))),
           "f_* no longer a degree-two cover")
    # Derive the old-edge census independently in target, source inclusion,
    # and after the COVER action: these are three different counts.
    target_zero = []
    for t in range(2*len(cuts)):
        real,_ = source_sample(t,cuts,x["x8"],x["x4"])
        if old_edge_for(Box.rational(real),x) is None:
            target_zero.append(t)
    pushed_zero = [s for s,t in enumerate(cover) if t in target_zero]
    edges = edge_analysis(x,c,neg,symneg,sympos)
    paths, circles = {}, []
    ensure(len(example["paths"])==2, "two path classes required")
    q = Q(example["paths"][0]["q"])
    ensure(all(Q(item["q"])==q for item in example["paths"]),
           "paths do not share target ideal endpoints")
    ensure(x["x20"].before(Box.rational(q))
           and Box.rational(q).before(-x["alpha"]), "q left the same marked base")
    for item in example["paths"]:
        w = Q(item["w"])
        circ = circle(q,w,c0,cr,Q(item["disk_limit"]),x["x4"])
        circ["name"]=item["name"]
        ensure((w < -x["x4"].center()) if item["name"]=="avoiding" else
               (-x["x4"].center()<w<x["x8"].center()), "path class altered")
        rows = restrictions(q,w,source_cuts,-x["x4"],x["x4"],x["x8"])
        for a,b in rows:
            ensure(len(short_arc(a,b,len(cover)))>2, "A.1 short source path")
            ensure(pulled[a]!=pulled[b], "A.3.2 path in one pullback block")
            ensure(len(short_arc(cover[a],cover[b],len(cuts)*2))>2,
                   "A.1 short covering image")
        paths[item["name"]] = {
            "source_restrictions":rows,
            "immersion_endpoint_pairs":[[pulled[a],pulled[b]] for a,b in rows],
            "covering_pushforward_pairs":[[cover[a],cover[b]] for a,b in rows],
            "surviving_count":len(rows),
            "filters":{"A1_short_span":True,"A3_2_not_in_one_pullback":True}}
        circles.append(circ)
    ensure(set(paths)=={"crossing","avoiding"}, "path class names changed")
    target_endpoints=[index_of(Box.rational(q),side,cuts) for side in (1,-1)]
    ensure(len(short_arc(*target_endpoints,len(cuts)*2))>2,
           "A.1 target path short")
    wave = example["wave"]
    center, r0, r1 = Q(wave["center"]), *map(Q,wave["open_radii"])
    ensure(0<r0<r1, "wave radii invalid")
    qr=Box(Box.rational(center+r0).low,Box.rational(center+r1).high)
    wr=Box(Box.rational(center-r1).low,Box.rational(center-r0).high)
    ensure(x["x20"].before(qr) and qr.before(-x["alpha"]),
           "whole wave endpoint range left its target base")
    ensure((-x["x4"]).before(wr) and wr.before(x["x8"]),
           "whole wave crossing range left attachment")
    ensure(source_cuts[0].before(wr) and wr.before(source_cuts[1]),
           "whole wave crossing range left source sheet")
    ensure(center==Q(circles[0]["center"]) and r1==Q(circles[0]["radius"]),
           "whole wave not enclosed by certified crossing disk")
    height = Q(wave["target_angular_height_pi"])
    child_height = Q(wave["child_angular_height_pi"])
    ensure(height==2 and child_height==1, "angular rectangle conventions drift")
    ratio=r1/r0
    parent_coeff=1/height
    child_coeff=1/child_height
    ensure(1/parent_coeff == 2/child_coeff,
           "symbolic harmonic series equality failed")
    pushed_bases=[short_arc(*pair,len(cuts)*2)
                  for pair in paths["crossing"]["covering_pushforward_pairs"]]
    base=short_arc(*target_endpoints,len(cuts)*2)
    ensure(all(len(b)==3 for b in [base]+pushed_bases),
           "Wave base lacks single crest atom")
    ensure(paths["crossing"]["surviving_count"]==2 and
           paths["avoiding"]["surviving_count"]==1,
           "physical marked breakage not 2 vs 1")
    all_crests=[base[1]]+[v[1] for v in pushed_bases]
    ensure(all(t in target_zero for t in all_crests),
           "claimed zero-old-edge Wave crest not a zero-edge atom")
    atom_names=["K2_terminal","edge_K2_K0_upper","K0_upper",
                "edge_K0_alpha_upper","edge_alpha_K1_upper",
                "K1_terminal","edge_alpha_K1_lower",
                "edge_K0_alpha_lower","K0_lower","edge_K2_K0_lower"]
    return {
        "polynomial":{"family":example["polynomial"]["family"],
                      "critical_point":"0","parameter_bracket":p,
                      "orbit_index_range":[0,36]},
        "return":{"physical_iterate":4,"restricted_degree":2,"global_degree":16},
        "domains":{"source":{"symbol":"V4",
                             "definition":"component(G^-1(U4),0)","degree":2},
                   "target":{"symbol":"U4","center":"0","radius":"1/16"},
                   "certificate":{"outer_rouche_margin_gt":"1/25",
                                  "inner_f12_rouche_margin_gt":"1/100",
                                  "primitive_four_phase_balls_disjoint":True}},
        "marked_tree":{"small_julia_intervals":["[x12,x24]","[x16,x4]","[x8,x20]"],
                       "hull":"[x8,x4]","preimage_in_V4":"[-x4,x4]",
                       "dividing_fixed_point":"alpha"},
        "attachment_census":{"complete_in_V4_given_degree_two":True,
                             "components":[{"interval":"[-x4,x8)","root":"x8",
                                            "boundary_atoms":attached,
                                            "immersion_boundary_destination":
                                            "target_interior_not_I0_boundary"}]},
        "ideal_boundary":{"target_atom_count":len(atom_names),
                          "target_atom_names":atom_names,
                          "target_real_cuts":names,
                          "covering_source_atom_count":len(cover),
                          "source_real_cuts":symbols,
                          "outer_component_atom_count":1},
        "operations":{"covering_f_star":{"action":"f_*","degree":2,
                                          "source_to_target":cover},
                      "immersion_iota_star":{"action":"iota^*",
                                              "source_to_pullback":pulled,
                                              "connected_blocks":blocks,
                                              "block_lengths":[len(b) for b in blocks],
                                              "end_proper_inner":True,
                                              "nonproper_target_atoms":nonproper}},
        "sheet_paths":{"endpoint_target_atoms":target_endpoints,
                       "circles":circles,"instances":paths,
                       "homotopy":"same_target_relative_ideal_endpoints",
                       "counts":[paths["crossing"]["surviving_count"],
                                 paths["avoiding"]["surviving_count"]]},
        "wave":{"center":str(center),"open_radii":[str(r0),str(r1)],
                "right_endpoint_range":[str(center+r0),str(center+r1)],
                "attachment_crossing_range":[str(center-r1),str(center-r0)],
                "target_base":base,"target_crest":base[1],
                "pushed_bases":pushed_bases,
                "pushed_crests":[b[1] for b in pushed_bases],
                "ratio":str(ratio),
                "target_width":f"log({ratio})/(2*pi)",
                "each_child_and_pushed_width":f"log({ratio})/pi",
                "child_multiplier":int(child_coeff/parent_coeff),
                "harmonic_series_equality":True,
                "symbolic_width_coefficients_in_log_ratio_over_pi":{
                    "target":"1/2","each_child":"1"}},
        "edge_transition":edges,
        "zero_edge_sectors":{"target_zero_old_edge_atoms":target_zero,
                             "source_inclusion_zero_old_edge_atoms":src_zero,
                             "cover_pushforward_zero_old_edge_atoms":pushed_zero,
                             "parent_and_child_wave_crests_zero_old_edge":True}
    }


def source_lock() -> dict:
    lock=load(LOCK)
    for item in lock["repository_files"]:
        path=REPO/item["path"]
        ensure(git_blob(path)==item["git_blob_sha1"],
               "period-four source lock mismatch: "+item["path"])
    return lock


def build_manifest(example: dict | None = None, parameter: dict | None = None) -> dict:
    lock=source_lock()
    if example is None:
        example=load(INPUT)
    if parameter is None:
        parameter=load(PARAMETER)
    output=recompute(example,parameter)
    return {"schema_version":1,"experiment_id":example["id"],
            "inputs":{"source_locks":lock["repository_files"],
                      "arxiv_source":lock["arxiv_source"],
                      "example_sha256":sha256(INPUT),
                      "parameter_certificate_sha256":sha256(PARAMETER),
                      "contracts_sha256":sha256(CONTRACT),
                      "lock_sha256":sha256(LOCK)},
            "code":{"file":"research/native_wave_transfer/regenerate_period4.py",
                    "sha256":sha256(Path(__file__))},
            "outputs":output,
            "outputs_sha256":hashlib.sha256(canonical(output)).hexdigest(),
            "proof_status":{
                "certified_by_exact_arithmetic":[
                    "unique degree-160 dyadic parameter root with derivative sign",
                    "two complex quadratic-like degree-two Rouché enclosures",
                    "disjoint four physical phase balls; primitive p=4 return",
                    "real interval phase orders and complete two-sheet inverse cuts",
                    "one attached component given the central degree-two map",
                    "separate covering and immersion and filtered 2/1 restrictions",
                    "one occurrence per real old edge and exact phi Perron identity",
                    "zero old-edge census on source, target, and covering images",
                    "closed four-iterate disks and entire wave endpoint ranges",
                    "rational coefficients of the symbolic harmonic width equality"],
                "conditional_on_cited_analytic_inputs":[
                    "real Chebyshev tip filled-Julia interval from the inner f12 portrait",
                    "slit-side prime-end boundary marking and KKL Proposition 6.5",
                    "KKL shortness and proper restriction semantics",
                    "relative ideal endpoint homotopy of the two circles",
                    "extremal-width rectangle and conformal-invariance identification"],
                "numeric_only":[],
                "unproved":[
                    "non-locally-connected canonical KL localization",
                    "closed crest transport and zero-edge subsector escape",
                    "general strict Wave gain or MLC"]}}


def main() -> None:
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--check",action="store_true",help="default; read-only freeze check")
    ap.add_argument("--write",action="store_true",help="explicitly re-freeze manifest")
    args=ap.parse_args()
    ensure(not (args.check and args.write),"check/write mutually exclusive")
    computed=canonical(build_manifest())
    if args.write:
        MANIFEST.write_bytes(computed)
        print("WROTE",MANIFEST)
    else:
        ensure(MANIFEST.read_bytes()==computed,"primitive4 immutable manifest mismatch")
        print("PASS: physical p=4 degree 2, 10/20 atoms, full attachment, "
              "2/1 restrictions, old edge phi, zero crests, harmonic Wave equality")


if __name__=="__main__":
    main()
