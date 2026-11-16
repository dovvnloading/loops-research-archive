#!/usr/bin/env python3
"""Conservative v2 satellite contact and real Markov certificate (not a Wave theorem).

Pure rational root/interval and polynomial-identity computations; no floating point.
The independent v1 refusal and primitive files are read but never modified.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
INPUT = HERE / "physical_examples/satellite2_misiurewicz_tip_refusal.json"
REGISTRY = HERE / "source_contracts/satellite_v2_field_sources.json"
SPEC = HERE / "SPECIFICATION_v2_satellite.md"
MANIFEST = HERE / "experiment_manifests/satellite2_misiurewicz_v2.json"
BASELINES = {
    "p3": "experiment_manifests/tip_pr68.json",
    "p4": "experiment_manifests/primitive4_tip12.json",
}
V1_BLOBS = {
    "experiment_manifests/tip_pr68.json": "39233f576e7de78cf707b4d616177d0313b98b25",
    "experiment_manifests/primitive4_tip12.json": "abcc01ad0b5ab0b59cd46e9d080ce44141603392",
}


def require(ok: bool, message: str) -> None:
    if not ok:
        raise AssertionError(message)


def canonical(obj: object) -> bytes:
    return (json.dumps(obj, sort_keys=True, indent=2, ensure_ascii=True) + "\n").encode("utf-8")


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def blob_sha(path: Path) -> str:
    data = path.read_bytes()
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def P(c: Q) -> Q:
    return c**3 + 2*c*c + 2*c + 2


def mul(x: list[int], y: list[int]) -> list[int]:
    result = [0] * (len(x) + len(y) - 1)
    for i, xi in enumerate(x):
        for j, yj in enumerate(y):
            result[i+j] += xi*yj
    return result


def reduce_mod_P(coefficients: list[int]) -> tuple[int, int, int]:
    p = coefficients[:] + [0] * max(0, 3-len(coefficients))
    for k in range(len(p)-1, 2, -1):
        factor = p[k]
        p[k] = 0
        # c^3 = -2c^2 - 2c - 2
        for j in range(3):
            p[k-3+j] -= 2*factor
    return tuple(p[:3])


def mat_mul(a: list[list[int]], b: list[list[int]]) -> list[list[int]]:
    return [[sum(a[i][k]*b[k][j] for k in range(len(a)))
             for j in range(len(b[0]))] for i in range(len(a))]


def exact_case(fixture: dict) -> dict:
    """All positive numerical comparisons are over Q and are strict."""
    require(set(fixture)=={"first_incompatible_field", "format", "id",
           "not_asserted", "parameter", "purpose", "record_compatibility",
           "refusal_reason", "renormalization"}, "unknown satellite input field")
    p, r = fixture["parameter"], fixture["renormalization"]
    require(set(p)=={"denominator_power_of_two", "equation", "family",
                        "lower_numerator", "orbit_notation", "upper_numerator"}
            and fixture["record_compatibility"]=="refused"
            and fixture["first_incompatible_field"]==
                "MarkedHubbardTree.small_julia_intervals",
            "v1 semantic refusal must be preserved")
    require(fixture["format"] == "native-wave-transfer-satellite-tip-refusal/v1"
            and p["family"] == "z^2+c"
            and p["equation"] == "c^3+2*c^2+2*c+2=0", "source parameter drift")
    require(r == {"physical_iterate": 2, "global_degree": 4,
                  "restricted_degree": 2, "target": "D(0,1)",
                  "source": "component((f^2)^-1(D(0,1)),0)"},
            "degree/domain drift")
    n = int(p["denominator_power_of_two"])
    lower = int(p["lower_numerator"])
    upper = int(p["upper_numerator"])
    require(n == 128 and upper == lower+1, "root isolator drift")
    c0, c1 = Q(lower, 2**n), Q(upper, 2**n)
    require(Q(-31, 20) < c0 < c1 < Q(-3, 2)
            and P(c0) < 0 < P(c1), "strict real root enclosure drift")
    # P'(x)=3(x+2/3)^2+2/3 > 0 globally.
    a0, a1 = c1*c1+c1, c0*c0+c0  # c<-1/2: a(c) decreases
    require(Q(4,5) < a0 < a1 < Q(9,10)
            and c1 < -a1 < -a0 < 0 < a0
            and a1 < 1 and a0-c1 > 1, "phase order or outer inverse drift")
    require(-2*c1-a1-2 > Q(1,5), "central return Rouché drift")
    require(4*a0*a0 > 2, "contact fixed point not repelling")

    # f(a)=-a modulo P, with a=c^2+c; f(-a)=-a as well.
    a_poly = [0,1,1]
    f_a_plus_a = mul(a_poly, a_poly)
    f_a_plus_a[0] += 0  # explicit constant term for readability
    f_a_plus_a[1] += 2  # c from f(a) plus c from a
    f_a_plus_a[2] += 1
    require(reduce_mod_P(f_a_plus_a) == (0,0,0),
            "fixed-contact polynomial identity drift")
    # G(z)+a = (z^2-a^2)(z^2-c^2) modulo P.
    # The outer roots +/-c lie outside |z|=1; the source has exactly +/-a.
    a_sq = mul(a_poly, a_poly)
    coefficient = a_sq[:]
    coefficient[1] += 2  # a^2 + c^2 + 2c = 0
    coefficient[2] += 1
    require(reduce_mod_P(coefficient)==(0,0,0), "G contact factor coefficient drift")
    constant = mul(a_sq, [0,0,1])  # a^2*c^2 - 2a = 0
    constant[1] -= 2
    constant[2] -= 2
    require(reduce_mod_P(constant)==(0,0,0), "G contact factor constant drift")
    # G'(z)=4z(z^2+c); at +/-a, z^2+c=-a, hence +/-4a^2 nonzero.
    require(a0 > 0 and a0-c1 > 1, "contact inverse germs degenerate")

    # Real ambient Hubbard-tree partition, output edges in row order.
    # E0=[c,-a], E1=[-a,0], E2=[0,a].
    # Exact vertex order c < -a < 0 < a; endpoint images are
    # f(c)=a, f(-a)=-a, f(0)=c, f(a)=-a.
    vertex_image = [3,1,0,1]
    edge_endpoints = [(0,1),(1,2),(2,3)]
    edge_images = [list(range(min(vertex_image[x],vertex_image[y]),
                              max(vertex_image[x],vertex_image[y])))
                   for x,y in edge_endpoints]
    m = [[int(i in edge_images[j]) for j in range(3)] for i in range(3)]
    require(m == [[0,1,1],[1,0,0],[1,0,0]], "Markov orientation drift")
    m3 = mat_mul(mat_mul(m,m),m)
    require(m3 == [[2*x for x in row] for row in m], "spectral polynomial drift")

    return {
        "parameter_and_return": {
            "equation": p["equation"],
            "bracket": [str(lower), str(upper), n],
            "central_map": "G=f^2:V->U; U=D(0,1); V=component(G^-1(U),0)",
            "restricted_degree": 2,
        },
        "bouquet": {
            "critical_phase": "K0=[-a,a]",
            "next_phase": "K1=f(K0)=[c,-a]",
            "phase_intersection": "K0 intersect K1={-a}",
            "contact_point": "-a",
            "contact_period_f": 1,
            "phase_cycle_under_f": ["K0->K1", "K1->K0"],
            "rotation_number_f": "1/2",
            "contact_multiplier_sign_f": "negative",
            "ambient_hull": "[c,a]",
            "ambient_contact_accesses": ["upper", "lower"],
            "return_slit_tip_access_count": 1,
        },
        "attachments": {
            "return_tree_T": "[-a,a]",
            "central_pullback_Tprime": "[-a,a]",
            "new_components": [],
            "phase_contacts_not_attachments": ["-a"],
        },
        "contact_germs": {
            "covering": "local f_* from G:V\\K0 -> U\\K0; no full atom table",
            "covering_preimages": ["-a", "+a"],
            "covering_local_degrees": [1,1],
            "covering_endpoint_germs": 2,
            "immersion": "local iota^* from inclusion V\\K0 -> U\\K0; no full pullback table",
            "immersion_preimages": ["-a"],
            "immersion_local_degrees": [1],
            "immersion_endpoint_germs": 1,
            "through_deleted_contact_proper_paths": 0,
            "global_filtered_proper_restrictions": None,
            "global_ideal_atom_tables": None,
        },
        "ambient_markov": {
            "vertices": ["c", "-a", "0", "a"],
            "edges": ["[c,-a]", "[-a,0]", "[0,a]"],
            "edge_images": edge_images,
            "matrix_output_rows_input_columns": m,
            "characteristic_polynomial": "t*(t^2-2)",
            "perron_root": "sqrt(2)",
            "operator_scope": "ambient_real_Hubbard_tree; NOT KKL_old_edge_operator",
        },
        "wave": {
            "satellite_marked_wave": None,
            "parent_exact_width": None,
            "children_exact_widths": None,
            "harmonic_width_transfer": "undetermined",
            "width_degradation_forced": None,
        },
    }



def validate_semantics(outputs: dict) -> None:
    """Fail closed if a topology certificate is relabelled as Wave data."""
    b=outputs["bouquet"]
    a=outputs["attachments"]
    g=outputs["contact_germs"]
    e=outputs["ambient_markov"]
    w=outputs["wave"]
    require(b["rotation_number_f"]=="1/2" and
            b["phase_intersection"]=="K0 intersect K1={-a}" and
            b["ambient_contact_accesses"]==["upper","lower"] and
            b["return_slit_tip_access_count"]==1,
            "satellite phase/prime-end identification drift")
    require(a["new_components"]==[] and a["phase_contacts_not_attachments"]==["-a"],
            "contact must not be rewritten as an attachment")
    require(g["covering_preimages"]==["-a","+a"] and
            g["immersion_preimages"]==["-a"] and
            g["covering_local_degrees"]==[1,1] and
            g["immersion_local_degrees"]==[1] and
            g["covering_endpoint_germs"]==2 and
            g["immersion_endpoint_germs"]==1 and
            g["covering"]!=g["immersion"] and
            g["through_deleted_contact_proper_paths"]==0,
            "covering/immersion contact distinction drift")
    require(g["global_filtered_proper_restrictions"] is None and
            g["global_ideal_atom_tables"] is None,
            "fabricated global satellite proper-path/atom results")
    require(e["matrix_output_rows_input_columns"]==[[0,1,1],[1,0,0],[1,0,0]] and
            e["perron_root"]=="sqrt(2)" and "NOT KKL" in e["operator_scope"],
            "ambient Markov invariant must not become KKL Wave operator")
    require(w=={"satellite_marked_wave":None, "parent_exact_width":None,
            "children_exact_widths":None, "harmonic_width_transfer":"undetermined",
            "width_degradation_forced":None},
            "no source-defined satellite Wave widths or transfer theorem")

def primitive_comparison() -> dict:
    projection = {}
    for name, rel in BASELINES.items():
        require(blob_sha(HERE/rel) == V1_BLOBS[rel], "baseline blob drift: "+rel)
        data = json.loads((HERE/rel).read_text(encoding="utf-8"))["outputs"]
        waves = data["wave"]
        paths = data["sheet_paths"]
        attachments = data["attachment_census"]["components"]
        require(len(attachments)==1 and paths["counts"]==[2,1]
                and waves["harmonic_series_equality"] is True,
                "baseline numeric comparison drift: "+name)
        projection[name] = {
            "attachments": len(attachments),
            "proper_restrictions_crossing_avoiding": paths["counts"],
            "parent_width": waves["target_width"],
            "each_child_width": waves["each_child_and_pushed_width"],
            "harmonic_equality": waves["harmonic_series_equality"],
        }
    return projection


def leaf_paths(obj: object, prefix: str="") -> set[str]:
    if isinstance(obj, dict):
        paths = set()
        for k,v in obj.items():
            paths.update(leaf_paths(v, f"{prefix}.{k}" if prefix else k))
        return paths
    return {prefix}


def validate_sources(outputs: dict, registry: dict) -> None:
    require(registry["format"]=="native-wave-transfer-satellite-v2-field-sources"
            and registry["schema_version"]==2, "field registry format drift")
    definitions = registry["definitions"]
    sources = registry["sources"]
    require(leaf_paths(outputs)==set(definitions),
            "incomplete or extra source citation fields: " +
            str(sorted(leaf_paths(outputs)^set(definitions))))
    for path, definition in definitions.items():
        if path.startswith("wave.") or path in (
            "contact_germs.global_filtered_proper_restrictions",
            "contact_germs.global_ideal_atom_tables"):
            require(definition["status"]=="unformalized"
                    and "OPEN" in definition["source_ids"],
                    "no published satellite Wave/filtration: "+path)
        require(definition["status"] in ("published", "exact-derived", "unformalized")
                and bool(definition["source_ids"])
                and all(s in sources for s in definition["source_ids"]),
                "field missing explicit source/status: " + path)


def make_manifest(fixture: dict) -> dict:
    out = exact_case(fixture)
    out["primitive_comparison"] = primitive_comparison()
    validate_semantics(out)
    registry = json.loads(REGISTRY.read_text(encoding="utf-8"))
    validate_sources(out,registry)
    return {
        "format": "native-wave-transfer-satellite-v2-manifest",
        "schema_version": 2,
        "experiment_id": "satellite2_misiurewicz_tip_contact_v2",
        "inputs": {
            "fixture_sha256": sha256(INPUT),
            "registry_sha256": sha256(REGISTRY),
            "specification_sha256": sha256(SPEC),
            "unchanged_v1_blobs": {k:V1_BLOBS[k] for k in BASELINES.values()},
        },
        "code": {"path": "research/native_wave_transfer/regenerate_satellite_v2.py",
                 "sha256": sha256(Path(__file__))},
        "outputs": out,
        "outputs_sha256": hashlib.sha256(canonical(out)).hexdigest(),
        "proof_status": {
            "exact": ["parameter and phase order by rational signs",
                      "reduced polynomial identities and real Markov image census",
                      "contact local derivatives, unramified covering and inclusion germs",
                      "ambient Markov characteristic polynomial and Perron root sqrt(2)"],
            "cited_but_unformalized": ["complex small filled Julia identification from v1",
                      "satellite bouquet and rotation interpretation",
                      "Caratheodory slit access and local endpoint proper-lift interpretation"],
            "numerical_only": [],
            "open": ["global satellite ideal atlas and KKL iota* pullback blocks",
                     "global contact-filtration multiplicities",
                     "satellite marked Wave and extremal widths",
                     "width preservation, loss, or forced degradation"],
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--write",action="store_true",help="explicitly regenerate immutable v2 manifest")
    group.add_argument("--check",action="store_true",help="read-only manifest check (default)")
    group.add_argument("--print-manifest",action="store_true")
    args=parser.parse_args()
    example=json.loads(INPUT.read_text(encoding="utf-8"))
    computed=canonical(make_manifest(example))
    if args.print_manifest:
        print(computed.decode("utf-8"),end="")
    elif args.write:
        MANIFEST.write_bytes(computed)
        print("WROTE",MANIFEST)
    else:
        require(MANIFEST.read_bytes()==computed,"immutable satellite v2 manifest drift")
        print("PASS: satellite v2 contact/germ/ambient Markov; Wave undefined")

if __name__=="__main__":
    main()
