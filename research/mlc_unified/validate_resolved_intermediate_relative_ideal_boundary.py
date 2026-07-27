"""Focused audit for the resolved relative ideal-boundary theorem.

The analytic proof is in
resolved_intermediate_relative_ideal_boundary.md.  This validator locks
the primary source files, checks finite algebraic controls for the split
group/fiber identities, checks the elementary strip obstruction, and
audits ledger routing and global open statuses.  These computations are
diagnostic only and do not replace the Fuchsian-group or boundary proofs.
"""

from __future__ import annotations

import cmath
import hashlib
import json
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parent
DOC = ROOT / "resolved_intermediate_relative_ideal_boundary.md"
KAHN_WAD = ROOT / ".tmp_kl06_source" / "wad.tex"
KAHN_PSI = ROOT / ".tmp_kl06_source" / "psiql2.tex"
KL = ROOT / ".tmp_kl08_source" / "psiql.tex"
KL_MODULI = ROOT / ".tmp_kl08_source" / "moduli.tex"
KKL = ROOT / ".tmp_wave_audit" / "waves-with-Misha.tex"
LEDGER = ROOT / "proof_obligations.json"
OUT = ROOT / "resolved_intermediate_relative_ideal_boundary_validation_20260726.json"

EXPECTED_SHA = {
    KAHN_WAD: "B5DF40A5D33B6B590B430D47693514088AF6FC287BAA5D87B4D11015B990E580",
    KAHN_PSI: "E4EFCCEC65D8C9C2BDFE2AF8203B3D4D63ECF992B40D302F56FBA78259547228",
    KL: "6CC9726461473812A5FBA93377F2DC0B088DB6CAC4B9DE90C7B2AE625DFB49AF",
    KL_MODULI: "CBDB9EF7D6AC94C33FDB0AB7167E19C39EB23D27373C266A296CF6031E0CAF7E",
    KKL: "AD4C774806D9902AA54FA31C56AD6146D8034946F19CC5E9CEC3C51A3F94FDD5",
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def require(text: str, needle: str, label: str) -> None:
    if needle not in text:
        raise AssertionError(f"missing {label}: {needle!r}")


def split_group_control() -> dict[str, object]:
    """Finite control for G=N x H and the fiber/coset bijection.

    The finite direct product is not a Fuchsian model.  It checks only the
    algebraic decomposition and cardinality statements used in Sections
    4--5 of the proof.
    """

    n_order = 5
    h_order = 7
    group = {
        (n, h)
        for n in range(n_order)
        for h in range(h_order)
    }
    kernel = {(n, 0) for n in range(n_order)}
    section = {(0, h) for h in range(h_order)}

    decompositions: dict[tuple[int, int], tuple[tuple[int, int], tuple[int, int]]] = {}
    for g in group:
        n_part = (g[0], 0)
        h_part = (0, g[1])
        if ((n_part[0] + h_part[0]) % n_order,
            (n_part[1] + h_part[1]) % h_order) != g:
            raise AssertionError("split decomposition failed")
        decompositions[g] = (n_part, h_part)

    if kernel & section != {(0, 0)}:
        raise AssertionError("kernel/section intersection is not trivial")

    # Left cosets of H are indexed by the N coordinate.
    cosets = {
        frozenset(
            {
                (n, h)
                for h in range(h_order)
            }
        )
        for n in range(n_order)
    }
    if len(cosets) != n_order:
        raise AssertionError("coset/fiber cardinality control failed")

    one_sheet_group = {(0, h) for h in range(h_order)}
    one_sheet_kernel = {(0, 0)}
    if len(one_sheet_group) // len(section) != 1 or len(one_sheet_kernel) != 1:
        raise AssertionError("one-sheet branch control failed")

    return {
        "group_order": len(group),
        "kernel_order": len(kernel),
        "section_order": len(section),
        "coset_count": len(cosets),
        "unique_decomposition_count": len(decompositions),
        "one_sheet_kernel_order": len(one_sheet_kernel),
    }


def strip_obstruction_control() -> dict[str, object]:
    """Check only the explicit exponential-cover identities in Model 6.4."""

    y_values = [0.2, 0.5, 0.8]
    translations = [0, 1, 2, 7, 31]
    values: dict[str, list[list[float]]] = {}

    for y in y_values:
        orbit = [cmath.exp(2j * cmath.pi * complex(n, y)) for n in translations]
        if max(abs(value - orbit[0]) for value in orbit) > 1e-12:
            raise AssertionError("deck-translation invariance failed")
        values[str(y)] = [[value.real, value.imag] for value in orbit]

    base_values = [cmath.exp(-2 * cmath.pi * y) for y in y_values]
    if len({round(value.real, 12) for value in base_values}) != len(y_values):
        raise AssertionError("distinct heights should give distinct quotient points")

    return {
        "translations": translations,
        "heights": y_values,
        "orbit_values": values,
        "distinct_radial_values": [value.real for value in base_values],
        "interpretation": (
            "All translated sequences approach one standalone wrapping end, "
            "while their constant quotient values depend on height."
        ),
    }


def main() -> None:
    for path, expected in EXPECTED_SHA.items():
        actual = sha256(path)
        if actual != expected:
            raise AssertionError(
                f"source hash mismatch for {path}: {actual} != {expected}"
            )

    wad = KAHN_WAD.read_text(encoding="utf-8", errors="replace")
    psi = KAHN_PSI.read_text(encoding="utf-8", errors="replace")
    kl = KL.read_text(encoding="utf-8", errors="replace")
    kl_moduli = KL_MODULI.read_text(encoding="utf-8", errors="replace")
    kkl = KKL.read_text(encoding="utf-8", errors="replace")
    doc = DOC.read_text(encoding="utf-8")

    for needle in [
        "For the rest of this paper, we will assume that this is the case.",
        "We let $\\hat S = \\cl \\D \\sm \\Lambda$",
        "We let $\\di \\hat S = \\pi^{-1}(\\di S) = \\di \\D \\sm \\Lambda$",
    ]:
        require(wad, needle, "Kahn ideal-boundary source")

    for needle in [
        "the latter map has degree 1",
        "A local marked Riemann surface",
    ]:
        require(psi, needle, "Kahn annulus/localization source")

    for needle in [
        "$\\hat A_i$ stands for a copy of $\\hat A$",
        "These embeddings extend to immersions $\\hat A_i\\ra \\hat B_j$",
        "the arcs $\\la_i$ form the {\\it outer boundary }",
        "$\\i(\\di \\BY)$ is not contained in $\\di\\BZ$",
    ]:
        require(kl, needle, "KL composite-boundary source")

    for needle in [
        "the group of deck transformations is generated by",
        "translation $z\\mapsto z+1$",
        "covers the $O$-boundary",
    ]:
        require(kl_moduli, needle, "KL strip/wrapping source")

    for needle in [
        "\\ddi \\VV:= (\\dD\\sm \\Lambda)/ \\Delta",
        "open and dense subset",
        "proper} on some $X'",
    ]:
        require(kkl, needle, "KKL relative-ideal source")

    for needle in [
        "Theorem 6.2 -- no extension through a deck-limit point",
        "Corollary 6.4 -- no extension of a nonconstant invariant composite",
        "Theorem 7.1 -- resolved full-boundary dichotomy",
        "Lemma 8.1 -- normal-kernel wrapping collision",
        "Theorem 8.3 -- actual KL whole-tile factorization is one-sheeted",
        "Theorem 9.1 -- cover-relative boundary descent",
        "\\mathfrak B_a",
        "\\chi_{\\rm hit}",
        "\\chi_{\\rm edge}",
        "deck-limit missing end",
        "K_a",
        "L_a\\Phi_a^{-1}",
        "K_a=e_aq_a",
        "\\overline\\Phi_a(\\omega_-)=\\zeta_-",
        "\\overline\\Phi_a(\\omega_+)=\\zeta_+",
        "Canonical/KL relation proper-end response",
        "VAAPC-I",
        "UPTCR",
        "MLC remain open",
    ]:
        require(doc, needle, "proof document")

    algebra = split_group_control()
    strip = strip_obstruction_control()

    ledger = json.loads(LEDGER.read_text(encoding="utf-8"))
    obligations = ledger["obligations"]
    by_id = {item["id"]: item for item in obligations}
    theorem_id = "RESOLVED_INTERMEDIATE_RELATIVE_IDEAL_BOUNDARY"
    theorem = by_id[theorem_id]
    if theorem["status"] != "proved":
        raise AssertionError(f"{theorem_id} must be proved")
    for dependency in [
        "KL_LOCALIZATION_SHEET_RESOLUTION_FACTORIZATION",
        "KAHN_ITERATE_COMPLEMENTARY_COMPONENT_ALIGNMENT",
    ]:
        if dependency not in theorem["dependencies"]:
            raise AssertionError(f"{theorem_id} is missing {dependency}")

    footprint = by_id["DIRECT_DECORATION_OUTER_CAP_FOOTPRINT"]
    if footprint["status"] != "open":
        raise AssertionError("DIRECT_DECORATION_OUTER_CAP_FOOTPRINT must remain open")
    if theorem_id not in footprint["dependencies"]:
        raise AssertionError("outer-footprint gate is missing relative-boundary dependency")

    global_ids = [
        "VIRTUAL_AUGMENTED_ATOM_PORT_CERTIFICATE",
        "UNIVERSAL_PROTECTED_TOWER_CLOSURE",
        "MLC",
    ]
    for item_id in global_ids:
        if by_id[item_id]["status"] != "open":
            raise AssertionError(f"{item_id} must remain open")

    counts = Counter(item["status"] for item in obligations)
    expected_counts = Counter({"proved": 235, "open": 72, "imported": 23})
    if len(obligations) != 330 or counts != expected_counts:
        raise AssertionError(
            f"unexpected ledger state: total={len(obligations)}, counts={counts}"
        )

    report = {
        "scope": (
            "Diagnostic source-lock, split-group/fiber control, explicit strip "
            "obstruction, ledger routing, and global-status audit.  The analytic "
            "deck-limit and relative quotient proofs remain in the proof document."
        ),
        "sources": {
            str(path.relative_to(ROOT)): sha256(path)
            for path in EXPECTED_SHA
        },
        "proof_document_sha256": sha256(DOC),
        "ledger_sha256": sha256(LEDGER),
        "finite_controls": {
            "split_group": algebra,
            "strip_obstruction": strip,
        },
        "ledger": {
            "total": len(obligations),
            "counts": dict(counts),
            "theorem": theorem_id,
            "global_statuses": {
                item_id: by_id[item_id]["status"]
                for item_id in global_ids
            },
        },
        "result": "PASS",
    }
    OUT.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"result": "PASS", "output": str(OUT)}, indent=2))


if __name__ == "__main__":
    main()
