"""Focused validation for the canonical/KL whole-tile comparison no-go.

The analytic proof is in
canonical_resolution_kl_tile_correspondence_no_go.md.  This validator
locks the cited source files, checks the exact non-covering immersion
control, checks theorem/repair markers, and audits ledger routing and
global open statuses.  It is diagnostic and does not replace the
deck-limit proof.
"""

from __future__ import annotations

import cmath
import hashlib
import json
import math
from collections import Counter
from pathlib import Path


ROOT = Path(__file__).resolve().parent
DOC = ROOT / "canonical_resolution_kl_tile_correspondence_no_go.md"
KAHN_WAD = ROOT / ".tmp_kl06_source" / "wad.tex"
KL_PSI = ROOT / ".tmp_kl08_source" / "psiql.tex"
KL_MODULI = ROOT / ".tmp_kl08_source" / "moduli.tex"
LEDGER = ROOT / "proof_obligations.json"
OUT = (
    ROOT
    / "canonical_resolution_kl_tile_correspondence_no_go_validation_20260725.json"
)

EXPECTED_SHA = {
    KAHN_WAD: "B5DF40A5D33B6B590B430D47693514088AF6FC287BAA5D87B4D11015B990E580",
    KL_PSI: "6CC9726461473812A5FBA93377F2DC0B088DB6CAC4B9DE90C7B2AE625DFB49AF",
    KL_MODULI: "CBDB9EF7D6AC94C33FDB0AB7167E19C39EB23D27373C266A296CF6031E0CAF7E",
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest().upper()


def require(text: str, needle: str, label: str) -> None:
    if needle not in text:
        raise AssertionError(f"missing {label}: {needle!r}")


def immersion_control() -> dict[str, object]:
    """Check the exact formulas in the non-covering positive control."""

    z_plus = complex(0.0, math.pi / 4.0)
    z_minus = complex(0.0, -math.pi / 4.0)

    def f(z: complex) -> complex:
        return cmath.exp(4.0 * (z - 1.0))

    value_plus = f(z_plus)
    value_minus = f(z_minus)
    expected = -math.exp(-4.0)
    if abs(value_plus - value_minus) > 1e-14:
        raise AssertionError("the two stated points are not in one fiber")
    if abs(value_plus - expected) > 1e-14:
        raise AssertionError("the exact collision value is wrong")

    samples = [
        complex(0.0, 0.0),
        complex(0.5, 0.0),
        complex(-0.5, 0.0),
        complex(0.0, 0.9),
        complex(0.7, 0.6),
    ]
    if any(abs(z) >= 1.0 for z in samples):
        raise AssertionError("a test point left the unit disk")
    if any(abs(f(z)) >= 1.0 for z in samples):
        raise AssertionError("the model did not map a sample into the unit disk")
    derivatives = [4.0 * f(z) for z in samples]
    if any(abs(value) == 0.0 for value in derivatives):
        raise AssertionError("the model derivative vanished")

    translation = complex(0.0, -math.pi / 2.0)
    translated_plus = z_plus + translation
    if abs(translated_plus - z_minus) > 1e-14:
        raise AssertionError("the forced local translation is wrong")
    witness = complex(0.9, 0.0)
    if abs(witness) >= 1.0 or abs(witness + translation) <= 1.0:
        raise AssertionError("translation non-automorphism witness failed")

    return {
        "z_plus": [z_plus.real, z_plus.imag],
        "z_minus": [z_minus.real, z_minus.imag],
        "common_value": [value_plus.real, value_plus.imag],
        "expected_common_value": expected,
        "minimum_sample_derivative_modulus": min(abs(value) for value in derivatives),
        "forced_translation": [translation.real, translation.imag],
        "translation_exit_witness": {
            "source": [witness.real, witness.imag],
            "translated_modulus": abs(witness + translation),
        },
        "interpretation": (
            "The map is a noninjective holomorphic immersion of the disk "
            "into the disk with continuous closed-disk values, but the "
            "forced fiber translation is not a disk automorphism."
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
    psi = KL_PSI.read_text(encoding="utf-8", errors="replace")
    moduli = KL_MODULI.read_text(encoding="utf-8", errors="replace")
    doc = DOC.read_text(encoding="utf-8")

    for needle in [
        "We let $\\hat S = \\cl \\D \\sm \\Lambda$",
        "We let $\\di \\hat S = \\pi^{-1}(\\di S) = \\di \\D \\sm \\Lambda$",
    ]:
        require(wad, needle, "Kahn relative ideal boundary")

    for needle in [
        "$\\hat A_i$ stands for a copy of $\\hat A$",
        "wraps around $K(f)$ infinitely many times",
        "extends continuously to the boundary",
    ]:
        require(psi, needle, "KL tile and wrapping boundary")

    for needle in [
        "translation $z\\mapsto z+1$",
        "covers the $O$-boundary",
    ]:
        require(moduli, needle, "KL strip model")

    for needle in [
        "Theorem 5.1 -- no end-compatible square with nontrivial kernel",
        "Corollary 5.2 -- canonical infinite resolution is not a whole KL tile",
        "\\mathfrak C_{\\rm whole}",
        "\\chi_{\\rm corr}",
        "Proper interior or collar restriction",
        "Non-covering immersion or relation-valued comparison",
        "Trivial-kernel positive control",
        "F(z)=\\exp(4(z-1))",
        "CANONICAL_KL_WHOLE_TILE_CORRESPONDENCE_NO_GO",
        "MLC remain open",
    ]:
        require(doc, needle, "proof document")

    control = immersion_control()

    ledger = json.loads(LEDGER.read_text(encoding="utf-8"))
    obligations = ledger["obligations"]
    by_id = {item["id"]: item for item in obligations}
    theorem_id = "CANONICAL_KL_WHOLE_TILE_CORRESPONDENCE_NO_GO"
    theorem = by_id[theorem_id]
    if theorem["status"] != "proved":
        raise AssertionError(f"{theorem_id} must be proved")
    for dependency in [
        "KL_LOCALIZATION_SHEET_RESOLUTION_FACTORIZATION",
        "KL_PSEUDOPIECE_CONFORMAL_IDEAL_BOUNDARY",
        "RESOLVED_INTERMEDIATE_RELATIVE_IDEAL_BOUNDARY",
    ]:
        if dependency not in theorem["dependencies"]:
            raise AssertionError(f"{theorem_id} is missing {dependency}")

    footprint = by_id["DIRECT_DECORATION_OUTER_CAP_FOOTPRINT"]
    if footprint["status"] != "open":
        raise AssertionError("DIRECT_DECORATION_OUTER_CAP_FOOTPRINT must be open")
    if theorem_id not in footprint["dependencies"]:
        raise AssertionError("outer-footprint gate is missing comparison no-go")

    global_ids = [
        "VIRTUAL_WAVE_MARKED_CORRESPONDENCE",
        "VIRTUAL_WAVE_HORIZON_CERTIFICATE",
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
            "Source-lock, theorem-marker, explicit non-covering immersion, "
            "ledger-routing, and global-status validation.  The analytic "
            "deck-limit proof remains in the proof document."
        ),
        "sources": {
            str(path.relative_to(ROOT)): sha256(path)
            for path in EXPECTED_SHA
        },
        "proof_document_sha256": sha256(DOC),
        "ledger_sha256": sha256(LEDGER),
        "finite_controls": {"noncovering_immersion": control},
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
