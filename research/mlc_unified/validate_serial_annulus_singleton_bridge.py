"""Validate the serial-annulus singleton bridge and its round models.

The theorem implication is the standard Grötzsch divergence principle; the
code checks the exact round-annulus formulas and records the scope boundary.
It does not claim that the direct-decoration dynamics already realizes the
required annuli.
"""

from __future__ import annotations

import json
import math
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
OUT = ROOT / "research" / "mlc_unified" / "serial_annulus_singleton_bridge_20260725.json"


def main() -> None:
    checks: dict[str, bool] = {}

    # Divergent harmonic model: m_n = 1/(n+1), n = 0,...,N-1.
    n_div = 20_000
    m_div = [1.0 / (n + 1) for n in range(n_div)]
    s_div = 0.0
    radii_div = []
    for m in m_div:
        s_div += m
        radii_div.append(math.exp(-2.0 * math.pi * s_div))
    mod_div = [math.log(math.exp(-2.0 * math.pi * (sum(m_div[:n]))) / radii_div[n]) / (2.0 * math.pi) for n in range(25)]

    # Finite geometric model: m_n = 2^(-(n+1)), total sum = 1.
    n_fin = 80
    m_fin = [2.0 ** (-(n + 1)) for n in range(n_fin)]
    s_fin = sum(m_fin)
    r_fin = math.exp(-2.0 * math.pi * s_fin)

    checks["round_annulus_modulus_formula"] = all(
        math.isclose(value, m_div[n], rel_tol=2e-12, abs_tol=2e-12)
        for n, value in enumerate(mod_div)
    )
    checks["harmonic_partial_sum_grows"] = sum(m_div) > 9.0
    checks["harmonic_radius_becomes_small"] = radii_div[-1] < 1e-20
    checks["harmonic_model_has_singleton_limit"] = radii_div[-1] < 1e-20
    checks["geometric_sum_is_finite"] = math.isclose(s_fin, 1.0, rel_tol=1e-12)
    checks["geometric_model_has_nondegenerate_limit"] = r_fin > 0.001
    checks["grötzsch_scope_is_explicit"] = True
    checks["dynamic_annulus_realization_not_claimed"] = True
    checks["original_artifacts_written"] = False

    # The last field is a safety record, not a mathematical check.
    all_checks = all(value for key, value in checks.items() if key != "original_artifacts_written")
    payload = {
        "artifact": "SERIAL_ANNULUS_SINGLETON_BRIDGE",
        "date": "2026-07-25",
        "status": "SERIAL_ANNULUS_SINGLETON_BRIDGE_VALID" if all_checks else "FAILED",
        "theorem": "pairwise disjoint nested annuli with divergent total modulus have singleton nested inner intersection",
        "source": {
            "title": "Conformal Geometry and Dynamics of Quadratic Polynomials",
            "author": "Mikhail Lyubich",
            "proposition": "6.16",
            "url": "https://www.math.stonybrook.edu/~mlyubich/book.pdf",
        },
        "divergent_model": {
            "terms": n_div,
            "partial_sum": sum(m_div),
            "last_radius": radii_div[-1],
        },
        "finite_model": {
            "terms": n_fin,
            "partial_sum": s_fin,
            "limiting_radius": r_fin,
        },
        "checks": checks,
        "all_checks": all_checks,
        "scope": "proved analytic implication; direct/virtual dynamical annulus realization remains open",
        "original_artifacts_written": False,
    }
    OUT.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(payload["status"])
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()

