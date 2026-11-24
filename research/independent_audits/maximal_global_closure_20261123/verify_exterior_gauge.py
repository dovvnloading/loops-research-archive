#!/usr/bin/env python3
"""Exact algebra for EXTERIOR_GAUGE_REPAIR.md (requires SymPy).

This checks formulas only; it does not prove QC compactness or analytic
no-line-field hypotheses for any infinitely renormalizable polynomial.
"""

import json
import sympy as sp


def main():
    w, v = sp.symbols("w v", nonzero=True)
    # v is a formal independent variable representing conjugate(w).
    radial = w * w * v

    def J(x):
        return x + 1 / x

    def zero(expr):
        assert sp.cancel(expr) == 0, expr

    zero(radial.subs({w: 1 / w, v: 1 / v}, simultaneous=True) - 1 / radial)
    zero(radial.subs({w: w**2, v: v**2}, simultaneous=True) - radial**2)
    zero(J(w)**2 - 2 - J(w**2))
    zero(radial.subs(v, 1 / w) - w)
    derivative_w = sp.diff(radial, w)
    derivative_v = sp.diff(radial, v)
    mu = sp.cancel(derivative_v / derivative_w)
    zero(mu - w / (2 * v))
    pulled_mu = mu.subs({w: w**2, v: v**2}, simultaneous=True) * v / w
    zero(pulled_mu - mu)
    zero(J(radial)**2 - 2 - J(radial**2))
    source = J(sp.Integer(2))
    target = J(radial.subs({w: 2, v: 2}, simultaneous=True))
    assert source == sp.Rational(5, 2)
    assert target == sp.Rational(65, 8)
    assert source != target
    print(json.dumps({
        "status": "PASS",
        "sympy_version": sp.__version__,
        "stretch_exponent": 3,
        "beltrami_modulus": "1/2",
        "qc_dilatation": 3,
        "source_point": str(source),
        "image_point": str(target),
        "verified": [
            "descent under w -> 1/w",
            "radial stretch commutes with squaring",
            "Joukowski semiconjugacy",
            "pointwise fixed unit circle",
            "Wirtinger derivative and invariant Beltrami coefficient",
            "induced Chebyshev conjugacy",
            "explicit nonidentity value",
        ],
        "scope": "exact algebra only; analytic support theorem is written",
    }, indent=2))


if __name__ == "__main__":
    main()
