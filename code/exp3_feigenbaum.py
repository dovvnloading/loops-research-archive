"""Experiment 3: Renormalization at the Feigenbaum point, two independent ways.

(A) Period-doubling cascade in z^2+c: superstable parameters s_n (critical orbit
    period 2^n) via high-precision Newton; ratios -> delta; extrapolate c_F.
(B) Cvitanovic-Feigenbaum fixed-point equation g(x) = -alpha*g(g(x/alpha)),
    g even, g(0)=1, alpha=-1/g(1): solve by collocation + Newton, then take the
    Jacobian of the doubling operator in coefficient space and read off its
    spectrum (essential expanding eigenvalue = delta; the dilation coordinate
    mode alpha^2 is discarded as a conjugacy artifact, exactly as in Lanford's
    computer-assisted proof).

This is the concrete face of "a priori bounds": the renormalization operator has
a hyperbolic fixed point with definite geometry.
"""
import json
import numpy as np
from mpmath import mp, mpf, mpc

mp.dps = 60

OUT = r"..\results\exp3_feigenbaum.json"


def superstable(n, c0):
    """Newton-solve f_c^(2^n)(0) = 0 for c near c0."""
    N = 2 ** n
    c = mpf(c0)
    for _ in range(80):
        z = mpf(0)
        dz = mpf(0)
        for _ in range(N):
            dz = 2 * z * dz + 1
            z = z * z + c
        step = z / dz
        c = c - step
        if abs(step) < mpf(10) ** (-50):
            break
    return c


def cascade(n_max=14):
    s = [mpf(0), mpf(-1)]
    for n in range(2, n_max + 1):
        if n == 2:
            guess = mpf("-1.31")
        else:
            guess = s[-1] + (s[-1] - s[-2]) / mpf("4.669")
        s.append(superstable(n, guess))
    deltas = []
    for n in range(2, len(s)):
        deltas.append((s[n - 1] - s[n - 2]) / (s[n] - s[n - 1]))
    d = deltas[-1]
    c_F = s[-1] + (s[-1] - s[-2]) / (d - 1)
    return s, deltas, c_F


# ---------------- Cvitanovic-Feigenbaum fixed point ----------------

def g_eval(a, x):
    """g(x) = 1 + sum a_k x^{2k}, vectorized over x."""
    x2 = x * x
    acc = np.zeros_like(x)
    for k in range(len(a) - 1, -1, -1):
        acc = acc * x2 + a[k]
    return 1.0 + acc * x2


def residual(a, xs):
    g1 = g_eval(a, np.array([1.0]))[0]
    alpha = -1.0 / g1
    inner = g_eval(a, xs / alpha)
    lhs = g_eval(a, xs)
    rhs = -alpha * g_eval(a, inner)
    return lhs - rhs


def _newton_at_order(a, N, iters=80):
    j = np.arange(1, N + 1)
    xs = np.cos((2 * j - 1) * np.pi / (4 * N))  # Chebyshev nodes in (0,1)
    for _ in range(iters):
        r = residual(a, xs)
        rn = np.max(np.abs(r))
        if rn < 1e-13:
            break
        J = np.zeros((N, N))
        h = 1e-6
        for k in range(N):
            ap = a.copy(); ap[k] += h
            am = a.copy(); am[k] -= h
            J[:, k] = (residual(ap, xs) - residual(am, xs)) / (2 * h)
        step = np.linalg.solve(J, r)
        # damped update: backtrack until residual decreases
        lam = 1.0
        for _bt in range(30):
            trial = a - lam * step
            if np.max(np.abs(residual(trial, xs))) < rn:
                a = trial
                break
            lam *= 0.5
        else:
            break
    return a, np.max(np.abs(residual(a, xs)))


def solve_fixed_point(N=10):
    """Warm-start continuation in polynomial order: N=4 -> ... -> N."""
    a = np.array([-1.52, 0.10, 0.02, -0.003])
    a, res = _newton_at_order(a, 4)
    for Nk in range(6, N + 1, 2):
        a = np.concatenate([a, np.zeros(Nk - len(a))])
        a, res = _newton_at_order(a, Nk)
    g1 = g_eval(a, np.array([1.0]))[0]
    alpha = -1.0 / g1
    return a, alpha, res


def doubling_operator_coeffs(a, N, xs_fit):
    """Coefficients of T[g](x) = -alpha g(g(x/alpha)) refit as even poly."""
    g1 = g_eval(a, np.array([1.0]))[0]
    alpha = -1.0 / g1
    vals = -alpha * g_eval(a, g_eval(a, xs_fit / alpha))
    # fit 1 + sum b_k x^{2k}: least squares on (vals - 1) against x^{2k}
    A = np.vander(xs_fit * xs_fit, N + 1, increasing=True)[:, 1:]
    b, *_ = np.linalg.lstsq(A, vals - 1.0, rcond=None)
    return b


def delta_spectrum(a, N=14):
    M = 3 * N
    xs_fit = np.cos((2 * np.arange(1, M + 1) - 1) * np.pi / (4 * M))
    base = doubling_operator_coeffs(a, N, xs_fit)
    J = np.zeros((N, N))
    h = 1e-7
    for k in range(N):
        ap = a.copy()
        ap[k] += h
        J[:, k] = (doubling_operator_coeffs(ap, N, xs_fit) - base) / h
    ev = np.linalg.eigvals(J)
    ev = ev[np.argsort(-np.abs(ev))]
    return ev


if __name__ == "__main__":
    s, deltas, c_F = cascade(14)
    a, alpha, res = solve_fixed_point(10)
    ev = delta_spectrum(a, len(a))
    ev_real = [[float(e.real), float(e.imag)] for e in ev[:6]]
    # essential delta: eigenvalue closest to 4.669 among |ev|>1
    cand = [e for e in ev if abs(e) > 1.0]
    delta_ev = min(cand, key=lambda e: abs(e - 4.6692)) if cand else None
    out = {
        "superstable_params": [mp.nstr(x, 30) for x in s],
        "delta_ratios": [mp.nstr(d, 20) for d in deltas],
        "delta_from_cascade": mp.nstr(deltas[-1], 16),
        "c_Feigenbaum": mp.nstr(c_F, 25),
        "alpha_from_fixed_point": float(alpha),
        "fixed_point_residual": float(res),
        "fixed_point_coeffs": [float(x) for x in a],
        "jacobian_top_eigenvalues": ev_real,
        "delta_from_spectrum": [float(delta_ev.real), float(delta_ev.imag)] if delta_ev is not None else None,
        "alpha_squared": float(alpha * alpha),
        "reference_values": {
            "delta": "4.669201609102990671853...",
            "alpha": "2.502907875095892822283...",
            "c_F": "-1.401155189092050995...",
        },
    }
    with open(OUT, "w") as f:
        json.dump(out, f, indent=2)
    print(json.dumps(out, indent=2)[:2000])
