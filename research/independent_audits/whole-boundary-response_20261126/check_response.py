"""Exact arithmetic regressions for the written whole-boundary response lemma.

These tests are not a certificate of the harmonic-flow or physical realization proof.
No numerical optimization, random sampling, or third-party dependencies.
"""
from fractions import Fraction as F
from itertools import combinations, product
import json


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def energy(edges, x):
    return sum((F(w) * (x[i] - x[j]) ** 2 for i, j, w in edges), F(0))


def cut_bound(edges, n):
    return max(energy(edges, x) for x in product((0, 1), repeat=n))


def reduce_one(edges, n, k):
    """Eliminate one floating constant electrode (not an arbitrary trace)."""
    c = [[F(0) for _ in range(n)] for _ in range(n)]
    for i, j, w in edges:
        c[i][j] += F(w)
        c[j][i] += F(w)
    degree = sum(c[k])
    remaining = [i for i in range(n) if i != k]
    return [(a, b, c[i][j] + (c[i][k] * c[j][k] / degree if degree else 0))
            for (a, i), (b, j) in combinations(enumerate(remaining), 2)]


def main():
    # D = vv^T with v=(1,1,-1,-1), written as signed edge weights.
    # L and L+D are ordinary graph Laplacians. D is PSD, not a Laplacian
    # with nonnegative conductances; singleton cuts do not suffice.
    v = (1, 1, -1, -1)
    base = [(i, j, F(1)) for i, j in combinations(range(4), 2)]
    residual = [(i, j, F(-v[i] * v[j])) for i, j in combinations(range(4), 2)]
    augmented = [(i, j, w + d) for (i, j, w), (_, _, d) in zip(base, residual)]
    require(all(w >= 0 for _, _, w in augmented), 'augmented graph sign')
    C = cut_bound(residual, 4)
    require(C == 4, 'all cuts')
    require(all(energy(residual, tuple(int(i == j) for i in range(4))) == 1
                for j in range(4)), 'singleton cut control is weaker')
    count = 0
    for x in product(range(-2, 3), repeat=4):
        osc = max(x) - min(x)
        d = energy(augmented, x) - energy(base, x)
        require(d == sum(a * b for a, b in zip(v, x)) ** 2, 'residual square')
        require(0 <= d <= C * osc ** 2, 'cut-to-oscillation estimate')
        count += 1
    require(energy(residual, (0, 0, 1, 1)) == C, 'attainment on finite test')
    # All binary cuts nonnegative does not imply PSD.
    bad = [(0, 1, -1), (0, 2, 1), (1, 2, 1)]
    require(all(energy(bad, x) >= 0 for x in product((0, 1), repeat=3)), 'negative control cuts')
    require(energy(bad, (1, -1, 0)) == -2, 'negative control detects indefinite form')
    low = reduce_one(base, 4, 3)
    high = reduce_one(augmented, 4, 3)
    eliminated = 0
    for x in product(range(-2, 3), repeat=3):
        d = energy(high, x) - energy(low, x)
        require(0 <= d <= C * (max(x) - min(x)) ** 2, 'constant electrode elimination')
        eliminated += 1
    # Physical tail comparison R/2 > 2^(p-4) follows from 3/40 > 1/16.
    require(F(3, 40) > F(1, 16), 'physical radius ratio')
    require(F(3, 4) == sum((F(i) - F(1, 4)) ** 2 for i in (1, 0, 0, 0)), 'Rayleigh normalization')
    print(json.dumps({'cut_bound': str(C), 'integer_vectors': count,
                      'elimination_vectors': eliminated, 'negative_control': '-2',
                      'physical_radius_ratio': '3/40 > 1/16',
                      'status': 'arithmetic-only'}, sort_keys=True))


if __name__ == '__main__':
    main()
