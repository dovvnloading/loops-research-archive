#!/usr/bin/env python3
"""Exact finite regressions for the prefix-potential charge.

The tests check finite orbit implications and rational weights only.
No conformal calibration, physical carrier, or native encounter is
inferred from the finite models.
"""
from fractions import Fraction as Q
from itertools import product


def orbit(f, n, x):
    for _ in range(n):
        x = f[x]
    return x


def partial_inverse_models():
    states = tuple(range(4))
    cases = stays = 0
    for f in product(states, repeat=4):
        for mask in range(16):
            critical = {x for x in states if mask & (1 << x)}
            internal = {}
            for x in critical:
                y = f[x]
                if y in critical:
                    if y in internal:
                        break
                    internal[y] = x
            else:
                for default in states:
                    phi = tuple(internal.get(y, default) for y in states)
                    for b in range(6):
                        deep = {orbit(phi, b, y) for y in critical}
                        for x in states:
                            inside = all(orbit(f, j, x) in critical
                                         for j in range(b + 1))
                            if inside:
                                stays += 1
                                assert orbit(phi, b, orbit(f, b, x)) == x
                                assert x in deep
                            if x not in deep:
                                assert not inside
                            cases += 1
    return cases, stays


def shift_checks():
    # A genuinely strictly nested critical-set model lives on N,
    # not on a finite invariant set with a total inverse branch.
    # F(x)=max(x-1,0), phi(x)=x+1, C={1,2,...}.
    checked = 0
    for b in range(51):
        for n in range(b + 1, b + 16):
            for y in range(1, 11):
                for j in range(b + 1):
                    assert max(0, y + n - j) >= 2
                    checked += 1
        assert all(any(max(0, x - j) == 0 for j in range(b + 1))
                   for x in range(b + 1))
    return checked


def weight_checks():
    checked = 0
    for b in range(51):
        assert sum(2**j for j in range(b + 1)) == 2**(b + 1) - 1
        assert sum(Q(2**j, 4) for j in range(b + 1)) == Q(2**(b + 1) - 1, 4)
        if b:
            B = 2**(b + 1) - 2
            a, c = Q(B, B + 1), Q(1, B + 1)
            assert a + c == 1
            assert a*a + B*c*c == Q(B, B + 1) < 1
    for A, B in product(range(1, 13), repeat=2):
        for i, j in product(range(13), repeat=2):
            x, y = Q(i, 6), Q(j, 6)
            if x + y < 1:
                continue
            cost = A*x*x + B*y*y
            optimum = Q(A*B, A+B)
            assert cost >= optimum
            assert (A+B)*cost-A*B == (A*x-B*y)**2 + A*B*((x+y)**2-1)
            checked += 1
        a, c = Q(B,A+B), Q(A,A+B)
        assert a+c == 1 and A*a*a + B*c*c == Q(A*B,A+B)
    return checked


def main():
    cases, stays = partial_inverse_models()
    shifts = shift_checks()
    weights = weight_checks()
    print(f"PASS: {cases} finite orbit cases, {stays} all-critical stays")
    print(f"PASS: {shifts} strict-nest prefix cases, {weights} rational weight cases")
    print("Scope: finite orbit and energy-weight algebra only.")


if __name__ == "__main__":
    main()
