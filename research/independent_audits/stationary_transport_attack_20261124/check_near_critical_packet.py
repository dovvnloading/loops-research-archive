#!/usr/bin/env python3
"""Finite cyclic checks for NEAR_CRITICAL_PACKET_CONTROL.md.

This checks discrete marking/cut implications, not conformal geometry,
prime-end realization, modulus, or the native stationary theorem.
"""
from itertools import chain, product


def bank_checks():
    cases = 0
    # Include small q and a range of marking refinements, not just one
    # atom per limb. Same-atom long bases are represented by a full turn.
    for q in range(3, 10):
        for sizes in product((1, 2), repeat=q):
            limb = tuple(j for j, size in enumerate(sizes) for _ in range(size))
            m = len(limb)
            bank = {i for i, j in enumerate(limb) if j <= 2}
            critical = {i for i, j in enumerate(limb) if j == 0}
            for start in range(m):
                for steps in range(2, m + 1):
                    end = (start + steps) % m
                    inside = {(start + k) % m for k in range(1, steps)}
                    for anchor in inside & (bank - critical):
                        assert limb[anchor] in (1, 2)
                        if start not in bank and end not in bank:
                            assert critical <= inside
                        cases += 1
    return cases


def cut_checks():
    cases = 0
    same_atom = 0
    # Exact integer angular samples. The chart is the open half-circle
    # centered on a; y is its antipode. Unequal atom lengths permit y
    # either to be a mark or to lie inside a large endpoint atom.
    for m in range(3, 8):
        for lengths in chain(
            product((4, 8), repeat=m),
            (tuple(64 if i == j else 4 for i in range(m)) for j in range(m)),
        ):
            cuts = [0]
            for size in lengths:
                cuts.append(cuts[-1] + size)
            period = cuts[-1]
            mark_set = set(cuts[:-1])
            def atom(t):
                t %= period
                return next(i for i in range(m) if cuts[i] < t < cuts[i+1])
            for k in range(m):
                a = (cuts[k] + cuts[k+1]) // 2
                y = (a + period // 2) % period
                H = None if y in mark_set else atom(y)
                for x in range(a - period // 4 + 1, cuts[k]):
                    if x % period in mark_set:
                        continue
                    for z in range(cuts[k+1]+1, a + period // 4):
                        if z % period in mark_set:
                            continue
                        i, j = atom(x), atom(z)
                        cap = {t % period for t in range(x, z+1)}
                        assert y not in cap
                        if i == j:
                            # The directed cap crosses a separate whole
                            # anchor atom, so it is the long same-atom class.
                            assert H == i
                            same_atom += 1
                        if H is not None and H not in (i, j):
                            assert not any(t in cap for t in range(cuts[H], cuts[H+1]+1))
                        cases += 1
    assert same_atom > 0
    return cases, same_atom


def end_atom_checks():
    cases = 0
    # A coarse block is a connected run of fine atoms; E is its first
    # fine atom. Check all oriented bases containing E strictly between
    # their endpoint atoms (including long same-atom classes).
    for m in range(3, 13):
        for k in range(1, m):
            coarse = set(range(k))
            E = 0
            for start in range(m):
                for steps in range(2, m + 1):
                    end = (start + steps) % m
                    inside = {(start + t) % m for t in range(1, steps)}
                    if E not in inside or E in (start, end):
                        continue
                    traversed = inside | {start, end}
                    assert len(traversed) >= 3
                    assert not traversed <= coarse
                    cases += 1
    return cases


if __name__ == '__main__':
    n = bank_checks()
    c, same = cut_checks()
    e = end_atom_checks()
    print(f'near-critical bank: {n:,} cases')
    print(f'fixed chart/cut: {c:,} cases ({same:,} long same-atom)')
    print(f'protected end atom: {e:,} cases')
    print(f'total: {n+c+e:,} finite checks passed')
