#!/usr/bin/env python3
"""Discrete regressions for signed endpoint shift and shared-crest ambient response.

No conformal/prime-end/native-geometric premise is verified by this file.
"""
from fractions import Fraction
from itertools import product


def end_probe_checks():
    count = 0
    # 1 or 2 coarse atoms per limb. Three fine atoms per coarse atom:
    # protected first/last and an arbitrary middle. This grid does not
    # model omitted-cut fibers; the written theorem treats those separately.
    # Exhaust candidate positively oriented cap arcs, including long ones.
    for q in range(2, 9):
        for sizes in product((1, 2), repeat=q):
            limb = tuple(k for k, size in enumerate(sizes) for _ in range(size))
            n = len(limb)
            m = 3*n
            for left in range(n):
                for right in range(left+2, n):
                    if limb[left] == 0 or limb[right] == 0:
                        continue
                    # Each interior crest probe is inside. Neither outside
                    # probe is inside or an endpoint. Probe endpoints inside
                    # the two ending coarse atoms are not constrained.
                    inside_mask = outside_mask = 0
                    for a in range(n):
                        if a in (left, right):
                            continue
                        probes = (1 << (3*a)) | (1 << (3*a+2))
                        if left < a < right:
                            inside_mask |= probes
                        else:
                            outside_mask |= probes
                    for start in range(m):
                        for length in range(3, m):
                            end = (start+length-1) % m
                            bits = ((1 << (length-2))-1) << ((start+1) % m)
                            bits = (bits & ((1 << m)-1)) | (bits >> m)
                            ends = (1 << start) | (1 << end)
                            if bits & inside_mask != inside_mask:
                                continue
                            if bits & outside_mask or ends & (inside_mask | outside_mask):
                                continue
                            assert start//3 == left and end//3 == right
                            count += 1
    return count


def shift_checks():
    count = 0
    # Integer real-coordinate model, BL0 represented after BL(q-1).
    for q in range(4, 21):
        for k in range(1, q):
            for lo in range(1, q):
                for hi in range(lo, q):
                    positive = lo >= k+2
                    negative = hi <= k-2
                    if not (positive or negative):
                        continue
                    for b in range(3*lo, 3*lo+3):
                        for t in range(b, 3*hi+3):
                            for B in range(t, 3*hi+3):
                                a = 3*k+1
                                d = 3*(B//3+1)
                                if positive:
                                    c = 3*(k+1)+1
                                    assert a < c < b <= t < d
                                else:
                                    c = 3*(k+1)
                                    assert b <= t < d < a < c
                                count += 1
    return count


def ambient_scale_checks():
    count = 0
    for b in range(1, 25):
        h = b+2
        N = h+12*b*2**h
        for s in range(1, 17):
            sigma = Fraction(s, 16)
            delta = sigma*sigma/(2048*N)
            assert (h+2)*delta <= sigma/8
            # Square the claimed square-root bound; all sides are nonnegative.
            assert 32*N*delta == (sigma/8)**2
            assert sigma/4+sigma/8+sigma/8 < sigma
            count += 1
    return count


if __name__ == "__main__":
    counts = [end_probe_checks(), shift_checks(), ambient_scale_checks()]
    for name, count in zip(("signed end-probe trap", "median shift order",
                            "ambient response scale"), counts):
        print(f"{name}: {count:,} exact cases")
    print(f"PASS: {sum(counts):,} discrete cases; geometry is not tested.")
