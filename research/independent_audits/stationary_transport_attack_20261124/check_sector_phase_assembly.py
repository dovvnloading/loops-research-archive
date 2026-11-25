#!/usr/bin/env python3
"""Exact discrete checks for finite phase assembly, not geometric verification."""
from itertools import product, combinations
from fractions import Fraction as Q


def interlace(a, b, c, d):
    return a < c < b < d or c < a < d < b


def shared_cell_order():
    cases = shared = alternating = 0
    for n in range(2, 13):
        pairs = [(i, j if j > i else j+n)
                 for i in range(n) for j in range(n) if i != j]
        for (a,b),(c0,d0) in combinations(pairs, 2):
            for shift in range(-2, 3):
                c, d = c0+shift*n, d0+shift*n
                if a == c:
                    assert b != d
                    kind = 'start'
                elif b == d:
                    kind = 'end'
                elif b == c:
                    kind = 'end-start'
                elif a == d:
                    kind = 'start-end'
                else:
                    kind = 'distinct'
                for u,v,x,y in product((1,2), repeat=4):
                    A,B,C,D = 3*a+u,3*b+v,3*c+x,3*d+y
                    if A in (C,D) or B in (C,D):
                        continue
                    cross = interlace(A,B,C,D)
                    if kind == 'start':
                        bad = A < C if b < d else C < A
                    elif kind == 'end':
                        bad = B < D if a < c else D < B
                    elif kind == 'end-start':
                        bad = B > C
                    elif kind == 'start-end':
                        bad = D > A
                    else:
                        bad = interlace(a,b,c,d)
                    assert cross == bad
                    cases += 1
                    shared += kind != 'distinct'
                    alternating += cross
    return cases, shared, alternating


def disk_geometry():
    count = 0
    # Doubled centers and radii keep all comparisons integral.
    for a in range(9):
        for b in range(a+1,11):
            for c in range(9):
                for d in range(c+1,11):
                    if b <= c or d <= a:
                        assert abs(a+b-c-d) >= b-a+d-c
                        count += 1
                    if a <= c and d <= b:
                        assert abs(a+b-c-d)+d-c <= b-a
                        count += 1
    return count


def sector_phase():
    count = 0
    # Target circumference 2n, source circumference 2dn in lifted
    # units; covering is reduction mod 2n. Cells have two grid units.
    for n in range(2,9):
        for deg in range(1,9):
            period = 2*n
            for a in range(n):
                for b in range(n):
                    if b == a:
                        continue
                    B = b if b > a else b+n
                    l,u = 2*a, 2*(B+1)
                    assert 0 < u-l <= period
                    # Full phase intervals, excluding their endpoints.
                    phases = [
                        {(x % (deg*period)) for x in range(l+s*period+1,u+s*period)}
                        for s in range(deg)]
                    for i, I in enumerate(phases):
                        assert len({x % period for x in I}) == len(I)
                        assert all(I.isdisjoint(J) for J in phases[i+1:])
                        count += 1
                    # An actual fixed anchor belongs to at most one
                    # open inverse interval of the given directed pair.
                    for anchor in range(deg*period):
                        assert sum(anchor in I for I in phases) <= 1
                        count += 1
    return count


def phase_deficit():
    count = 0
    # Nonnegative source phase widths, one privileged compatible
    # sector phase per directed pair. Largest-phase selection loses
    # no more than the mass outside that privileged phase.
    for m in range(1,6):
        for widths in product(range(5), repeat=m):
            total = sum(widths)
            defect = total-max(widths)
            for privileged in range(m):
                assert defect <= total-widths[privileged]
                count += 1
            if m > 1 and defect:
                assert max(widths) >= Q(defect,m-1)
                count += 1
    return count


def scale():
    count = 0
    for b in range(1,17):
        h=b+2
        H=h+2
        N=h+12*b*2**h
        for n in range(1,17):
            sigma=Q(n,16)
            delta=sigma*sigma/(2048*N)
            assert (h+2)*delta <= sigma/8
            assert 32*N*delta == (sigma/8)**2
            assert sigma/4+sigma/8+sigma/8 < sigma
            # With E_base+B_fixed<=delta/4 at W=1,
            # both thresholds in the phase-deficit alternative
            # are at least delta/4.
            for t in range(5):
                E=delta*Q(t,16)
                B=delta/4-E
                assert delta/2-E >= delta/4
                assert sigma/4-E-B >= delta/4
                assert H > 0
                count += 1
    return count


if __name__ == '__main__':
    order, shared, altern = shared_cell_order()
    disks = disk_geometry()
    phase = sector_phase()
    deficit = phase_deficit()
    scales = scale()
    print(f'shared-cell/lift order: {order:,} cases ({shared:,} shared, {altern:,} alternating)')
    print(f'diameter disk geometry: {disks:,} cases')
    print(f'covering sector/phase: {phase:,} cases')
    print(f'phase-selection deficit: {deficit:,} cases')
    print(f'ambient deficit scale: {scales:,} cases')
    print(f'PASS: {order+disks+phase+deficit+scales:,} exact discrete checks; geometry not certified.')
