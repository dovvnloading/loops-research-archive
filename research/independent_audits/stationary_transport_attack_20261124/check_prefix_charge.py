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


def endpoint_census_checks():
    from itertools import combinations
    checked = 0
    # Exhaust all subsets of the finite owner/phase grid for k,b<=3.
    # Stage records use distinct pairs, so each owner contributes <= b.
    for k, b in product(range(1, 4), repeat=2):
        pairs = list(product(range(k), range(b)))
        for n in range(len(pairs) + 1):
            for records in combinations(pairs, n):
                counts = [sum(q == a for q, _ in records) for a in range(k)]
                assert max(counts) <= b
                assert n <= k*b
                if n > b:
                    assert sum(c > 0 for c in counts) >= 2
                checked += 1
    for b in range(1, 65):
        for h in range(65):
            e = max(0, (h + b)//b - 2)
            assert h + 1 <= (2+e)*b
            assert h + 1 - 2*b <= e*b
            if e:
                assert h + 1 > (2+e-1)*b
            assert sum(2*b*2**j for j in range(h)) + b*2**h == b*(3*2**h-2)
            if h >= 2*b:
                assert e >= 1
            checked += 1
    return checked


def latest_bank_checks():
    # Each final target needs only its latest qualifying predecessor.
    # Its suffix can contain the critical phase zero only at that time.
    cases = equalities = 0
    for P in range(2, 11):
        for mask in range(1, 1 << P, 2):
            critical = {k for k in range(P) if mask & (1 << k)}
            b = len(critical)
            for h in range(P):
                for s in range(h + 1):
                    total = 0
                    for k in range(P):
                        stages = [j for j in range(s, h + 1)
                                  if (k - h + j) % P in critical]
                        if not stages:
                            continue
                        j = max(stages)
                        phase = (k - h + j) % P
                        degree_two = any((phase + d) % P == 0
                                         for d in range(h-j))
                        if degree_two:
                            assert phase == 0
                        total += 2**j * (2 if degree_two else 1)
                    bound = b*2**h + (b+1)*(2**h-2**s)
                    assert total <= bound
                    cases += 1
                    equalities += total == bound
    assert cases == 47102
    assert equalities == 10170
    return cases, equalities


def canonical_direction_checks():
    checked = 0
    # Signed crossing telescopes even for arbitrarily interleaved
    # inward/outward crossings of each raw component.
    for n in range(11):
        for bits in product(range(2), repeat=n+1):
            for sign in (-1, 1):
                assert sum(sign*(bits[j]-bits[j+1]) for j in range(n)) == sign*(bits[0]-bits[-1])
                checked += 1
    # At most one anchor plus total +1 forces a unique positive one.
    for n in range(1, 9):
        for signs in product((-1, 1), repeat=n):
            for chosen in range(n):
                active = [j == chosen for j in range(n)]
                if sum(signs[j] for j in range(n) if active[j]) == 1:
                    assert signs[chosen] == 1
                    assert sum(active) == 1
                checked += 1
    # Actual cyclic order of positive bases. Use two distinct
    # representative positions per marked block so that both
    # endpoints can lie in the same physical limb.
    for q in range(3, 15):
        for start in range(2*q):
            for span in range(1, 2*q):
                end = (start+span) % (2*q)
                interior = {(start+j) % (2*q) for j in range(1, span)}
                for k in range(1, q-1):
                    if not {2*k, 2*k+1} <= interior:
                        continue
                    if start//2 == q-1:
                        assert {0, 1} <= interior
                    if 0 in (start//2, end//2) and not {2*q-2, 2*q-1} <= interior:
                        assert start//2 == 0 and end//2 != 0
                    checked += 1
    for b in range(1, 65):
        for h in range(65):
            e = max(0, (h+b)//b-1)
            assert h+1 <= (1+e)*b
            assert h+1-b <= e*b
            if e:
                assert h+1 > e*b
            if h >= b:
                assert e >= 1
            checked += 1
    assert checked == 30130
    return checked


def deck_collision_checks():
    checked = 0
    # Actual finite window multiplication and majority-gain threshold.
    for h in range(15):
        for bits in product(range(2), repeat=h):
            r = 1
            for bit in bits:
                r *= 1 + bit
            k = sum(bits)
            assert r == 2**k
            if 2*k > h:
                assert r*r >= 2*2**h
            checked += 1
    # Exact rational thresholds with a specified input fraction.
    for h in range(13):
        for k in range(h+1):
            for denom in range(1, 17):
                for numerator in range(1, denom+1):
                    eta = Q(numerator, denom)
                    r2 = 2**(2*k)
                    gain = Q(r2, 2**h)*eta
                    assert (gain >= 2) == (2*2**h <= eta*r2)
                    assert (gain > 1) == (2**h < eta*r2)
                    checked += 1
    # Symmetric polygonal branch model: exact coordinates and areas.
    for n in range(1, 65):
        delta = Q(1, 2**n)
        vertices = [(Q(1),Q(0)),(Q(2),Q(0)),(Q(2),Q(3)),
                    (delta,Q(3)),(delta,Q(2)),(Q(2),Q(-3)),
                    (delta,Q(-3)),(delta,Q(-2))]
        assert all(x > 0 and x*x+y*y < 16 for x,y in vertices)
        # Squaring identifies only opposite points; the positive
        # real part prevents distinct A-vertices from colliding.
        images = {(x*x-y*y,2*x*y) for x,y in vertices}
        assert len(images) == len(vertices)
        assert all(x*x+y*y < 256 for x,y in images)
        assert Q(1,2*delta) == 2**(n-1)
        assert 2*delta*Q(1,2*delta)**2 == Q(1,2*delta)
        checked += 1
    return checked


def coherent_packet_checks():
    checked = 0
    # Exact window/area factors: using r sheets costs r, not d.
    for h in range(15):
        for bits in product(range(2), repeat=h):
            factor = Q(1)
            for bit in bits:
                r = 1+bit
                factor *= Q(r, r*r)
            k = sum(bits)
            assert factor == Q(1, 2**k)
            assert factor*(2**k) == 1
            if k:
                assert factor <= Q(1, 2)
            checked += 1
    # Disjoint support partitions with arbitrary rational widths:
    # sum of the individual pattern gains controls the aggregate excess.
    for widths in product(range(5), repeat=4):
        for counts in product(range(4), repeat=4):
            total = sum(widths)
            coll = sum(w for w,k in zip(widths,counts) if k)
            output = sum(w*(2**k) for w,k in zip(widths,counts))
            assert output >= total+coll
            checked += 1
    # Sharp output threshold and the no-gain converse with bounded loss.
    for W in range(1, 33):
        for denom in range(1, 9):
            for num in range(1, denom+1):
                eta = Q(num, denom)
                E = eta*W/4
                G = W-E
                B = eta*W-E
                D = G+B
                assert D == (1+eta/2)*W
                assert B == (D/W-1)*W+E
                checked += 1
    return checked


def attachment_screening_checks():
    # Exact polygon/rectangle arithmetic for the harmonic barrier model.
    # The maximum-principle and conformal boundary-chart arguments
    # are written proofs, not tested by floating point sampling.
    checked = 0
    for n in range(1, 65):
        delta = Q(1, 2**n)
        vertices = [(Q(1),Q(0)),(Q(1),Q(1)),(delta,Q(1)),
                    (delta,Q(3)),(Q(1),Q(-1)),
                    (delta,Q(-1)),(delta,Q(-3))]
        assert all(x > 0 and x*x+y*y < 16 for x,y in vertices)
        images = {(x*x-y*y,2*x*y) for x,y in vertices}
        assert len(images) == len(vertices)
        assert all(x*x+y*y < 256 for x,y in images)
        area = 4*delta
        density = 1/(2*delta)
        assert (2*delta)*density == 1
        assert area*density*density == 1/delta == 2**n
        # The upper-bank test disks of radius 1/4 stay strictly
        # away from the fixed vertical sidewalls and the roof.
        assert Q(1,2)+Q(1,4) < 1
        assert Q(1,4) < 1
        checked += 1
    return checked


def auxiliary_response_checks():
    checked = 0
    # Exact finite contact labels: distinct endpoints force a transition.
    for length in range(2, 10):
        for labels in product(range(3), repeat=length):
            if labels[0] != labels[-1]:
                assert any(a != b for a,b in zip(labels, labels[1:]))
            checked += 1
    # Exact series optimum and its quadratic excess.
    for P,B in product(range(1, 33), repeat=2):
        w = Q(P*B, P+B)
        assert P >= w+w*w/B
        a,c = Q(B,P+B),Q(P,P+B)
        assert a+c == 1
        assert a*a*P+c*c*B == w
        checked += 1
    # Fractional response with a prescribed positive-width packet,
    # a bounded sum of auxiliary capacities and exact series equality.
    for W in range(1, 17):
        for denominator in range(2, 9):
            for numerator in range(1, denominator+1):
                eta = Q(numerator, denominator)
                w = eta*W
                for K in range(2, 9):
                    B = K*W
                    P = w*B/(B-w)
                    E = eta*eta*W/(2*K)
                    G = W-E
                    if G < w:
                        G = w
                    D = G-w+P
                    assert D >= W-E+eta*eta*W/K
                    assert D >= (1+eta*eta/(2*K))*W
                    checked += 1
    return checked


def main():
    cases, stays = partial_inverse_models()
    shifts = shift_checks()
    weights = weight_checks()
    print(f"PASS: {cases} finite orbit cases, {stays} all-critical stays")
    print(f"PASS: {shifts} strict-nest prefix cases, {weights} rational weight cases")
    print(f"PASS: {endpoint_census_checks()} exact endpoint census and birth-budget cases")
    cases, equalities = latest_bank_checks()
    print(f"PASS: {cases} latest-bank cases, including {equalities} exact budget equalities")
    print(f"PASS: {canonical_direction_checks()} crossing, cyclic-order and one-sided birth cases")
    print(f"PASS: {deck_collision_checks()} deck-window, threshold and symmetric-gap cases")
    print(f"PASS: {coherent_packet_checks()} coherent-packet and response-budget cases")
    print(f"PASS: {attachment_screening_checks()} exact attachment-screening polygon/neck cases")
    print(f"PASS: {auxiliary_response_checks()} auxiliary contact/series response cases")
    print("Scope: finite orbit, endpoint census, orientation and energy-weight algebra only.")


if __name__ == "__main__":
    main()
