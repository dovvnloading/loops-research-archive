#!/usr/bin/env python3
"""Rejected exploratory evidence, not a Lean theorem or an MLC contribution.

Enumerate reductions in characteristic two of the spectral polynomial from
Buff--Epstein--Koch, Eigenvalues of the Thurston operator, Proposition 9.7.
No assertion here concerns repeated complex eigenvalues or parameter fibers.

For x_0=0, x_{j+1}=x_j^2+c, and an exact critical period m, form

    R(c,v) = sum_{k=0}^{m-1} v^k product_{j=1}^k x_{m-j}.

The universal factor is 1+v in characteristic two. Test whether
Q=R/(1+v) is relatively prime to its formal derivative. We enumerate all
c in F_(2^m), avoiding repeated work on Frobenius-conjugate parameters.
All roots of x_m(c) lie in this field: x_m(c)^2+x_m(c)=c^(2^m)+c.

Scope: m=3,...,16 only. Integer bit arithmetic implements the finite fields;
the defining binary polynomials are checked for irreducibility. The program
uses no approximate numerics, optional packages, network access, or Lean.
Its completed output is stored beside it as EXPLORED_REDUCED_SPECTRUM.txt.
"""

from __future__ import annotations


MODULI = {
    3: 0xD,
    4: 0x19,
    5: 0x29,
    6: 0x73,
    7: 0xD5,
    8: 0x11B,
    9: 0x217,
    10: 0x7F3,
    11: 0xE81,
    12: 0x1E61,
    13: 0x36E3,
    14: 0x582D,
    15: 0xA7BB,
    16: 0x10225,
}


def prime_divisors(n: int) -> list[int]:
    result = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            result.append(p)
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        result.append(n)
    return result


def binary_remainder(a: int, b: int) -> int:
    assert b
    while a and a.bit_length() >= b.bit_length():
        a ^= b << (a.bit_length() - b.bit_length())
    return a


def binary_gcd(a: int, b: int) -> int:
    while b:
        a, b = b, binary_remainder(a, b)
    return a


class BinaryField:
    def __init__(self, m: int, modulus: int):
        self.m, self.modulus, self.size = m, modulus, 1 << m
        assert modulus.bit_length() == m + 1

        # Rabin's irreducibility criterion, specialized to F_2.
        powers = [2]
        for _ in range(m):
            powers.append(self.raw_mul(powers[-1], powers[-1]))
        assert powers[m] == 2
        for p in prime_divisors(m):
            assert binary_gcd(powers[m // p] ^ 2, modulus) == 1

        primes = prime_divisors(self.size - 1)
        generator = 2
        while any(self.power(generator, (self.size - 1) // p) == 1 for p in primes):
            generator += 1
        assert generator < self.size

        self.exp = [1] * (2 * self.size)
        self.log = [0] * self.size
        value = 1
        seen = set()
        for i in range(self.size - 1):
            assert value not in seen
            seen.add(value)
            self.exp[i], self.log[value] = value, i
            value = self.raw_mul(value, generator)
        assert value == 1 and len(seen) == self.size - 1
        for i in range(self.size - 1, len(self.exp)):
            self.exp[i] = self.exp[i - (self.size - 1)]
        self.square = [self.mul(a, a) for a in range(self.size)]

    def raw_mul(self, a: int, b: int) -> int:
        result = 0
        while b:
            if b & 1:
                result ^= a
            b >>= 1
            a <<= 1
            if a >> self.m:
                a ^= self.modulus
        return result

    def power(self, a: int, n: int) -> int:
        result = 1
        while n:
            if n & 1:
                result = self.raw_mul(result, a)
            a = self.raw_mul(a, a)
            n >>= 1
        return result

    def mul(self, a: int, b: int) -> int:
        return self.exp[self.log[a] + self.log[b]] if a and b else 0

    def inv(self, a: int) -> int:
        assert a
        return self.exp[self.size - 1 - self.log[a]]

    @staticmethod
    def trim(p: list[int]) -> list[int]:
        while p and p[-1] == 0:
            p.pop()
        return p

    def remainder(self, p: list[int], q: list[int]) -> list[int]:
        p = p[:]
        inverse = self.inv(q[-1])
        while len(p) >= len(q):
            k, a = len(p) - len(q), self.mul(p[-1], inverse)
            for j, b in enumerate(q):
                p[j + k] ^= self.mul(a, b)
            self.trim(p)
        return p

    def gcd(self, p: list[int], q: list[int]) -> list[int]:
        while q:
            p, q = q, self.remainder(p, q)
        inverse = self.inv(p[-1])
        return [self.mul(a, inverse) for a in p]

    def evaluate(self, p: list[int], at: int) -> int:
        result = 0
        for coefficient in reversed(p):
            result = self.mul(result, at) ^ coefficient
        return result

    def spectral_polynomials(self, c: int) -> tuple[list[int], list[int], list[int]]:
        orbit = [0]
        for _ in range(self.m):
            orbit.append(self.square[orbit[-1]] ^ c)
        assert orbit[-1] == 0 and 0 not in orbit[1:-1]
        r, product = [1], 1
        for k in range(1, self.m):
            product = self.mul(product, orbit[self.m - k])
            r.append(product)
        q = [1]
        for a in r[1:-1]:
            q.append(a ^ q[-1])
        assert q[-1] == r[-1]  # Exact division by 1+v.
        derivative = self.trim([a if i & 1 else 0 for i, a in enumerate(q)][1:])
        return q, derivative, self.gcd(q, derivative)


def explore(m: int, modulus: int) -> tuple[int, int]:
    field = BinaryField(m, modulus)
    seen = bytearray(field.size)
    exact_count = collision_count = 0
    for c in range(field.size):
        if seen[c]:
            continue
        conjugates, d = [], c
        while not seen[d]:
            conjugates.append(d)
            seen[d] = 1
            d = field.square[d]
        orbit, x = [], 0
        for _ in range(m):
            x = field.square[x] ^ c
            orbit.append(x)
        if orbit[-1] != 0 or 0 in orbit[:-1]:
            continue
        exact_count += len(conjugates)
        _, _, common = field.spectral_polynomials(c)
        if len(common) > 1:
            collision_count += len(conjugates)
    return exact_count, collision_count


def period_nine_example() -> None:
    # c denotes the residue of X modulo X^9+X^4+X^2+X+1.
    field = BinaryField(9, 0x217)
    q, derivative, common = field.spectral_polynomials(2)
    assert common == [35, 0, 1]  # v^2 + (1+c+c^5).
    root = 348  # c^2+c^3+c^4+c^6+c^8.
    assert field.evaluate(q, root) == field.evaluate(derivative, root) == 0
    assert field.square[root] == 35
    print("period-9 example: h(c)=c^9+c^4+c^2+c+1")
    print("Q coefficients (low degree first, binary c-polynomial encoding):", q)
    print("gcd(Q,Q') = v^2 + 1+c+c^5")
    print("repeated root: v=c^2+c^3+c^4+c^6+c^8")


if __name__ == "__main__":
    print("REJECTED EXPLORATORY EVIDENCE; no complex-family theorem or Lean proof")
    print("period modulus exact_period_parameters nonsquarefree_Q_parameters")
    for period, polynomial in MODULI.items():
        total, bad = explore(period, polynomial)
        print(period, hex(polynomial), total, bad)
    period_nine_example()
