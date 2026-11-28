#!/usr/bin/env python3
"""Exact exhaustive check of the rigid-atom criterion in NOTE.md.

Model (NOTE.md, section "Evidence", step 1).  A marked contour substitution
system of degree d on M >= 2 atoms is

    a[i] >= 1   number of target atoms covered by source atom i,
    c[i] >= 0   number of target atoms inserted at the marked point p_i that
                precedes atom i,
    t0          first target atom of the image of atom 0,

with sum(a) + sum(c) = d*M.  A proper state is (s, k): the open interval made
of atoms s, ..., s+k-1 (1 <= k <= M; k = M is the circle punctured at p_s).
Phi(s, k) = (tau(s), Lam) if Lam <= M and the whole circle FULL otherwise,
where Lam = sum of a over the atoms plus sum of c over the k-1 interior
marked points.  Phi(FULL) = FULL.

Everything is integer arithmetic over ALL systems of the listed sizes.  The
script re-derives every statement by direct simulation of Phi; it does not
use the theorems to produce the data it compares them with.  It certifies the
finite instances only.  The all-size statements are the written proofs in
NOTE.md.  No system here is claimed to be a Hubbard tree, a polynomial, or a
KKL wave.

Run from the repository root:

    python contributions/rigid_atom_criterion_20261126/check_rigid_atom_criterion.py
"""
from __future__ import annotations

import itertools
import sys
import time

FULL = -1


def compositions(total: int, parts: int):
    """All tuples of `parts` nonnegative integers with the given sum."""
    if parts == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in compositions(total - first, parts - 1):
            yield (first,) + rest


def systems(M: int, d: int):
    for extra in compositions((d - 1) * M, 2 * M):
        a = tuple(1 + x for x in extra[:M])
        c = extra[M:]
        for t0 in range(M):
            yield a, c, t0


class System:
    def __init__(self, M: int, a, c, t0: int):
        self.M, self.a, self.c = M, a, c
        tau = [t0]
        for i in range(M - 1):
            tau.append((tau[i] + a[i] + c[i + 1]) % M)
        # the lift closes up after d full turns
        assert (tau[M - 1] + a[M - 1] + c[0]) % M == t0
        self.tau = tau
        # phi on proper states, encoded s*M + (k-1); FULL is -1
        self.lam = [0] * (M * M)
        self.phi = [FULL] * (M * M)
        for s in range(M):
            lam = 0
            for k in range(1, M + 1):
                j = (s + k - 1) % M
                lam += a[j] + (c[j] if k > 1 else 0)
                self.lam[s * M + k - 1] = lam
                if lam <= M:
                    self.phi[s * M + k - 1] = tau[s] * M + (lam - 1)

    def rigid_interval(self, s: int, k: int) -> bool:
        return self.lam[s * self.M + k - 1] == k

    def rigid_cycle_atoms(self) -> dict[int, int]:
        """atom -> period, for atoms on a cycle of the partial map sigma."""
        M, a, tau = self.M, self.a, self.tau
        out = {}
        for s in range(M):
            x, n = s, 0
            while a[x] == 1 and n < M:
                x, n = tau[x], n + 1
                if x == s:
                    out[s] = n
                    break
        return out

    def longest_rigid_chain(self) -> int:
        """h: the largest number of rigid atoms i, sigma(i), sigma^2(i), ...
        Only called when there is no rigid cycle."""
        M, a, tau = self.M, self.a, self.tau
        best = 0
        for s in range(M):
            x, n = s, 0
            while a[x] == 1:
                x, n = tau[x], n + 1
                assert n <= M
            best = max(best, n)
        return best

    def periodic_states(self) -> set[int]:
        """Proper states lying on a cycle of Phi, by direct iteration."""
        M, phi = self.M, self.phi
        status = [0] * (M * M)  # 0 new, 1 on current path, 2 done
        periodic = set()
        for start in range(M * M):
            if status[start]:
                continue
            path = []
            x = start
            while x != FULL and status[x] == 0:
                status[x] = 1
                path.append(x)
                x = phi[x]
            if x != FULL and status[x] == 1:
                periodic.update(path[path.index(x):])
            for y in path:
                status[y] = 2
        return periodic


def contained(M: int, x: int, y: int) -> bool:
    """Open-arc inclusion of states (FULL contains everything)."""
    if y == FULL:
        return True
    if x == FULL:
        return False
    s, k = divmod(x, M)
    t, l = divmod(y, M)
    return (s - t) % M + (k + 1) <= l + 1


def meets(M: int, x: int, r: int) -> bool:
    """Does the state meet the run L of atoms 0..r-1?"""
    s, k = divmod(x, M)
    k += 1
    return s < r or s + k > M


def check_system(sy: System, counters: dict, chain_check: bool) -> None:
    M, phi = sy.M, sy.phi
    cyc = sy.rigid_cycle_atoms()
    periodic = sy.periodic_states()

    # Lemma 1: length never drops while the image is proper; Phi is monotone.
    for x in range(M * M):
        if phi[x] != FULL:
            assert phi[x] % M >= x % M
    if M <= 5:
        for x in range(M * M):
            for y in range(M * M):
                if contained(M, x, y):
                    assert contained(M, phi[x], phi[y])
        counters["monotone"] += 1

    # Theorem 1: a proper periodic interval exists iff a rigid cycle exists,
    # and the periodic proper intervals are exactly the predicted ones.
    assert bool(periodic) == bool(cyc)
    predicted = set()
    for s, q in cyc.items():
        for k in range(1, M + 1):
            x, good = s, True
            for _ in range(q):
                if not sy.rigid_interval(x, k):
                    good = False
                    break
                x = sy.tau[x]
            if good:
                predicted.add(s * M + k - 1)
    assert predicted == periodic
    counters["systems"] += 1
    if cyc:
        counters["with_rigid_cycle"] += 1
        return

    # From here on: no rigid cycle.
    counters["without_rigid_cycle"] += 1
    h = sy.longest_rigid_chain()

    # Theorem 2: plateaus.  plateau[x] = states Phi^0 x, ..., Phi^n x with n
    # maximal such that Phi^n x is proper of the same length as x.
    longest = 0
    plateaus = []
    for x in range(M * M):
        k = x % M
        orbit = [x]
        y = phi[x]
        while y != FULL and y % M == k:
            orbit.append(y)
            y = phi[y]
            assert len(orbit) <= M * M
        assert len(set(orbit)) == len(orbit)              # no repeated state
        for z in orbit[:-1]:
            assert sy.rigid_interval(z // M, k + 1)       # all but the last are rigid
        longest = max(longest, len(orbit) - 1)
        plateaus.append(orbit)
    assert longest == h                                    # Corollary 3(a), sharp
    counters["max_h"] = max(counters["max_h"], h)

    # Corollary 3(b): critical encounters on one plateau.
    bound = {}
    for r in range(1, M):
        z = sum(1 for i in range(r) if sy.a[i] > 1)
        for k in range(1, M + 1):
            g = sum(1 for s in range(M)
                    if sy.rigid_interval(s, k) and meets(M, s * M + k - 1, r))
            if z >= 1:
                assert g <= r - z                           # Lemma 4
            bound[r, k] = min(M, r + k - 1, g + 1)
        for orbit in plateaus:
            k = orbit[0] % M + 1
            hits = sum(1 for y in orbit if meets(M, y, r))
            assert hits <= bound[r, k]
            if hits == bound[r, k]:
                counters["plateau_bound_attained"] += 1
        counters["plateau_checks"] += len(plateaus)

    # Corollary 5: variable-time enlargement chains.
    if not chain_check:
        return
    reach = []
    for x in range(M * M):
        seen = []
        y = phi[x]
        while y != FULL and y not in seen:
            seen.append(y)
            y = phi[y]
        reach.append(seen)
    for r in range(1, M):
        nodes = [x for x in range(M * M) if meets(M, x, r)]
        edges = {x: [y for y in nodes if any(contained(M, w, y) for w in reach[x])]
                 for x in nodes}
        for K in range(1, M + 1):
            keep = [x for x in nodes if x % M + 1 <= K]
            memo: dict[int, int] = {}
            active: set[int] = set()

            def longest_from(x: int) -> int:
                if x in memo:
                    return memo[x]
                assert x not in active                      # the chain graph is acyclic
                active.add(x)
                best = 1 + max((longest_from(y) for y in edges[x] if y % M + 1 <= K),
                               default=0)
                active.discard(x)
                memo[x] = best
                return best

            t = max((longest_from(x) for x in keep), default=0)
            assert t <= sum(bound[r, k] for k in range(1, K + 1))
            counters["chain_checks"] += 1


def check_count_lemma(max_m: int) -> int:
    """Lemma 4 for every set of rigid atoms: if the run L = atoms 0..r-1
    contains z >= 1 non-rigid atoms, at most r - z length-k intervals made of
    rigid atoms meet L."""
    cases = 0
    for M in range(2, max_m + 1):
        for mask in range(1 << M):
            rigid = [(mask >> i) & 1 for i in range(M)]
            for r in range(1, M):
                z = r - sum(rigid[:r])
                if z == 0:
                    continue
                for k in range(1, M + 1):
                    g = 0
                    for s in range(M):
                        if (s < r or s + k > M) and all(rigid[(s + j) % M] for j in range(k)):
                            g += 1
                    assert g <= r - z
                    cases += 1
    return cases


def check_named_examples() -> None:
    # The negative control of research/independent_audits/interval_growth_repair_20261106.md
    # section 6: words 0 -> (0), 1 -> (1,2), 2 -> (0,1,2).  Atom 0 is a rigid fixed atom.
    sy = System(3, (1, 2, 3), (0, 0, 0), 0)
    assert sy.rigid_cycle_atoms() == {0: 1}
    assert sy.periodic_states() == {0}
    # NOTE.md example 6: two edges x, y; contour atoms (x+, x-, y+, y-); x is mapped onto
    # itself and y onto the path y, y, x.  Incidence matrix [[1,0],[1,2]] has spectral
    # radius 2 > 1 and is reducible; both sides of x are rigid fixed atoms.
    sy = System(4, (1, 1, 3, 3), (0, 0, 0, 0), 0)
    assert sy.tau == [0, 1, 2, 1]
    assert sy.rigid_cycle_atoms() == {0: 1, 1: 1}
    assert sy.periodic_states() == {0 * 4 + 0, 1 * 4 + 0, 0 * 4 + 1}   # x+, x-, and (x+ x-)
    # A system with an insertion at a marked point: the closed-up interval grows although
    # both atoms are rigid, so endpoint insertions are not seen by open intervals.
    sy = System(2, (1, 1), (2, 0), 0)
    assert sy.rigid_cycle_atoms() and 0 * 2 + 0 in sy.periodic_states()


def check_arithmetic(max_b: int) -> None:
    for b in range(1, max_b + 1):
        r, K = 6 * b, 12 * b - 1
        # audit bound: sum_{k<=K} (r + k - 1) = (12b-1)^2
        assert sum(r + k - 1 for k in range(1, K + 1)) == (12 * b - 1) ** 2
        # refined bound when the limb contains a non-rigid atom (z >= 1): K * (r - 1 + 1)
        refined = K * r
        assert refined == 72 * b * b - 6 * b
        assert refined < (12 * b - 1) ** 2 or b == 0
        assert refined + 2 <= 216 * b * b


def main() -> int:
    started = time.time()
    counters = dict.fromkeys(
        ["systems", "with_rigid_cycle", "without_rigid_cycle", "monotone", "max_h",
         "plateau_checks", "plateau_bound_attained", "chain_checks"], 0)
    plan = [(1, range(2, 8)), (2, range(2, 7)), (3, range(2, 5))]
    per_size = []
    for d, sizes in plan:
        for M in sizes:
            before = counters["systems"]
            chain = M <= 4
            for a, c, t0 in systems(M, d):
                check_system(System(M, a, c, t0), counters, chain)
            per_size.append(f"d={d} M={M}: {counters['systems'] - before}")
    cases = check_count_lemma(10)
    check_named_examples()
    check_arithmetic(1000)

    print("Marked contour substitution systems checked exhaustively (degree d, M atoms):")
    print("  " + "; ".join(per_size))
    print(f"  total {counters['systems']} systems: {counters['with_rigid_cycle']} with a rigid "
          f"cycle, {counters['without_rigid_cycle']} without")
    print("Verified on every one of them, by direct simulation of Phi:")
    print("  Lemma 1    length never drops while the image is proper "
          f"(inclusion-monotonicity on all state pairs for the {counters['monotone']} systems with M <= 5)")
    print("  Theorem 1  a nonempty proper periodic interval exists iff a rigid cycle exists, and the")
    print("             set of periodic proper intervals equals the predicted set exactly")
    print("  Theorem 2  without a rigid cycle no plateau repeats a state, all but its last state are")
    print(f"             rigid intervals, and the longest plateau has exactly h steps (largest h seen: {counters['max_h']})")
    print(f"  Cor. 3(b)  critical encounters on a plateau <= min(M, r+k-1, g_k+1): "
          f"{counters['plateau_checks']} plateau/limb pairs, bound attained {counters['plateau_bound_attained']} times")
    print(f"  Cor. 5     longest enlargement chain <= sum of those bounds, and the chain graph is acyclic: "
          f"{counters['chain_checks']} (system, r, K) cases with M <= 4")
    print(f"Lemma 4 (g_k <= r - z when z >= 1): all {cases} (rigid set, r, k) cases with M <= 10")
    print("Named examples: audit negative control; reducible incidence example; endpoint insertion")
    print("Arithmetic: (12b-1)^2 and the refined 72b^2-6b chain bounds for 1 <= b <= 1000")
    print(f"ALL CHECKS PASSED in {time.time() - started:.1f}s")
    return 0


if __name__ == "__main__":
    sys.exit(main())
