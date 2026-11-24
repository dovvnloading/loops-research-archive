#!/usr/bin/env python3
"""Finite bookkeeping for Corollary 3.3 of NOTE.md (selected slit pair).

Blocks are derived from the two real cut lists and the order (O2). Images
also consume the covering alignment f_*(S_s) = I_(s mod 10), proved in
IDEAL_BOUNDARY.md (9); that alignment is not derived from the cut lists.
No block or image table is typed in by hand except as an expected value.
This checks finite contour bookkeeping. The component-pullback theorem
is a written proof, and its native KKL interpretation remains conditional
on the source-identification premise (MC) in NOTE.md.
"""
from __future__ import annotations

import itertools
import json
import sys

# Order (O2) of the relevant real points, left to right.  "-x" is the
# reflection of x.  The tips are -y1 (source only), y2 (target left tip) and
# y1 (common right tip).
ORDER = ["-y1", "-y4", "y2", "y5", "-a", "y3", "y6", "a", "-y5", "-y2", "y4", "y1"]
POS = {name: i for i, name in enumerate(ORDER)}

TARGET_CUTS = ["y5", "y3", "y6", "a", "y4"]            # IDEAL_BOUNDARY (6)
SOURCE_CUTS = ["-y4", "y2", "y5", "-a", "y3", "y6", "a", "-y5", "-y2", "y4"]  # (8)
TARGET_SLIT = ("y2", "y1")
SOURCE_SLIT = ("-y1", "y1")
TARGET_TIP = "y2"                                       # the access tau


def require(cond: bool, msg: str) -> None:
    if not cond:
        raise AssertionError(msg)


def accesses(slit, cuts):
    """Cyclic list of the marking endpoints of a slit's access circle.

    Starting just after the left tip on the upper bank and going round:
    upper accesses of the cuts left to right, then lower accesses right to
    left.  Each endpoint is (point, bank).
    """
    require(all(POS[slit[0]] < POS[c] < POS[slit[1]] for c in cuts), "cut off slit")
    require(cuts == sorted(cuts, key=POS.get), "cuts not sorted")
    return [(c, "+") for c in cuts] + [(c, "-") for c in reversed(cuts)]


def atoms(endpoints):
    """Atom k is the open arc between endpoint k-1 and endpoint k (cyclic).

    Atom 0 therefore contains the left tip, matching I_0 and S_0.
    """
    n = len(endpoints)
    return [(endpoints[(k - 1) % n], endpoints[k]) for k in range(n)]


T_END = accesses(TARGET_SLIT, TARGET_CUTS)   # 10 target endpoints
S_END = accesses(SOURCE_SLIT, SOURCE_CUTS)   # 20 source endpoints
I = atoms(T_END)                             # I_0..I_9
S = atoms(S_END)                             # S_0..S_19
require(len(I) == 10 and len(S) == 20, "atom counts")

# --- the contour map q on source marking endpoints -------------------------
# An access of T' over a point x > y2 is the same access of T.  Every access
# over [-y1, y2] (both banks and the far tip) is collapsed to tau.


def q_endpoint(e):
    point, bank = e
    if POS[point] <= POS[TARGET_TIP]:
        return "tau"
    return (point, bank)


# Position of a point of the target circle, as a number in [0, 10): the
# endpoint T_END[k] sits at k + 1/2 ... we only need to know in which closed
# target atom / at which target endpoint a source endpoint lands.

def target_location(e):
    """Return ('atom', k) or ('endpoint', k) for the q-image of a source endpoint."""
    img = q_endpoint(e)
    if img == "tau":
        return ("atom", 0)                      # tau is interior to I_0
    if img in T_END:
        return ("endpoint", T_END.index(img))
    point, bank = img
    # strictly between two target cuts (or beyond the last one) on that bank
    cuts = [TARGET_TIP] + TARGET_CUTS + [TARGET_SLIT[1]]
    for j in range(len(cuts) - 1):
        if POS[cuts[j]] < POS[point] < POS[cuts[j + 1]]:
            # upper bank segment j is atom j (j=0 is the tip atom), the last
            # segment is the right tip atom 5; lower bank mirrors.
            if j == 0:
                return ("atom", 0)
            if j == len(cuts) - 2:
                return ("atom", 5)
            return ("atom", j if bank == "+" else 10 - j)
    raise AssertionError(f"unlocated endpoint {e}")


loc = [target_location(e) for e in S_END]

# --- blocks B_k = q^{-1}(I_k) as runs of source atoms ----------------------
# Source atom s lies in q^{-1}(I_k) iff both of its endpoints map into the
# closure of I_k and the atom is not collapsed across another atom.  Since q
# is monotone of degree one, it suffices to walk the circle once.

def atom_target(s):
    """Target atom containing q(S_s) (S_s is never mapped onto an endpoint)."""
    a, b = loc[(s - 1) % 20], loc[s]
    cands = []
    for kind, k in (a, b):
        if kind == "atom":
            cands.append({k})
        else:                                   # endpoint k separates I_k, I_{k+1}
            cands.append({k, (k + 1) % 10})
    common = cands[0] & cands[1]
    require(len(common) == 1, f"ambiguous atom S_{s}: {a} {b}")
    return common.pop()


owner = [atom_target(s) for s in range(20)]
blocks = {k: [s for s in range(20) if owner[s] == k] for k in range(10)}

EXPECTED_BLOCKS = {
    0: [18, 19, 0, 1, 2], 1: [3, 4], 2: [5], 3: [6], 4: [7, 8, 9],
    5: [10], 6: [11, 12, 13], 7: [14], 8: [15], 9: [16, 17],
}


def cyclic_run(members, n=20):
    """Return the members as one cyclically consecutive run, or None."""
    ms = set(members)
    starts = [m for m in ms if (m - 1) % n not in ms]
    if len(starts) != 1:
        return None
    run, m = [], starts[0]
    while m in ms:
        run.append(m)
        m = (m + 1) % n
        if len(run) > n:
            return None
    return run if len(run) == len(ms) else None


for k in range(10):
    run = cyclic_run(blocks[k])
    require(run is not None, f"B_{k} is not a consecutive run")
    require(run == EXPECTED_BLOCKS[k], f"B_{k}: derived {run}, table {EXPECTED_BLOCKS[k]}")
    blocks[k] = run

# (2) partition
require(sorted(itertools.chain.from_iterable(blocks.values())) == list(range(20)),
        "blocks do not partition the 20 source atoms")

# (3) refinement: every block boundary is a source marking endpoint that maps
# to a target marking endpoint, and there are exactly ten of them.
boundary = [s for s in range(20) if owner[s] != owner[(s + 1) % 20]]
require(len(boundary) == 10, "expected ten block boundaries")
require(all(loc[s][0] == "endpoint" for s in boundary), "block boundary not over a target cut")
require(set(TARGET_CUTS) <= set(SOURCE_CUTS), "target cuts are not source cuts")

# (4) properness: iota fails to be proper exactly on atoms meeting the
# interior of attachment arc A (accesses over [-y1, y2)).


def meets_attachment(s):
    (p0, _), (p1, _) = S[s]
    lo = min(POS[p0], POS[p1])
    return lo < POS[TARGET_TIP] or s == 0


non_proper = sorted(s for s in range(20) if meets_attachment(s))
require(non_proper == [0, 1, 19], f"non-proper atoms {non_proper}")
for k in range(10):
    ends = {blocks[k][0], blocks[k][-1]}
    require(not (ends & set(non_proper)), f"iota not end-proper on B_{k}")
proper_targets = [k for k in range(10) if not (set(blocks[k]) & set(non_proper))]
require(proper_targets == list(range(1, 10)), "F should be proper exactly on I_1..I_9")

# (5) the contour/component action, with f_* S_s = I_{s mod 10}.
# This is the native action F_* only under premise (MC) in NOTE.md.
F = {k: [s % 10 for s in blocks[k]] for k in range(10)}
EXPECTED_F = {
    0: [8, 9, 0, 1, 2], 1: [3, 4], 2: [5], 3: [6], 4: [7, 8, 9],
    5: [0], 6: [1, 2, 3], 7: [4], 8: [5], 9: [6, 7],
}
require(F == EXPECTED_F, "F_* table mismatch")
for k in range(10):
    require(cyclic_run(F[k], 10) == F[k], f"F_* I_{k} is not a connected run")


# Derive the increasing degree-two lift on target marking cuts.  Cut k is
# the left endpoint of I_k, so its image is the first source cut of B_k.
# Adding ten to a target cut adds twenty to its lifted image.
CUT_LIFT = [blocks[0][0] - 20]
for k in range(10):
    CUT_LIFT.append(CUT_LIFT[-1] + len(blocks[k]))
require(CUT_LIFT[-1] == CUT_LIFT[0] + 20, "cut lift has wrong degree")


def lifted_cut(k):
    turn, index = divmod(k, 10)
    return CUT_LIFT[index] + 20 * turn


def push_open_arc(arc):
    """Push an open connected arc, preserving its two excluded endpoints.

    A pair (a, b) denotes the projection of (a, b) from the cut-index lift.
    None denotes the full circle.  A span of exactly ten is a punctured
    circle, even though it contains every open atom; only a span greater
    than ten includes every point of the circle.
    """
    if arc is None:
        return None
    a, b = arc
    require(0 < b - a <= 10, "invalid open arc")
    left, right = lifted_cut(a), lifted_cut(b)
    span = right - left
    if span > 10:
        return None
    left %= 10
    return left, left + span


# Regression: these open half-turns contain all atom labels after one
# iterate but omit their common endpoint.  The following iterate fills it.
halfturns = []
for start in range(10):
    for length in range(1, 10):
        if lifted_cut(start + length) - lifted_cut(start) == 10:
            image = push_open_arc((start, start + length))
            require(image is not None and image[1] - image[0] == 10,
                    "punctured circle incorrectly declared full")
            require(push_open_arc(image) is None, "punctured circle did not fill")
            halfturns.append([start, start + length])
require(halfturns == [[2, 8], [3, 9], [8, 12], [9, 13]],
        "open half-turn regression witnesses changed")

# Saturation: every proper connected open run of atoms, including internal
# joints and excluding its two endpoints, fills the circle within five
# steps, and five is attained.  Atom-label coverage alone is insufficient.
worst = 0
count = 0
open_atom_times = []
for start in range(10):
    for length in range(1, 10):
        cur = (start, start + length)
        steps = 0
        while cur is not None:
            cur = push_open_arc(cur)
            steps += 1
            require(steps <= 5, f"no saturation within five steps from {start},{length}")
        if length == 1:
            open_atom_times.append(steps)
        worst = max(worst, steps)
        count += 1
require(worst == 5, f"sharp bound should be five, got {worst}")

json.dump({
    "blocks": {f"I_{k}": [f"S_{s}" for s in blocks[k]] for k in range(10)},
    "non_proper_source_atoms": [f"S_{s}" for s in non_proper],
    "contour_action": {f"I_{k}": [f"I_{j}" for j in F[k]] for k in range(10)},
    "marked_runs_checked": count,
    "max_saturation_steps": worst,
    "cut_lift": CUT_LIFT,
    "open_atom_saturation_steps": open_atom_times,
    "open_halfturn_examples": halfturns,
    "status": "finite contour bookkeeping verified; component topology is a written proof; native identification conditional on (MC)",
}, sys.stdout, indent=2)
print()
