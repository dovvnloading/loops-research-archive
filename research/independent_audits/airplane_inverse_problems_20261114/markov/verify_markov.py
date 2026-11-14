"""Exact checks for the loaded archive graph and substitution theorem. Python 3.9+."""
import argparse
import hashlib
import itertools
import json
from collections import Counter
from fractions import Fraction
from pathlib import Path


RANKS = [1, 19, 10, 16, 25, 7, 13, 22, 4, 6, 24, 15, 9, 0, 18,
         12, 21, 3, 5, 23, 14, 8, 26, 17, 11, 20, 2]
ADJACENCY_SHA256 = "1a9fdfc1a874090176ee3fcdf46db9efdcb5e05cf68318720afb35b04374d4d5"
MARKER = "LLRLLRR"


def check(condition, message):
    if not condition:
        raise ValueError(message)


def substitution(word):
    return "".join("RLR" if letter == "L" else "LLR" for letter in word)


def substitute_n(word, depth):
    for _ in range(depth):
        word = substitution(word)
    return word


def reachable(edges, vertex):
    visited = {vertex}
    frontier = [vertex]
    while frontier:
        for target in edges[frontier.pop()]:
            if target not in visited:
                visited.add(target)
                frontier.append(target)
    return visited


def read_graph(path):
    rank = {label: i for i, label in enumerate(RANKS)}
    images = [rank[(label + 1) % len(RANKS)] for label in RANKS]
    edges = [list(range(min(i, j), max(i, j))) for i, j in zip(images, images[1:])]
    compact = json.dumps(edges, separators=(",", ":")).encode()
    check(hashlib.sha256(compact).hexdigest() == ADJACENCY_SHA256, "adjacency hash")
    if path is not None:
        spine = json.loads(path.read_text())["real_interval_markov_spine"]
        check(spine["ordered_orbit_indices"] == RANKS, "manifest ranks")
        check(spine["edge_destinations"] == edges, "manifest edges")
        check(spine["edge_adjacency_sha256"] == ADJACENCY_SHA256, "manifest digest")
    return edges


def label(path):
    zero_rank = RANKS.index(0)
    return "".join("L" if vertex < zero_rank else "R" for vertex in path)


def get_components(edges):
    reach = [reachable(edges, i) for i in range(len(edges))]
    parts = {frozenset(j for j in row if i in reach[j]) for i, row in enumerate(reach)}
    parts = sorted(parts, key=len)
    check(list(map(len, parts)) == [2, 6, 18], "component sizes")
    for i, block in enumerate(parts):
        for j, other in enumerate(parts):
            check(bool(reach[min(block)] & other) == (i <= j), "chain orientation")
    return parts


def return_loops(edges, block):
    choices = {v: [w for w in edges[v] if w in block] for v in block}
    sites = [v for v, targets in choices.items() if len(targets) != 1]
    check(len(sites) == 1, "unique site")
    site = sites[0]
    check(len(choices[site]) == 2, "two first returns")
    loops = []
    for target in choices[site]:
        path = [site]
        while target != site:
            check(target not in path, "loop without a return")
            path.append(target)
            target = choices[target][0]
        loops.append(path)
    return sorted(loops, key=len)


def graph_words(edges, block, length):
    paths = [(v,) for v in block]
    for _ in range(length - 1):
        paths = [p + (w,) for p in paths for w in edges[p[-1]] if w in block]
    return {label(p) for p in paths}


def frequencies(period, length):
    counts = Counter()
    for start in range(len(period)):
        word = "".join(period[(start+i) % len(period)] for i in range(length))
        counts[word] += Fraction(1, len(period))
    return counts


def symbolic_words(depth, length):
    scale = 3 ** depth
    num_letters = (length + scale - 2) // scale + 1
    words = set()
    for source in itertools.product("LR", repeat=num_letters):
        if "RR" in "".join(source):
            continue
        image = substitute_n("".join(source), depth)
        for phase in range(scale):
            words.add(image[phase:phase+length])
    return words


def admitted(word, depth):
    if depth == 0:
        return "RR" not in word
    for variable_phase in range(3):
        fixed = {((variable_phase + 1) % 3): "L", ((variable_phase + 2) % 3): "R"}
        if any(i % 3 in fixed and fixed[i % 3] != w for i, w in enumerate(word)):
            continue
        preimage = "".join("R" if ch == "L" else "L" for ch in word[variable_phase::3])
        if admitted(preimage, depth-1):
            return True
    return False


def verify_frequency_identities():
    words = ["LLR", "LRR", "LRRLRL", "LRRLRLLRL", "LRRLRLLRLLRRLRLLRR"]
    a, b, c, short, long = [frequencies(w, 6) for w in words]
    for word in map("".join, itertools.product("LR", repeat=6)):
        check(3*short[word] == a[word]+2*c[word], "short six-block identity")
        check(6*long[word] == a[word]+b[word]+4*c[word], "long six-block identity")
    for i, period in enumerate(["LRRLRLLRL", "LRRLRLLRLLRRLRLLRR"]):
        source = substitute_n(["L", "LR"][i], 2)
        check(period in source*2 and len(period) == len(source), "cycle rotation")
    print("All 128 rational coordinates of the two six-block mixture identities agree.")


def verify_symbolic_depths(last_depth):
    marker = MARKER
    for depth in range(2, last_depth+1):
        threshold = 2*3**(depth-1)+1
        for length in (threshold-1, threshold):
            candidates = symbolic_words(depth, length)
            private = {w for w in candidates if not any(admitted(w, k) for k in range(depth))}
            check(private == ({marker} if length == threshold else set()), "minimum marker")
        print(f"Depth {depth}: checked unique shortest marker of length {threshold}.")
        marker = substitution(marker)[:-2]


def verify_full_recognition(last_depth):
    # Enumerate inner words, then test all coarser depths by parsing phases.
    # This is independent of the induction by which the threshold was derived.
    longest = "RLRLLR"
    for depth in range(1, last_depth+1):
        length = 7*3**(depth-1)
        for window in (length-1, length):
            shared = {w for w in symbolic_words(depth, window)
                      if any(admitted(w, j) for j in range(depth))}
            check(shared == ({longest} if window == length-1 else set()),
                  "largest shared window")
        longest = "LR"+substitution(longest)
        print(f"Depth {depth}: every inner window of length {length} identifies its depth.")


def verify_resonance():
    # Reduce x^6 and x^3 by x^2 = u(x+1). Coefficients are ordinary
    # integer polynomials in u. Seven distinct evaluations certify an
    # identity of degree at most six.
    for u in range(1, 8):
        power = [(1, 0)]
        for _ in range(6):
            a, b = power[-1]
            power.append((b*u, a+b*u))
        a3, b3 = power[3]
        a6, b6 = power[6]
        common = u*u*(u*u+3*u-1)
        check((a6-u*a3-u**3, b6-u*b3) == (common*u, common*(u+1)),
              "resonance polynomial remainder")
    lo_u, hi_u = Fraction(3027, 10000), Fraction(3028, 10000)
    lo_r, hi_r = Fraction(721, 1000), Fraction(723, 1000)
    check(lo_u**2+3*lo_u < 1 < hi_u**2+3*hi_u, "u enclosure")
    check(lo_r**2 < lo_u*(lo_r+1) and hi_r**2 > hi_u*(hi_r+1), "rho enclosure")
    y_min = lo_r**18/(hi_u**5*hi_r**9+hi_u**9)
    y_max = hi_r**18/(lo_u**5*lo_r**9+lo_u**9)
    check(17 < y_min < y_max < 19, "marker weight enclosure")
    print("Triple-point polynomial identity and rational weight enclosures passed.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path, help="archive results/period27_symbolic_marking.json")
    parser.add_argument("--depth", type=int, default=5, choices=range(2, 7))
    args = parser.parse_args()
    edges = read_graph(args.manifest)
    parts = get_components(edges)
    for depth, block in enumerate(parts):
        loops = return_loops(edges, block)
        words = [label(p) for p in loops]
        check(words == [substitute_n(w, depth) for w in ("L", "LR")], "return coding")
        print(f"Depth {depth}: {len(block)} vertices; return words {', '.join(words)}.")
        for word, path in zip(words, loops):
            # A six-letter continuation suffices to count every marker
            # beginning before the end of this return, across any seam.
            continuations = [tuple(path)]
            for _ in range(6):
                continuations = [p + (w,) for p in continuations for w in edges[p[-1]] if w in block]
            # First target after the end of a chosen return is its return site.
            continuations = [p for p in continuations if p[len(path)] == path[0]]
            for p in continuations:
                itinerary = label(p)
                hits = sum(itinerary[i:i+7] == MARKER for i in range(len(path)))
                check(hits == int(depth == 2), "marker count per return")
    for length in range(1, 8):
        w0, w1, w2 = [graph_words(edges, block, length) for block in parts]
        check(w2-(w0|w1) == ({MARKER} if length == 7 else set()), "archive marker")
        for depth, words in enumerate((w0, w1, w2)):
            check(words == symbolic_words(depth, length), "symbolic/graph agreement")
    for word, depth in [("LLR", 0), ("LRR", 1), ("LRRLRL", 1)]:
        check(admitted(word * 5, depth), "mixture witness")
    verify_frequency_identities()
    verify_symbolic_depths(args.depth)
    verify_full_recognition(min(args.depth, 4))
    verify_resonance()
    print("Archive adjacency, all loop weights, detector minimality and mixture checks passed.")


if __name__ == "__main__":
    main()
