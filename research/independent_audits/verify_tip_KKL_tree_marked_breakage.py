#!/usr/bin/env python3
"""Exact geometry + source-marking checks for actual KKL tree-complement breakage.

NOT the ordinary KL W->V duplicated-tile map.  This audit uses the existing
physical degree-two G=f^3:V3->U3 and its literal tree-complement inclusion.
The full original parameter/phase manifest is read in repository CI. All
numeric bounds are exact rational or outward-rounded dyadic intervals.
Dendrite, prime-end, covering and KKL Proposition 6.5 inputs remain written
analytic mathematics, not conclusions obtained from finite enumeration.
"""
from __future__ import annotations
import argparse
import json
from dataclasses import dataclass
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / 'results/tip_root_interval_geometry.json'
OUT = ROOT / 'results/tip_KKL_tree_marked_breakage_20261109.json'
SCALE = 1 << 256


def require(ok: bool, message: str) -> None:
    if not ok:
        raise AssertionError(message)


@dataclass(frozen=True)
class Interval:
    lo: int
    hi: int

    def __post_init__(self) -> None:
        require(self.lo <= self.hi, 'reversed interval')

    @staticmethod
    def point(x: F | int) -> 'Interval':
        y = F(x) * SCALE
        a = y.numerator // y.denominator
        b = -((-y.numerator) // y.denominator)
        return Interval(a, b)

    def __add__(self, other: 'Interval') -> 'Interval':
        return Interval(self.lo + other.lo, self.hi + other.hi)

    def __neg__(self) -> 'Interval':
        return Interval(-self.hi, -self.lo)

    def square(self) -> 'Interval':
        vals = [self.lo * self.lo, self.hi * self.hi]
        low = 0 if self.lo <= 0 <= self.hi else min(vals)
        high = max(vals)
        return Interval(low // SCALE, (high + SCALE - 1) // SCALE)

    def midpoint(self) -> F:
        return F(self.lo + self.hi, 2 * SCALE)

    def certified_lt(self, other: 'Interval') -> bool:
        return self.hi < other.lo

    def contains(self, x: 'Interval') -> bool:
        return self.lo <= x.lo <= x.hi <= self.hi


TARGET_NAMES = [
    'K2_terminal', 'edge_K2_K0_upper', 'K0_upper', 'edge_K0_alpha_upper',
    'edge_alpha_K1_upper', 'K1_terminal', 'edge_alpha_K1_lower',
    'edge_K0_alpha_lower', 'K0_lower', 'edge_K2_K0_lower',
]
SOURCE_CUT_LABELS = ['-x12', 'x6', 'x15', '-alpha', 'x9', 'x18',
                     'alpha', '-x15', '-x6', 'x12']
TARGET_CUT_LABELS = ['x15', 'x9', 'x18', 'alpha', 'x12']


def sample_atom(k: int, cuts: list[Interval], left: Interval,
                right: Interval) -> tuple[F, int]:
    """Chosen cyclic inner-circle indices: left terminal, upper interiors,
    right terminal, lower interiors reversed. +/- denotes physical side."""
    n = len(cuts)
    if k == 0:
        return (left.midpoint() + cuts[0].midpoint()) / 2, 1
    if k == n:
        return (cuts[-1].midpoint() + right.midpoint()) / 2, 1
    j, side = (k, 1) if k < n else (2 * n - k, -1)
    value = (cuts[j - 1].midpoint() + cuts[j].midpoint()) / 2
    # Critical point zero is inside a marked atom, not a marking endpoint.
    if abs(value) < F(1, 1000000):
        value = (2 * cuts[j - 1].midpoint() + cuts[j].midpoint()) / 3
    return value, side


def locate(value: Interval, side: int, cuts: list[Interval]) -> int:
    n = len(cuts)
    if value.certified_lt(cuts[0]):
        return 0
    if cuts[-1].certified_lt(value):
        return n
    for j in range(1, n):
        if cuts[j - 1].certified_lt(value) and value.certified_lt(cuts[j]):
            return j if side == 1 else 2 * n - j
    raise AssertionError('sample is not separated from a marking cut')


def span(a: int, b: int, size: int) -> int:
    return 1 + min((b - a) % size, (a - b) % size)


def check_filter(pair: list[int], coarse: list[int]) -> None:
    require(span(*pair, 20) > 2, 'KKL A.1 deletes this source path')
    require(coarse[pair[0]] != coarse[pair[1]],
            'single-pullback-interval exclusion not ruled out')
    require(span(pair[0] % 10, pair[1] % 10, 10) > 2,
            'dynamical pushforward is short under target marking')


def compute(source_path: Path = SOURCE) -> dict:
    original = json.loads(source_path.read_text(encoding='utf-8'))
    parameter = original['parameter_bracket']
    require(parameter == {'denominator_power_of_two': 128,
        'lower_numerator': -607918036626757496169199575185708826140,
        'upper_numerator': -607918036626757496169199575185708826139},
        'source parameter changed: redo dynamical audit')
    require('x18=-x9' in original['exact_orbit_relations'], 'missing exact root identity')
    require(original['inner_root_exact_interval'] == '[x9,x18]', 'fine root changed')
    require(original['phase_intervals_pairwise_disjoint'], 'phase separation absent')
    phases = {v['physical_phase']: v for v in original['phase_intervals']}
    for k, interval in [(0, '[x9,x18]'), (3, '[x12,x3]'), (6, '[x6,x15]')]:
        require(phases[k]['coarse_phase'] == 0 and phases[k]['exact_interval'] == interval,
                'source fine-phase interval drift')
    den = 1 << parameter['denominator_power_of_two']
    c_lo, c_hi = (F(parameter[k], den) for k in ('lower_numerator', 'upper_numerator'))
    c = Interval(int(c_lo * SCALE), int(c_hi * SCALE))
    orbit = [Interval.point(0)]
    for _ in range(27):
        orbit.append(orbit[-1].square() + c)
    x = {f'x{k}': orbit[k] for k in range(28)}

    def G(z: Interval) -> Interval:
        for _ in range(3):
            z = z.square() + c
        return z

    alpha = Interval(Interval.point(F(3, 32)).lo, Interval.point(F(1, 10)).hi)
    require(Interval.point(F(3, 32)).certified_lt(G(Interval.point(F(3, 32)))),
            'lower alpha bracket has wrong sign')
    require(G(Interval.point(F(1, 10))).certified_lt(Interval.point(F(1, 10))),
            'upper alpha bracket has wrong sign')
    x['alpha'] = alpha
    for k in ['x3', 'x6', 'x9', 'x12', 'x15', 'alpha']:
        x['-' + k] = -x[k]
    target_cuts = [x[k] for k in TARGET_CUT_LABELS]
    source_cuts = [x[k] for k in SOURCE_CUT_LABELS]
    for cuts in [target_cuts, source_cuts]:
        require(all(a.certified_lt(b) for a, b in zip(cuts, cuts[1:])),
                'cut order fails exact interval test')
    require(x['-x3'].certified_lt(x['x6']), 'new attachment empty')
    require(x['x3'].certified_lt(Interval.point(F(1, 4))), 'real tree outside U3')

    # G'(z)=8 z f(z) f^2(z): prove sign -sign(z) on entire real T'.
    first = Interval(0, x['x3'].hi).square() + c
    second = first.square() + c
    require(first.hi < 0 and second.lo > 0, 'real monotonicity sign not certified')

    # Source atom-to-target f* labels and inner inclusion pullback labels
    # are derived from physical positions and G, not asserted as a finite automaton.
    f_labels, inclusion_labels = [], []
    for s in range(20):
        sample, side = sample_atom(s, source_cuts, x['-x3'], x['x3'])
        value = Interval.point(sample)
        mapped_side = side if sample < 0 else -side
        f_labels.append(locate(G(value), mapped_side, target_cuts))
        inclusion_labels.append(0 if value.certified_lt(x['x6'])
                                else locate(value, side, target_cuts))
    require(f_labels == [s % 10 for s in range(20)], 'degree-two marking alignment fails')
    expected = [0, 0, 0, 1, 1, 2, 3, 4, 4, 4, 5, 6, 6, 6, 7, 8, 9, 9, 0, 0]
    require(inclusion_labels == expected, 'physical marking coarsening fails')
    blocks = [[18, 19, 0, 1, 2], [3, 4], [5], [6], [7, 8, 9], [10],
              [11, 12, 13], [14], [15], [16, 17]]
    require(sorted(k for b in blocks for k in b) == list(range(20)), 'not a partition')
    for target, block in enumerate(blocks):
        require(all(inclusion_labels[s] == target for s in block), 'wrong block label')
        require(all(b == (a + 1) % 20 for a, b in zip(block, block[1:])),
                'pullback is not a connected cyclic block')
    attachment_atoms = {19, 0, 1}
    require(all(b[0] not in attachment_atoms and b[-1] not in attachment_atoms
                for b in blocks), 'end-properness fails')
    nonproper = [i for i, b in enumerate(blocks) if attachment_atoms.intersection(b)]
    require(nonproper == [0], 'more than the attachment-host atom is nonproper')

    q, small_w, big_w = F(-1, 8), F(-5, 32), F(-13, 64)
    qi, wi = Interval.point(q), Interval.point(small_w)
    require(x['x15'].certified_lt(qi) and qi.certified_lt(x['-alpha']), 'q placement')
    require(x['-x12'].certified_lt(wi) and wi.certified_lt(x['x6']), 'slit crossing')
    require(Interval.point(big_w).certified_lt(x['-x3']), 'big circle fails to avoid Tprime')
    require(locate(qi, 1, target_cuts) == 1 and locate(qi, -1, target_cuts) == 9,
            'target marked endpoints differ from declared ones')
    require([locate(qi, 1, source_cuts), locate(wi, 1, source_cuts),
             locate(wi, -1, source_cuts), locate(qi, -1, source_cuts)] == [3, 1, 19, 17],
            'source path endpoint placement failed')
    small_pairs, big_pairs = [[3, 1], [19, 17]], [[3, 17]]
    for pair in small_pairs + big_pairs:
        check_filter(pair, inclusion_labels)
    require(span(1, 9, 10) == 3, 'target fails A.1')

    # Certify the WHOLE closed circle disks lie in V3 using disk arithmetic,
    # not sampling the boundary. Centers in invariant Tprime select central component.
    c_mid, c_rad = (c_lo + c_hi) / 2, (c_hi - c_lo) / 2
    circle_rows = []
    for name, w, bound, clearance in [('crossing', small_w, F(1, 20), F(1, 5)),
                                      ('avoiding', big_w, F(21, 100), F(1, 25))]:
        center, radius = (q + w) / 2, (q - w) / 2
        require(abs(center) + radius < F(1, 4), 'disk outside U3')
        require(x['-x3'].certified_lt(Interval.point(center)) and
                Interval.point(center).certified_lt(x['x3']), 'disk center not in Tprime')
        d, r = center, radius
        for _ in range(3):
            r = 2 * abs(d) * r + r * r + c_rad
            d = d * d + c_mid
        require(abs(d) + r < bound and F(1, 4) - abs(d) - r > clearance,
                'whole-disk complex containment not proved')
        circle_rows.append({'name': name, 'center': str(center), 'radius': str(radius),
                            'real_left_intersection': str(w), 'real_right_endpoint': str(q),
                            'certified_G_disk_image_absolute_bound': str(bound),
                            'certified_clearance_to_target_radius_1_over_4': str(clearance)})

    # An entire native marked wave: concentric circles centered at -9/64,
    # radii 3/256 < r < 1/64. Exact endpoint ranges stay in the SAME
    # authenticated marking intervals; the disk bound above covers all leaves.
    wave_center, r0, r1 = F(-9, 64), F(3, 256), F(1, 64)
    require(r0 < r1, 'wave empty')
    q_range = Interval(Interval.point(wave_center + r0).lo,
                       Interval.point(wave_center + r1).hi)
    w_range = Interval(Interval.point(wave_center - r1).lo,
                       Interval.point(wave_center - r0).hi)
    require(x['x15'].certified_lt(q_range) and q_range.certified_lt(x['-alpha']),
            'wave endpoints leave source atom S3/S17')
    require(x['-x12'].certified_lt(w_range) and w_range.certified_lt(x['x6']),
            'wave crossing points leave source attachment atoms S1/S19')
    require(r1 / r0 == F(4, 3), 'width ratio drift')

    # Type-independent finite rejection tests: changing multiplicity alone
    # never authorizes ignoring a path; cells + adjacency are mandatory.
    require(span(1, 2, 20) == 2, 'short-path negative control failed')
    require(inclusion_labels[1] == inclusion_labels[2], 'single-block negative control')

    return {
        'schema_version': 1,
        'scope': 'ACTUAL KKL Hubbard-tree marking for physical degree-two G=f^3:V3->U3 at the certified tip; NOT ordinary KL W->V tile duplication',
        'source_parameter': parameter,
        'arithmetic_precision_bits': 256,
        'tree': '[x6,x3]', 'tree_preimage_in_V3': '[-x3,x3]',
        'single_new_attachment': '[-x3,x6)',
        'target_inner_marking_atoms': TARGET_NAMES,
        'target_inner_cut_positions_increasing': TARGET_CUT_LABELS,
        'source_inner_cut_positions_increasing': SOURCE_CUT_LABELS,
        'source_f_cover_atom_map': f_labels,
        'source_inclusion_pullback_atom_map': inclusion_labels,
        'inner_pullback_blocks': blocks,
        'inner_pullback_lengths': [len(b) for b in blocks],
        'attachment_boundary_source_atoms': [19, 0, 1],
        'end_proper_on_all_ten_inner_intervals': True,
        'not_proper_on_target_inner_atoms': nonproper,
        'outer_circle_convention': 'one whole-component atom; inner attachment computation uses KKL Propositions 6.5-6.6, no claim of outer boundary properness',
        'circles': circle_rows,
        'marked_breakable_wave': {
            'center': str(wave_center), 'open_radius_interval': [str(r0), str(r1)],
            'right_endpoint_range': [str(wave_center + r0), str(wave_center + r1)],
            'attachment_crossing_range': [str(wave_center - r1), str(wave_center - r0)],
            'target_base_atoms': [9, 0, 1], 'target_crest_atom': 0,
            'two_pushed_base_atoms': [[1, 2, 3], [7, 8, 9]],
            'two_pushed_crest_atoms': [2, 8],
            'target_extremal_width': 'log(4/3)/(2*pi)',
            'each_restriction_and_pushforward_width': 'log(4/3)/pi',
            'child_width_multiplier': 2,
            'harmonic_series_inequality_is_equality': True,
            'proof': 'log(z-center) maps the target foliation to a rectangle of angle height 2*pi; removing the attachment gives two rectangles of angle height pi; G injective on the negative-half-plane wave support'
        },
        'target_endpoint_atom_pair': [1, 9],
        'crossing_circle_source_restrictions': small_pairs,
        'crossing_circle_coarse_endpoint_pairs': [[inclusion_labels[a], inclusion_labels[b]] for a, b in small_pairs],
        'crossing_circle_F_pushforward_atom_pairs': [[a % 10, b % 10] for a, b in small_pairs],
        'avoiding_circle_source_restrictions': big_pairs,
        'avoiding_circle_F_pushforward_atom_pairs': [[3, 7]],
        'both_crossing_restrictions_pass_A1_and_single_pullback_cell_filters': True,
        'same_target_arc_class_different_marked_restriction_counts': [2, 1],
        'homotopy': 'vary real left intersection w from -5/32 to -13/64; disks nested in the certified larger disk; all w<x6 so homotopy avoids T',
        'infinite_proof_not_finite_sampling': 'Circle intersection formulas and a whole-disk image enclosure prove the continuum of homotopic target paths; finite incidence is not substituted for the analytic argument',
        'analytic_trust_boundary': [
            'Previously certified exact parameter, K3/K9 polynomial-like representatives and small Julia interval identities',
            'Misiurewicz local connectivity/dendrite property identifies the native KKL connected hull with the real interval',
            'Degree two on V3, not the global degree-eight polynomial, excludes other preimages of the tree',
            'KKL 6.5 attachment formula and 6.6 marking/refinement theorem specialized to this native tree inclusion',
            'Prime ends of real slit complements and A.1/A.3.2 path definitions; no machine formalization of complex topology'
        ],
        'not_claimed': [
            'No counterexample to KKL: breakable paths are expressly allowed and this example is at the attachment-host interval',
            'No uniqueness failure for full lifts under an embedding: the two restrictions are disjoint subpaths, not duplicate full lifts',
            'No identification with the canonical unrestricted psi-localization or PR67 W->V immersion',
            'No large-q wave amplification or global H1-H4, UPTCR or MLC conclusion'
        ]
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source', type=Path, default=SOURCE)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check-manifest', action='store_true')
    mode.add_argument('--write-manifest', action='store_true')
    args = parser.parse_args()
    result = compute(args.source)
    if args.write_manifest:
        OUT.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n', encoding='utf-8')
        print('WROTE', OUT)
    elif args.check_manifest:
        require(json.loads(OUT.read_text(encoding='utf-8')) == result, 'manifest drift')
        print('PASS: 10/20 actual KKL inner atoms; attachment blocks [5,2,1,1,3,1,3,1,1,2]; exact whole-disk two-vs-one marked restriction witness')
    else:
        print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == '__main__':
    main()
