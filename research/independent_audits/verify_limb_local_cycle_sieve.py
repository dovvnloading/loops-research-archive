#!/usr/bin/env python3
"""Exact finite-cyclic regression for the all-limb no-recurrence sieve.

Checks ONLY integer-marked circular limb partitions, not holomorphic dynamics,
KKL endpoint geometry, proper-path pullbacks, or the absence of native cycles.

    python research/independent_audits/verify_limb_local_cycle_sieve.py --check-manifest
"""
from __future__ import annotations

import argparse
import itertools
import json
import random
from pathlib import Path

MANIFEST = Path(__file__).resolve().parents[2] / 'results' / 'limb_local_cycle_sieve_20261107.json'


def crosses(k: int, r: int, neighbor: int) -> int:
    """Number of pairs (critical, neighbor) of proper nonempty fragments."""
    low = max(1, k - neighbor + 1)
    high = min(r - 1, k - 1)
    return max(0, high - low + 1)


def local_formula(k: int, r: int, left: int, right: int) -> int:
    inside = r - k + 1 if 1 <= k < r else 0
    return inside + crosses(k, r, left) + crosses(k, r, right)


def total_formula(r: int, left: int, right: int) -> int:
    return r * (r + 1) // 2 - 1 + (r - 1) * (left + right - 2)


def census(limb_lengths: tuple[int, ...], idx: int) -> tuple[dict[int, int], dict[int, int]]:
    """Enumerate every positive proper cyclic marked interval from first principles."""
    q = len(limb_lengths)
    assert q >= 3 and all(length >= 1 for length in limb_lengths)
    m = sum(limb_lengths)
    masks = []
    shift = 0
    for length in limb_lengths:
        mask = sum(1 << ((shift + j) % m) for j in range(length))
        masks.append(mask)
        shift += length
    critical_mask = masks[idx]
    # A punctured circle has every atom but omits a single cut. It is not C,
    # yet it STILL contains every whole open limb, so it cannot qualify.
    punctured_atom_mask = (1 << m) - 1
    assert all(punctured_atom_mask & limb == limb for limb in masks)
    counts = {}
    critical_only = {}
    for k in range(1, m):
        accepted = critical_partial = 0
        for start in range(m):
            interval = sum(1 << ((start + j) % m) for j in range(k))
            if not interval & critical_mask:
                continue
            if critical_mask & interval != critical_mask:
                critical_partial += 1
            if all(limb & interval != limb for limb in masks):
                accepted += 1
        counts[k] = accepted
        critical_only[k] = critical_partial
    return counts, critical_only


def audit(max_q: int = 5, max_limb: int = 5) -> dict:
    partitions = indices = length_cases = 0
    states_accepted = 0
    strict_improvements = 0
    max_gap = 0
    for q in range(3, max_q + 1):
        for sizes in itertools.product(range(1, max_limb + 1), repeat=q):
            partitions += 1
            for idx in range(q):
                indices += 1
                r = sizes[idx]
                left = sizes[(idx - 1) % q]
                right = sizes[(idx + 1) % q]
                brute, old = census(sizes, idx)
                for k, n in brute.items():
                    expected = local_formula(k, r, left, right)
                    assert n == expected, ('length sieve', sizes, idx, k, n, expected)
                    assert n <= old[k]
                    strict_improvements += int(n < old[k])
                    max_gap = max(max_gap, old[k] - n)
                    length_cases += 1
                    states_accepted += n
                assert sum(brute.values()) == total_formula(r, left, right), (
                    'total sieve', sizes, idx)
                assert max((k for k, v in brute.items() if v), default=0) <= (
                    r + max(left, right) - 2 if r > 1 else 0)

    # Actual interval counterexample to the incorrect critical-limb-only filter:
    # with adjacent 1-atom limbs, crossing them already forces future saturation.
    witness = (3, 1, 2, 1, 1)
    all_counts, old_counts = census(witness, 0)
    assert old_counts[2] == 4 and all_counts[2] == 2

    # Long rings, including q=24, to guard against accidental small-q wrapping.
    rng = random.Random(27072026)
    extended = 0
    for q in (6, 9, 24):
        for _ in range(80):
            sizes = tuple(rng.randint(1, 6) for _ in range(q))
            idx = rng.randrange(q)
            brute, _old = census(sizes, idx)
            r, left, right = sizes[idx], sizes[(idx-1) % q], sizes[(idx+1) % q]
            for k, count in brute.items():
                assert count == local_formula(k, r, left, right)
            assert sum(brute.values()) == total_formula(r, left, right)
            extended += 1
    return {
        'exhaustive_q': f'3 <= q <= {max_q}',
        'exhaustive_limb_lengths': f'1 <= length <= {max_limb}',
        'distinct_limb_partitions': partitions,
        'distinguished_critical_limb_cases': indices,
        'length_by_critical_cases': length_cases,
        'accepted_states_with_multiplicity': states_accepted,
        'strict_improvement_over_critical_limb_only_cases': strict_improvements,
        'max_per_length_gap_in_test': max_gap,
        'extended_seed': 27072026,
        'extended_partition_cases': extended,
        'critical_only_counterexample': {
            'limb_lengths': list(witness), 'critical_limb': 0, 'k': 2,
            'critical_limb_only': old_counts[2], 'all_limb_avoidance': all_counts[2]
        },
        'per_length_formula': '(r-k+1 if 1<=k<r else 0) + cross(k,r,left) + cross(k,r,right)',
        'cross': 'max(0, min(r-1,k-1)-max(1,k-neighbor+1)+1)',
        'total_formula': 'r*(r+1)//2 - 1 + (r-1)*(left+right-2)',
    }


def high_rotation_arithmetic(max_b: int = 1000) -> dict:
    for b in range(1, max_b + 1):
        r = left = right = 6*b
        cap = total_formula(r, left, right)
        assert cap == 90*b*b - 21*b + 1
        assert r + max(left, right) - 2 == 12*b - 2
        assert cap < (12*b-2)*(12*b-1)
    assert total_formula(6,6,6) == 70
    assert total_formula(3,1,1) == 5
    assert total_formula(1,6,6) == 0
    return {
        'max_b_checked': max_b,
        'source_inputs': 'q>=24b, all actual limb lengths <=6b, original limbs tile the marked circle',
        'max_local_cycle_candidates': '90*b*b - 21*b + 1',
        'max_candidate_length_when_nonempty': '12*b-2',
        'b1_worst_case_candidates': 70,
        'b1_critical_only_prior_cap': 110,
        'root_placement_required': False,
        'marked_length_monotonicity_required_for_cycle_iff': False,
        'actual_native_first_return_arrows_verified': False,
    }


def manifest() -> dict:
    return {
        'schema_version': 1,
        'method': 'exact integer marked-limb tiling regression only',
        'analytic_boundary': 'No proof of the actual KKL cut return map, WAD witness, or MLC',
        'source': 'KKL arXiv:2606.27272v1, section 6.1 after Proposition 6.6 and Lemma 4.8',
        'cycle_sieve': audit(),
        'uniform_bounds': high_rotation_arithmetic(),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument('--write-manifest', action='store_true')
    group.add_argument('--check-manifest', action='store_true')
    args = parser.parse_args()
    content = json.dumps(manifest(), sort_keys=True, indent=2) + '\n'
    if args.write_manifest:
        MANIFEST.parent.mkdir(parents=True, exist_ok=True)
        MANIFEST.write_text(content, encoding='utf-8')
        print('Wrote', MANIFEST)
    elif args.check_manifest:
        assert MANIFEST.read_text(encoding='utf-8') == content, 'Manifest mismatch'
        print('PASS: exact all-limb cycle sieve and byte-identical manifest')
    else:
        print(content, end='')


if __name__ == '__main__':
    main()
