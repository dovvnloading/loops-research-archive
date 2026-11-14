"""Independent exact checks of ray landing diagnostics and phase readouts. Python 3."""
import json
from itertools import combinations, product
from pathlib import Path


def word(phases):
    """Evaluate each coefficient from its ternary site digits."""
    sites = []
    for index in range(3 ** len(phases)):
        coefficient = 1
        for phase in phases:
            index, digit = divmod(index, 3)
            coefficient *= (1, phase, -1)[digit]
        sites.append(coefficient)
    return sites


def audit(phases):
    signs = word(phases)
    bits = ''.join('0' if a == 1 else '1' for a in signs)
    numerator = int(bits, 2)
    denominator = 2 ** len(bits) - 1
    pos = numerator
    kneading = []
    first_hit = None
    for i in range(len(bits)):
        step = 2 * pos
        edges = (numerator, denominator + numerator)
        kneading.append('*' if step in edges else str(int(edges[0] < step < edges[1])))
        pos = step % denominator
        if first_hit is None and numerator < pos < denominator - numerator:
            first_hit = i + 1
    assert pos == numerator
    assert kneading.count('*') == 1 and kneading[-1] == '*'
    for j, s in enumerate(phases):
        recovered = int(kneading[2 * 3**j - 1]) ^ (j % 2)
        assert recovered == int(s == 1)
    expected_hit = 3 ** phases.index(1) if 1 in phases else None
    assert first_hit == expected_hit

    mass = sum(signs)
    assert abs(mass) == 1
    phase_slope = sum(i * a for i, a in enumerate(signs)) // mass
    assert phase_slope == (len(bits) - 1) // 2 - 2 * sum(3**j * s for j, s in enumerate(phases))
    return {
        'phases_fine_to_coarse': ''.join('+' if s == 1 else '-' for s in phases),
        'angle_numerator': numerator, 'angle_denominator': denominator,
        'bit_word': bits, 'kneading': ''.join(kneading), 'first_gap_hit': first_hit,
        'forward_phase_slope': phase_slope,
    }


def main():
    for k in range(1, 8):
        all_phases = list(product((-1, 1), repeat=k))
        rows = [audit(phases) for phases in all_phases]
        assert len({row['kneading'] for row in rows}) == 2**k
        assert len({row['forward_phase_slope'] for row in rows}) == 2**k
        if k <= 5:
            for (s, a), (t, b) in combinations(zip(all_phases, rows), 2):
                flipped = sum(u != v for u, v in zip(s, t))
                distances = sum(u != v for u, v in zip(a['bit_word'], b['bit_word']))
                assert 2 * distances == 3**k - 3**(k-flipped)
        if k == 3:
            exact = Path(__file__).with_name('period27_readout.json')
            assert rows == json.loads(exact.read_text()), 'period-27 record differs'
        print(f'PASS length {3**k}, all {2**k} phase vectors')


if __name__ == '__main__':
    main()
