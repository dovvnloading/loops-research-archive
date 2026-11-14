"""Exact finite cross-checks for the airplane phase-retrieval theorem. Python 3."""
from collections import Counter
from itertools import product


def phase_word(phases):
    """Signs in coefficient order; phases run from finest to coarsest scale."""
    signs = (1,)
    for phase in phases:
        signs += tuple(phase * x for x in signs) + tuple(-x for x in signs)
    return signs


def bit_word(signs):
    return "".join("0" if sign == 1 else "1" for sign in signs)


def autocorrelation(signs):
    size = len(signs)
    return tuple(
        sum(signs[i] * signs[i + shift] for i in range(size - shift))
        for shift in range(size)
    )


def predicted_correlation(level, shift):
    if shift % 2:
        return 0
    remaining = shift // 2
    nonzero = 0
    while remaining:
        digit = (remaining + 1) % 3 - 1
        nonzero += (digit != 0)
        remaining = (remaining - digit) // 3
    return (-1) ** nonzero * 3 ** (level - nonzero)


def angular_kneading(bits):
    denominator = (1 << len(bits)) - 1
    numerator = int(bits, 2)
    point = numerator
    result = []
    for _ in bits:
        double_point = 2 * point
        if double_point in (numerator, numerator + denominator):
            result.append("*")
        elif numerator < double_point < numerator + denominator:
            result.append("1")
        else:
            result.append("0")
        point = double_point % denominator
    return "".join(result)


def substitute(bits):
    return "".join("011" if symbol == "0" else "100" for symbol in bits)


def inflate_kneading(itinerary):
    opposite = {"0": "1", "1": "0", "*": "*"}
    return "".join("10" + opposite[symbol] for symbol in itinerary)


def inverse_binary_correlation(correlation):
    """Recover all fixed-origin binary words, independently of factorization.

    Peel in from the two ends. At lag N-1-i only the two outermost unknown
    products involve the newly assigned signs; each partial failure can be
    discarded before searching deeper. Check every lag at surviving leaves.
    """
    size = len(correlation)
    assert size >= 3 and size % 2
    signs = [None] * size
    signs[0] = 1
    signs[-1] = correlation[-1]
    assert signs[-1] in (-1, 1)

    def extend(depth):
        if depth > size // 2:
            candidate = tuple(signs)
            if autocorrelation(candidate) == correlation:
                yield candidate
            return
        right = size - 1 - depth
        positions = (depth,) if right == depth else (depth, right)
        for values in product((-1, 1), repeat=len(positions)):
            for i, value in zip(positions, values):
                signs[i] = value
            lag = right
            if sum(signs[i] * signs[i + lag] for i in range(depth + 1)) == correlation[lag]:
                yield from extend(depth + 1)
        for i in positions:
            signs[i] = None

    yield from extend(1)


def main():
    for level in (1, 2):
        size = 3 ** level
        census = Counter(
            autocorrelation((1,) + tail)
            for tail in product((-1, 1), repeat=size - 1)
        )
        maximum = max(census.values())
        winners = [corr for corr in census if census[corr] == maximum]
        assert maximum == 2 ** level
        assert winners == [autocorrelation(phase_word((-1,) * level))]
        print(f"Length {size}: full census of {2 ** (size - 1)} normalized words, one maximal class of {maximum}")

    for level in range(1, 6):
        size = 3 ** level
        target = tuple(predicted_correlation(level, h) for h in range(size))
        candidates = set()
        for phases in product((-1, 1), repeat=level):
            word = phase_word(phases)
            assert autocorrelation(word) == target
            assert tuple(word[3 ** j] for j in range(level)) == phases
            candidates.add(word)
        assert len(candidates) == 2 ** level
        if level == 3:
            recovered = set(inverse_binary_correlation(target))
            assert recovered == candidates
            assert len({angular_kneading(bit_word(w)) for w in recovered}) == len(recovered)
            print("Length 27: independent binary inverse search recovered exactly 8 words; 8 distinct kneadings")
        expected_angle = bit_word(phase_word((-1,) * level))
        assert expected_angle == max(map(bit_word, candidates))
        print(f"Length {size}: verified every lag of all {len(candidates)} predicted phase choices")

    actual = "011"
    twin = "001"
    for level in range(1, 8):
        actual_k = angular_kneading(actual)
        twin_k = angular_kneading(twin)
        expected_index = 2 * 3 ** (level - 1) - 1
        assert [i for i in range(len(actual)) if actual_k[i] != twin_k[i]] == [expected_index]
        assert actual_k[-1] == twin_k[-1] == "*"
        assert actual == bit_word(phase_word((-1,) * level))
        assert twin == bit_word(phase_word((-1,) * (level - 1) + (1,)))
        if level == 3:
            assert (int(actual, 2), int(twin, 2)) == (59914011, 59885851)
            print(f"Period 27: {actual_k} and {twin_k}, disparity at position {expected_index + 1}")
        if level < 7:
            actual, twin = substitute(actual), substitute(twin)
            assert angular_kneading(actual) == inflate_kneading(actual_k)
            assert angular_kneading(twin) == inflate_kneading(twin_k)
    print("Single-symbol kneading disparity verified through length 2187")


if __name__ == "__main__":
    main()
