"""Adversarial tests: detect false numerical/theorem promotions and row mutations."""
from fractions import Fraction as Q
import unittest

from verify import (
    CertificateError, GRID, THREE_CEILING, THREE_FLOORS,
    annulus_forced_K, check_algebra, check_row, check_three,
    conditional_crest, conditional_widths,
)


def sample_row(pair):
    radial, plane, gaps = GRID[pair]
    def interior(bounds):
        midpoint = Q(sum(bounds), 2 * 100000)
        return (midpoint, midpoint)
    return {
        "pair": pair,
        "root_chart_radius": Q(1, 10**80),
        "seed": Q(-2),
        "radial": interior(radial),
        "qplane": interior(plane),
        "radial5": radial,
        "qplane5": plane,
        "rouche1": Q(gaps[0], 10**6) + Q(1, 10**12),
        "rouche2": Q(gaps[1], 10**6) + Q(1, 10**12),
        "rouche3_normalized_lower": Q(gaps[2], 10**6) + Q(1, 10**12),
    }


class MarkedGlobalQCAuditTests(unittest.TestCase):
    def test_algebra_and_no_depth_compounding(self):
        check_algebra()
        for k in (Q(1), Q(5, 4), Q(17, 3)):
            self.assertEqual(
                conditional_widths(Q(1, 4), Q(39, 50), k, 10**8),
                (Q(1, 4)/k, Q(39, 50)*k))
            self.assertEqual(
                conditional_crest(Q(5676, 10000), Q(5684, 10000), k),
                (Q(5676, 10000)/(k*k), Q(5684, 10000)*k*k))
        self.assertEqual(conditional_widths("13/50", "39/50", "2"),
                         (Q(13, 100), Q(39, 25)))

    def test_no_fictitious_uniform_global_constant(self):
        self.assertEqual(annulus_forced_K(1, 1), 1)
        self.assertEqual(annulus_forced_K(1, 100000), 100000)
        self.assertEqual(annulus_forced_K(Q(1, 3), Q(2, 3)), 2)
        with self.assertRaises(CertificateError):
            annulus_forced_K(0, 10)

    def test_nine_locked_rational_rows_and_mutations(self):
        self.assertEqual(len(GRID), 9)
        for pair in GRID:
            with self.subTest(pair=pair):
                row = sample_row(pair)
                check_row(pair, row)
                bad = dict(row, radial=(Q(1, 4), Q(1, 4)))
                with self.assertRaisesRegex(CertificateError, "radial witness"):
                    check_row(pair, bad)
                bad = dict(row, qplane5=(0, 100000))
                with self.assertRaisesRegex(CertificateError, "plane grid bins"):
                    check_row(pair, bad)
                bad = dict(row, rouche2=Q(GRID[pair][2][1], 10**6))
                with self.assertRaisesRegex(CertificateError, "Rouché gap"):
                    check_row(pair, bad)
                bad = dict(row, radial=(float(0.26), float(0.26)))
                with self.assertRaisesRegex(CertificateError, "exact Fractions"):
                    check_row(pair, bad)
                with self.assertRaisesRegex(CertificateError, "wrong grid row"):
                    check_row(pair, dict(row, pair=(7, 7)))
                with self.assertRaisesRegex(CertificateError, "unsupported depth-two"):
                    check_row([3, 3], row)
                with self.assertRaisesRegex(CertificateError, "radial grid bins"):
                    check_row(pair, dict(row, radial5=None))

    def test_distinct_three_level_certificate(self):
        r = {name: Q(floor, 10**6) + Q(1, 10**12)
             for name, floor in THREE_FLOORS.items()}
        r["root_chart"] = Q(1, 10**80)
        r["plane_width_upper"] = Q(THREE_CEILING, 10**6) - Q(1, 10**12)
        check_three(r)
        wrong = dict(r, plane_width_upper=Q(THREE_CEILING, 10**6))
        with self.assertRaisesRegex(CertificateError, "upper envelope"):
            check_three(wrong)
        wrong = dict(r, normalized_third=Q(THREE_FLOORS["normalized_third"], 10**6))
        with self.assertRaisesRegex(CertificateError, "normalized_third"):
            check_three(wrong)

    def test_reject_invalid_assumptions(self):
        for call in (
            lambda: conditional_widths(0, 1, 2),
            lambda: conditional_widths(1, 1, 2),
            lambda: conditional_widths(Q(1, 4), 1, Q(1, 2)),
            lambda: conditional_widths(1, 2, 2, depth=True),
            lambda: conditional_widths(1, 2, 2, depth=0),
            lambda: conditional_widths(1, 2, float(2)),
            lambda: conditional_widths(1, 2, True),
            lambda: conditional_crest(0, 1, 1),
            lambda: conditional_crest(1, 2, float(2)),
        ):
            with self.subTest(call=call), self.assertRaises(CertificateError):
                call()


if __name__ == "__main__":
    unittest.main()
