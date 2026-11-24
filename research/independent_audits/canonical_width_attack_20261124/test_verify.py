"""Adversarial normalization and scope regressions for the written theorem."""
from fractions import Fraction as F
import json
from pathlib import Path
import unittest
from unittest.mock import patch

import verify as proof


class BufferedExclusionChecks(unittest.TestCase):
    def test_landen_two_square_threshold(self):
        root2 = proof.I.point(2).sqrt()
        m = proof.I.point(12)*root2-proof.I.point(16)
        q = proof.v.elliptic_factor(m)/proof.v.elliptic_factor(proof.ONE-m)
        self.assertLess(q.low(), F(2))
        self.assertGreater(q.high(), F(2))
        self.assertLess(q.high()-q.low(), F(1, 10**12))

    def test_half_log_distance_not_full_log(self):
        # cosh(log(2)/2)=3/(2sqrt(2)); r=(cosh(d)-1)/(cosh(d)+1).
        root2 = proof.I.point(2).sqrt()
        ch = proof.I.point(3)/(proof.TWO*root2)
        r = (ch-proof.ONE)/(ch+proof.ONE)
        q = proof.v.elliptic_factor(proof.ONE-r)/proof.v.elliptic_factor(r)
        self.assertLess(q.low(), F(2))
        self.assertGreater(q.high(), F(2))
        # Substituting d=log(2) gives cosh(d)=5/4 and r=1/9;
        # this is already strictly below the two-square threshold.
        wrong_r = proof.I.point(F(1, 9))
        wrong_q = (proof.v.elliptic_factor(proof.ONE-wrong_r)
                   / proof.v.elliptic_factor(wrong_r))
        self.assertLess(wrong_q.high(), F(8, 5))

    def test_ring_reflection_doubles_energy(self):
        # A square half-domain has conductance one, its double two.
        ell = proof.ring_length_bound(proof.I.point(F(1, 2)))
        pi = proof.v.pi_interval()
        self.assertLess(ell.low(), 2*pi.high())
        self.assertGreater(ell.high(), 2*pi.low())
        self.assertGreater(ell.low(), 6)
        self.assertGreater(ell.low(), pi.high())

    def test_disk_cross_ratio_matches_uncancelled_map(self):
        b, a, d, c, radius = map(F, (-3, F(-1, 2), F(1, 4), 2, 4))
        h = lambda z: z+radius*radius/z
        B, A, D, C = (h(z) for z in (b, a, d, c))
        expected = (D-A)*(C-B)/((D-B)*(C-A))
        got = proof.cross_ratio(*(proof.I.point(z) for z in (b,a,d,c,radius)))
        self.assertLessEqual(got.low(), expected)
        self.assertGreaterEqual(got.high(), expected)

    def test_reversed_or_outside_electrodes_rejected(self):
        point = proof.I.point
        with self.assertRaisesRegex(AssertionError, "unordered"):
            proof.cross_ratio(point(-2),point(1),point(-1),point(2),point(3))
        with self.assertRaisesRegex(AssertionError, "outside"):
            proof.cross_ratio(point(-2),point(-1),point(1),point(4),point(3))

    def test_coarse_collar_caps_are_insufficient(self):
        # Rounding to 6 and 4.2 loses the margin; the tighter caps matter.
        coarse = proof.collar_cosh_bound(F(6), F(21, 5))
        self.assertLess(coarse.high()**2, F(9, 8))
        sharp = proof.collar_cosh_bound(F(597, 100), F(419, 100))
        self.assertGreater(sharp.low()**2, F(9, 8))

    def test_unsplit_broad_p13_tail_is_rejected(self):
        with self.assertRaisesRegex(AssertionError, "length cap failed"):
            proof.certify_chart("invalid broad replacement", *proof.uniform_tail_chart(13))

    def test_sixth_cut_uses_exact_tip_reflection(self):
        parameter, orbit = proof.v.isolate_model()
        # Remove the sixth iterate completely. The tail must use the
        # exact physical identity X6=-X3, not a j=6 derivative estimate.
        with patch.object(proof.v, "isolate_model", return_value=(parameter, orbit[:6])):
            x, _ = proof.uniform_tail_chart()
        self.assertEqual(x[6], -x[3])

    def test_certificate_replays_exactly(self):
        saved = json.loads((Path(__file__).parent / "certificate.json").read_text())
        self.assertEqual(saved, proof.certify())
        self.assertEqual([r["case"] for r in saved["cases"]],
                         ["10","11","12","13","14","15","16","all p>=17"])


if __name__ == "__main__":
    unittest.main()
