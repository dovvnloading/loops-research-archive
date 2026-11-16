"""Negative controls: reject perturbed native geometry and marking manifests."""
import copy
import json
import unittest

from verify import TIP, orbit, marking, certify, pi_range, cos_range, Q


class FiniteGuards(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.tip = json.loads(TIP.read_text(encoding='utf-8'))

    def test_original_source_passes(self):
        self.assertTrue(certify()['incidence']['failed_clause'])

    def test_parameter_mutation_fails(self):
        s = copy.deepcopy(self.tip)
        s['source_parameter']['upper_numerator'] += 1
        with self.assertRaises(AssertionError):
            orbit(s)

    def test_cover_mutation_fails(self):
        s = copy.deepcopy(self.tip)
        s['source_f_cover_atom_map'][10] = 1
        with self.assertRaises(AssertionError):
            marking(s)

    def test_inclusion_mutation_fails(self):
        s = copy.deepcopy(self.tip)
        s['source_inclusion_pullback_atom_map'][19] = 9
        with self.assertRaises(AssertionError):
            marking(s)

    def test_attachment_mutation_fails(self):
        s = copy.deepcopy(self.tip)
        s['attachment_boundary_source_atoms'] = [18, 0, 1]
        with self.assertRaises(AssertionError):
            marking(s)

    def test_wave_endpoint_mutation_fails(self):
        s = copy.deepcopy(self.tip)
        s['crossing_circle_source_restrictions'] = [[3, 1], [9, 11]]
        with self.assertRaises(AssertionError):
            marking(s)

    def test_strict_transcendental_enclosures(self):
        a,b = pi_range()
        c,d = cos_range(Q(3,5))
        self.assertTrue(Q(333,106) < a < b < Q(22,7))
        self.assertTrue(c < d < 1)


if __name__ == '__main__':
    unittest.main()
