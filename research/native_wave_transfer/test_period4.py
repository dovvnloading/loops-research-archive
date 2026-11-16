#!/usr/bin/env python3
"""Adversarial, independent oracles for the second physical configuration."""
from __future__ import annotations

import copy
import json
import unittest
from pathlib import Path

import regenerate_period4 as p4
from regenerate import HERE, sha256


class PrimitivePeriodFourRegression(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.example=p4.load(p4.INPUT)
        cls.parameter=p4.load(p4.PARAMETER)
        cls.out=p4.recompute(cls.example,cls.parameter)

    def test_exact_parameter_bracket_and_primitive_domains(self) -> None:
        c, orbit=p4.certify_parameter(self.parameter)
        self.assertTrue(orbit[12].overlaps(-orbit[24]))
        self.assertTrue(c.low<c.high)
        self.assertEqual(self.out["return"],{
            "physical_iterate":4,"restricted_degree":2,"global_degree":16})
        self.assertEqual(self.out["domains"]["certificate"],{
            "outer_rouche_margin_gt":"1/25",
            "inner_f12_rouche_margin_gt":"1/100",
            "primitive_four_phase_balls_disjoint":True})
        self.assertEqual(self.out["marked_tree"]["hull"],"[x8,x4]")
        self.assertEqual(self.out["marked_tree"]["preimage_in_V4"],"[-x4,x4]")

    def test_two_independent_ideal_actions(self) -> None:
        b=self.out["ideal_boundary"]
        self.assertEqual((b["target_atom_count"],b["covering_source_atom_count"]),(10,20))
        self.assertEqual(b["target_real_cuts"],
                         ["x20","x12","x24","alpha","x16"])
        self.assertEqual(b["source_real_cuts"],
                         ["-x16","x8","x20","-alpha","x12",
                          "x24","alpha","-x20","-x8","x16"])
        self.assertEqual(b["outer_component_atom_count"],1)
        f=self.out["operations"]["covering_f_star"]
        i=self.out["operations"]["immersion_iota_star"]
        self.assertEqual(f["source_to_target"],list(range(10))*2)
        self.assertEqual(i["block_lengths"],[5,2,1,1,3,1,3,1,1,2])
        self.assertEqual(i["nonproper_target_atoms"],[0])
        self.assertEqual(i["source_to_pullback"],
                         [0,0,0,1,1,2,3,4,4,4,5,6,6,6,7,8,9,9,0,0])
        self.assertEqual(
            self.out["attachment_census"]["components"][0]["boundary_atoms"],
            [19,0,1])
        self.assertEqual(
            self.out["attachment_census"]["components"][0]["interval"],
            "[-x4,x8)")

    def test_marked_breakage_and_distinct_pushforward(self) -> None:
        a=self.out["sheet_paths"]
        self.assertEqual(a["endpoint_target_atoms"],[1,9])
        self.assertEqual(a["counts"],[2,1])
        self.assertEqual(a["instances"]["crossing"]["source_restrictions"],
                         [[3,1],[19,17]])
        self.assertEqual(a["instances"]["avoiding"]["source_restrictions"],
                         [[3,17]])
        self.assertEqual(a["instances"]["crossing"]["immersion_endpoint_pairs"],
                         [[1,0],[0,9]])
        self.assertEqual(a["instances"]["crossing"]["covering_pushforward_pairs"],
                         [[3,1],[9,7]])
        self.assertEqual(a["instances"]["avoiding"]["covering_pushforward_pairs"],
                         [[3,7]])
        self.assertEqual([z["certified_G_disk_image_absolute_bound"]
                          for z in a["circles"]],["1/32","1/20"])

    def test_old_edge_and_zero_edge_oracles(self) -> None:
        t=self.out["edge_transition"]
        self.assertEqual(t["edges"],["E20","E0a","Ea1"])
        self.assertEqual(t["matrix_output_rows_input_columns"],
                         [[0,0,1],[1,0,1],[1,1,0]])
        self.assertEqual(t["perron_root"],"(1+sqrt(5))/2")
        self.assertEqual(t["strictly_positive_power"],4)
        self.assertEqual(
            [a["new_attachment_sheets"] for a in t["inverse_edge_sheets"]],
            [[True,False],[False,False],[False,False]])
        z=self.out["zero_edge_sectors"]
        self.assertEqual(z["target_zero_old_edge_atoms"],[0,2,5,8])
        self.assertEqual(z["source_inclusion_zero_old_edge_atoms"],
                         [0,1,2,5,10,15,18,19])
        self.assertEqual(z["cover_pushforward_zero_old_edge_atoms"],
                         [0,2,5,8,10,12,15,18])
        self.assertTrue(z["parent_and_child_wave_crests_zero_old_edge"])

    def test_exact_wave_widths(self) -> None:
        w=self.out["wave"]
        self.assertEqual(w["center"],"-17/512")
        self.assertEqual(w["open_radii"],["1/256","3/512"])
        self.assertEqual(w["ratio"],"3/2")
        self.assertEqual(w["target_base"],[9,0,1])
        self.assertEqual(w["pushed_bases"],[[1,2,3],[7,8,9]])
        self.assertEqual(w["target_width"],"log(3/2)/(2*pi)")
        self.assertEqual(w["each_child_and_pushed_width"],"log(3/2)/pi")
        self.assertTrue(w["harmonic_series_equality"])

    def test_adversarial_changes_fail_closed(self) -> None:
        def failure(mutator):
            e=copy.deepcopy(self.example)
            c=copy.deepcopy(self.parameter)
            mutator(e,c)
            with self.assertRaises(AssertionError):
                p4.recompute(e,c)
        failure(lambda e,c:e["return"].__setitem__("physical_iterate",3))
        failure(lambda e,c:e["domains"]["target"].__setitem__("radius","1/4"))
        failure(lambda e,c:e["operations"]["immersion"].__setitem__("ideal_action","f_*"))
        failure(lambda e,c:c["parameter_bracket"].__setitem__("lower_numerator",
                   c["parameter_bracket"]["lower_numerator"]+8))
        failure(lambda e,c:e["marking"]["target_cuts"].reverse())
        failure(lambda e,c:e["paths"][0].__setitem__("disk_limit","1/128"))
        failure(lambda e,c:e["paths"][1].__setitem__("q","-1/32"))
        failure(lambda e,c:e["wave"].__setitem__("open_radii",["3/512","1/256"]))
        failure(lambda e,c:e["wave"].__setitem__("center","-1/32"))

    def test_sources_and_old_code_unchanged(self) -> None:
        lock=p4.source_lock()
        self.assertEqual(lock["arxiv_source"]["id"],"arXiv:2606.27272v1")
        contract=p4.load(p4.CONTRACT)
        declared=set(contract["sources"])
        for rec in contract["records"].values():
            for field,annotation in rec.items():
                self.assertEqual(len(annotation),2,field)
                self.assertIn(annotation[1],declared,field)
        old=p4.load(HERE/"experiment_manifests/tip_pr68.json")
        self.assertEqual(sha256(HERE/"regenerate.py"),
                         old["code"]["sha256"])
        self.assertEqual(old["outputs"]["return"]["physical_iterate"],3)

    def test_immutable_new_manifest(self) -> None:
        actual=p4.canonical(p4.build_manifest())
        self.assertEqual(p4.MANIFEST.read_bytes(),actual)


if __name__ == "__main__":
    unittest.main()
