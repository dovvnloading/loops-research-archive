"""Adversarial source/semantics tests for additive satellite v2."""
from __future__ import annotations

import copy
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import regenerate_satellite_v2 as sat


class SatelliteV2Tests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.fixture = json.loads(sat.INPUT.read_text(encoding="utf-8"))
        cls.registry = json.loads(sat.REGISTRY.read_text(encoding="utf-8"))

    def bad(self, change, reason):
        altered = copy.deepcopy(self.fixture)
        change(altered)
        with self.assertRaisesRegex(AssertionError, reason):
            sat.exact_case(altered)

    def test_exact_geometry_and_distinct_local_maps(self):
        o=sat.exact_case(self.fixture)
        self.assertEqual(o["bouquet"]["phase_intersection"],"K0 intersect K1={-a}")
        self.assertEqual(o["bouquet"]["rotation_number_f"],"1/2")
        self.assertEqual(o["bouquet"]["contact_period_f"],1)
        self.assertEqual(o["bouquet"]["return_slit_tip_access_count"],1)
        self.assertEqual(len(o["bouquet"]["ambient_contact_accesses"]),2)
        self.assertEqual(o["attachments"]["new_components"],[])
        g=o["contact_germs"]
        self.assertEqual(g["covering_preimages"],["-a","+a"])
        self.assertEqual(g["covering_local_degrees"],[1,1])
        self.assertEqual(g["covering_endpoint_germs"],2)
        self.assertEqual(g["immersion_preimages"],["-a"])
        self.assertEqual(g["immersion_local_degrees"],[1])
        self.assertEqual(g["immersion_endpoint_germs"],1)
        self.assertNotEqual(g["covering"],g["immersion"])
        self.assertEqual(g["through_deleted_contact_proper_paths"],0)
        self.assertIsNone(g["global_filtered_proper_restrictions"])
        self.assertIsNone(g["global_ideal_atom_tables"])

    def test_exact_symbolic_factor_and_spectral_matrix(self):
        self.assertEqual(sat.reduce_mod_P([2,2,2,1]),(0,0,0))
        self.assertNotEqual(sat.reduce_mod_P([2,2,2,2]),(0,0,0))
        o=sat.exact_case(self.fixture)["ambient_markov"]
        m=o["matrix_output_rows_input_columns"]
        self.assertEqual(o["edge_images"],[[1,2],[0],[0]])
        self.assertEqual(m,[[0,1,1],[1,0,0],[1,0,0]])
        self.assertEqual(sat.mat_mul(sat.mat_mul(m,m),m),[[2*x for x in row] for row in m])
        self.assertEqual(o["characteristic_polynomial"],"t*(t^2-2)")
        self.assertEqual(o["perron_root"],"sqrt(2)")
        self.assertIn("NOT KKL",o["operator_scope"])
        self.assertNotEqual(o["perron_root"],"(1+sqrt(5))/2")

    def test_root_degree_contact_and_v1_mutations_rejected(self):
        self.bad(lambda x:x["parameter"].__setitem__("denominator_power_of_two",127),"root isolator")
        self.bad(lambda x:x["parameter"].__setitem__("upper_numerator",x["parameter"]["lower_numerator"]),"root isolator")
        self.bad(lambda x:x["parameter"].__setitem__("lower_numerator",str(int(x["parameter"]["lower_numerator"])+1)),"root isolator")
        self.bad(lambda x:x["parameter"].__setitem__("lower_numerator",str(int(x["parameter"]["lower_numerator"])-1)),"root isolator")
        self.bad(lambda x:x["parameter"].__setitem__("equation","c^3=0"),"source parameter")
        self.bad(lambda x:x["renormalization"].__setitem__("restricted_degree",4),"degree/domain")
        self.bad(lambda x:x["renormalization"].__setitem__("physical_iterate",3),"degree/domain")
        self.bad(lambda x:x.__setitem__("v1_marking",{"small_julia_intervals":[1,2,3]}),"unknown satellite input field")
        self.bad(lambda x:x.__setitem__("record_compatibility","compatible"),"v1 semantic refusal")
        self.bad(lambda x:x.__setitem__("first_incompatible_field","WaveFamily"),"v1 semantic refusal")

    def test_source_registry_closed_and_wave_unformalized(self):
        out=sat.exact_case(self.fixture)
        out["primitive_comparison"]={k:{"attachments":1,
            "proper_restrictions_crossing_avoiding":[2,1],
            "parent_width":"unused","each_child_width":"unused",
            "harmonic_equality":True} for k in ("p3","p4")}
        sat.validate_sources(out,self.registry)
        mutated=copy.deepcopy(self.registry)
        del mutated["definitions"]["contact_germs.covering_endpoint_germs"]
        with self.assertRaisesRegex(AssertionError,"citation fields"):
            sat.validate_sources(out,mutated)
        mutated=copy.deepcopy(self.registry)
        mutated["definitions"]["wave.parent_exact_width"]["status"]="published"
        with self.assertRaisesRegex(AssertionError,"no published satellite Wave"):
            sat.validate_sources(out,mutated)
        mutated=copy.deepcopy(self.registry)
        mutated["definitions"]["wave.parent_exact_width"]["source_ids"]=["fake"]
        with self.assertRaisesRegex(AssertionError,"no published satellite Wave"):
            sat.validate_sources(out,mutated)
        mutated=copy.deepcopy(self.registry)
        mutated["definitions"]["ambient_markov.perron_root"]["source_ids"]=["fake"]
        with self.assertRaisesRegex(AssertionError,"missing explicit source"):
            sat.validate_sources(out,mutated)
        out["wave"]["parent_exact_width"]="0"
        with self.assertRaisesRegex(AssertionError,"no source-defined satellite Wave"):
            sat.validate_semantics(out)

    def test_immutable_baselines_and_manifest(self):
        for rel,sha in sat.V1_BLOBS.items():
            self.assertEqual(sat.blob_sha(sat.HERE/rel),sha)
        computed=sat.make_manifest(self.fixture)
        self.assertEqual(sat.MANIFEST.read_bytes(),sat.canonical(computed))
        self.assertEqual(computed["outputs_sha256"],
                         sat.hashlib.sha256(sat.canonical(computed["outputs"])).hexdigest())
        self.assertIsNone(computed["outputs"]["wave"]["parent_exact_width"])
        self.assertEqual(computed["outputs"]["primitive_comparison"]["p3"]["parent_width"],"log(4/3)/(2*pi)")
        self.assertEqual(computed["outputs"]["primitive_comparison"]["p4"]["parent_width"],"log(3/2)/(2*pi)")
        with tempfile.TemporaryDirectory() as folder:
            moved=Path(folder)/"spec.md"
            moved.write_bytes(sat.SPEC.read_bytes()+b"\n")
            with patch.object(sat,"SPEC",moved):
                self.assertNotEqual(computed["inputs"]["specification_sha256"],
                                    sat.make_manifest(self.fixture)["inputs"]["specification_sha256"])


if __name__=="__main__":
    unittest.main()
