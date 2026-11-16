"""Adversarial assertions for finite crest-transport circular-collar certificate."""
import ast
import importlib.util
from fractions import Fraction as F
from pathlib import Path
import unittest
from unittest.mock import patch

HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('crest_asymptotics_verify',HERE/'verify.py')
v=importlib.util.module_from_spec(spec)
import sys
sys.modules[spec.name]=v
spec.loader.exec_module(v)


class CertificateTests(unittest.TestCase):
 def test_outward_negative_and_crossing_square(self):
  self.assertEqual((v.I.point(-3)*v.I.point(2)),v.I.point(-6))
  sq=v.I.hull(F(-1,5),F(1,3)).square()
  self.assertEqual(sq.lo,0)
  self.assertGreaterEqual(sq.upper(),F(1,9))
  self.assertLessEqual(sq.lower(),F(0))

 def test_transcendental_tails_and_exact_arithmetic(self):
  plo,phi=v.pi_bounds()
  self.assertLess(plo,phi)
  self.assertGreater(plo,F(314159,100000))
  self.assertLess(phi,F(314160,100000))
  self.assertEqual(v.asin_bounds(F(0)),(0,0))
  # A zero centred angle must fall between independent positive/negative
  # rational Maclaurin intervals, including the correct sign reversal.
  x=F(1,8)
  lo,hi=v.asin_bounds(x)
  mlo,mhi=v.asin_bounds(-x)
  self.assertEqual((mlo,mhi),(-hi,-lo))
  self.assertGreater(lo,x)
  self.assertGreater(hi,lo)
  self.assertLess(v.log_interval(F(2))[0],v.log_interval(F(2))[1])
  self.assertEqual(v.log_interval(F(1)),(0,0))

 def test_branch_mutation_is_rejected(self):
  with patch.dict(v.SEEDS,{13:v.SEEDS[14]}):
   with self.assertRaises(AssertionError):v.parameter(13)

 def test_wrong_immersion_partition_is_rejected(self):
  _,c,x=v.parameter(9)
  a=v.alpha(c,9,x)
  wrong=[list(b) for b in v.EXPECTED_BLOCKS]
  wrong[1]=[3,5]
  with patch.object(v,'EXPECTED_BLOCKS',wrong):
   with self.assertRaises(AssertionError):v.source_actions(c,9,x,a)

 def test_covering_and_immersion_are_distinct(self):
  _,c,x=v.parameter(9)
  cover,blocks,_=v.source_actions(c,9,x,v.alpha(c,9,x))
  self.assertEqual(cover,[s%10 for s in range(20)])
  host={s:i for i,block in enumerate(blocks) for s in block}
  self.assertEqual((host[0],host[3],host[17]),(0,1,9))
  self.assertNotEqual(host[3],cover[3])
  self.assertEqual([cover[s] for s in [0,3,17]],[0,3,7])

 def test_outer_parent_is_not_certified_as_terminal_collar(self):
  p=16
  _,c,x=v.parameter(p)
  d=v.I.point(-F(3,4))*x[p]
  rad=lambda q:q*x[p]
  lo,hi=F(1,16),F(p-1,8*p)
  u=v.gate(d,rad(v.I.point(hi)),c,p)
  r3=v.y_return(d,rad(v.I.point(hi)),u,c,p)[2]
  self.assertTrue((r3+x[p]).negative())
  bracket=v.bisect_terminal(p,c,x,d,rad,-x[p],lo,hi)
  self.assertTrue(bracket[0]<bracket[1]<hi)

 def test_certified_coarse_run_and_no_float_proof_oracle(self):
  row=v.run(9,64)
  self.assertEqual(row['p'],9)
  self.assertLess(row['original_fixed_subcollar']['ratio_bracket_1e5'][1],
                  row['ratio_bracket_1e5'][0])
  self.assertLess(row['ratio_bracket_1e5'][0],41811)
  self.assertGreater(row['ratio_bracket_1e5'][1],41810)
  parsed=ast.parse((HERE/'verify.py').read_text())
  self.assertFalse([node for node in ast.walk(parsed)
                    if isinstance(node,ast.Constant) and isinstance(node.value,float)])


if __name__=='__main__':unittest.main()
