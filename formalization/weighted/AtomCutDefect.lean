import LimbInsertionHolonomy
import Mathlib

/-!
# Exact finite cell-incidence check for a REAL quadratic slit-carrier

The *analytic* input is the periodically repelling Misiurewicz polynomial
  P_c(z) = z² + c,  c³+2c²+2c+2=0,
with old Hubbard interval [c,c²+c] and full preimage [c,-c].

Exact holomorphic Joukowski charts show that, in the genuine refined
four-atom marking, the four atom IMAGE supports are:
  0 -> {1,2}, 1 -> {3}, 2 -> {0}, 3 -> {1,2}.
But the marked internal cut 0 has a NONTRIVIAL immersion attachment:
  F_* {cut 0} covers the outer atoms {0,3}.
The true open input Jout contains that cut; atom-only propagation
wrongly predicts a period-two proper orbit.

This Lean module checks ONLY the exact finite set algebra once those
geometric source incidences have been proved on the actual polynomial.
It does not certify Joukowski uniformization, the existence of a
source-defined native KKL critical-gate atlas, or MLC.
-/

namespace LoopsNativeAtomCut

def atomImage (i : Fin 4) : Finset (Fin 4) :=
  if i = 0 ∨ i = 3 then {1, 2}
  else if i = 1 then {3}
  else {0}

/-- Naive *atom-only* map, an invalid map on connected open
multi-intervals because it omits internal marked cut fibers. -/
def atomOnly (s : Finset (Fin 4)) : Finset (Fin 4) :=
  s.biUnion atomImage

def middleAtoms : Finset (Fin 4) := {1, 2}
def outerAtoms : Finset (Fin 4) := {0, 3}

/-- The incorrect finite atom-only action exhibits an apparent
periodic two-cycle. All atoms are real analytic old sides;
the problem is OMITTED ZERO-CELL ATTACHMENT. -/
theorem atom_only_apparent_two_cycle :
    atomOnly middleAtoms = outerAtoms ∧
    atomOnly outerAtoms = middleAtoms := by
  decide

/-- The true polynomial's INTERNAL old tip cut maps through the
whole attached branch boundary; its target image contains both
outer atoms (and the exterior endpoint cuts). -/
def internalTipCutImageAtoms : Finset (Fin 4) := outerAtoms

/-- The true open interval Jout consists of outer atoms PLUS the
internal marked tip cut. Its next covering image has ALL 4 atoms,
and in the real analytic stage all intervening cuts, so saturates. -/
theorem internal_cut_stalk_kills_atom_only_cycle :
    atomOnly outerAtoms ∪ internalTipCutImageAtoms =
      (Finset.univ : Finset (Fin 4)) := by
  decide

/-- The actual continuous-cycle obstruction is a partial return
graph on Mid and Out: the next return from Out is terminal because
the REAL immersed pullback saturates. This is NOT an independently
chosen dynamical claim: the transition table is derived in the
companion Joukowski proof. -/
inductive RealGate
  | mid
  | out
deriving DecidableEq, Repr

def realGateReturn : RealGate → Option RealGate
  | .mid => some .out
  | .out => none

def realGateRank : RealGate → ℕ
  | .mid => 2
  | .out => 1

theorem realGate_rank_decreases
    (x y : RealGate) (h : realGateReturn x = some y) :
    realGateRank y < realGateRank x := by
  cases x <;> cases y <;> simp [realGateReturn, realGateRank] at *

/-- For the certified analytic two-gate subsystem no positive return
length can bring a proper marked interval back to itself. -/
theorem no_real_gate_two_cycle
    (x : RealGate) (n : ℕ) (hn : 0 < n) :
    LoopsKKLLimbInsertion.partialIter realGateReturn n x ≠ some x :=
  LoopsKKLLimbInsertion.no_periodic_partial_gate_of_rank
    realGateReturn realGateRank realGate_rank_decreases x n hn

end LoopsNativeAtomCut
