import Period27Kneading

/-!
# Kernel-computed dyadic period-27 orbit certificate

This module reimplements the outward interval recurrence used by the
standard-library Python verifier at the coarser, still sufficient
integer resolution 2^144. The Lean kernel verifies the following
FINITE arithmetic consequences:

* opposite strict signs at the rational P27 bracket endpoints;
* strict negative parameter derivative throughout the bracket;
* strict signs of all 26 nonzero critical iterates;
* strict disjointness and order of all 27 orbit interval enclosures;
* exact correspondence of those kernel-computed signs/order with the
  already kernel-checked kneading and twisted-rank tables.

The correctness of the outward-interval interpretation and the
analytic IVT/MVT inference are mathematical facts whose proofs are
described separately. Do not confuse these integer computations with
a Lean formalization of real/complex analysis, parameter-ray landing,
prime-end transport, sheet transport, or MLC.
-/

namespace LoopsFormal.Period27

/-- Integer coordinates represent real numbers in units of 2^-128. -/
def unit : Int := 2 ^ 144

def parameterK : Int := -607890580437450502081459824019535455703

structure Bounds where
  lo : Int
  hi : Int
  deriving Repr, DecidableEq

def zeroBound : Bounds := ⟨0, 0⟩
def oneBound : Bounds := ⟨unit, unit⟩

def parameterStep : Int := 2 ^ 16

def parameterLower : Int := parameterK * parameterStep

def centerParameter : Bounds :=
  ⟨parameterLower, parameterLower + parameterStep⟩

def lowerParameter : Bounds := ⟨parameterLower, parameterLower⟩
def upperParameter : Bounds :=
  ⟨parameterLower + parameterStep, parameterLower + parameterStep⟩

def addBounds (a b : Bounds) : Bounds :=
  ⟨a.lo + b.lo, a.hi + b.hi⟩

/-- Integer floor and ceiling of an interval product divided by unit.
    Int division uses the floor convention at positive denominators. -/
def mulBounds (a b : Bounds) : Bounds :=
  let p1 := a.lo * b.lo
  let p2 := a.lo * b.hi
  let p3 := a.hi * b.lo
  let p4 := a.hi * b.hi
  let low := min (min p1 p2) (min p3 p4)
  let high := max (max p1 p2) (max p3 p4)
  ⟨low / unit, - ((-high) / unit)⟩

/-- Squaring a signed interval: handle a zero-crossing exactly. -/
def squareBounds (a : Bounds) : Bounds :=
  let p := a.lo * a.lo
  let q := a.hi * a.hi
  let low := if a.lo ≤ 0 ∧ 0 ≤ a.hi then 0 else min p q
  ⟨low / unit, - ((-(max p q)) / unit)⟩

def doubleBounds (a : Bounds) : Bounds :=
  ⟨2 * a.lo, 2 * a.hi⟩

def nextOrbit (c : Bounds) (x : Bounds) : Bounds :=
  addBounds (squareBounds x) c

def orbitTrace : Nat → Bounds → Bounds → List Bounds
  | 0, _, x => [x]
  | k + 1, c, x =>
      x :: orbitTrace k c (nextOrbit c x)

def pointAfter27 (c : Bounds) : Bounds :=
  (orbitTrace 27 c zeroBound).getD 27 zeroBound

/-- Joint forward iteration of x_j and d_j = dx_j/dc, with
    d_(j+1) = 2*x_j*d_j + 1. -/
def jointTrace : Nat → Bounds → Bounds → Bounds → List (Bounds × Bounds)
  | 0, _, x, d => [(x, d)]
  | k + 1, c, x, d =>
      (x, d) ::
      jointTrace k c
        (nextOrbit c x)
        (addBounds (mulBounds (doubleBounds x) d) oneBound)

def centerTrace : List (Bounds × Bounds) :=
  jointTrace 27 centerParameter zeroBound zeroBound

def orbitAt (j : Nat) : Bounds :=
  (centerTrace.getD j (zeroBound, zeroBound)).1

def derivativeAt (j : Nat) : Bounds :=
  (centerTrace.getD j (zeroBound, zeroBound)).2

theorem parameter_bracket_straddles_period27_root :
    (pointAfter27 lowerParameter).lo > 0 ∧
    (pointAfter27 upperParameter).hi < 0 := by
  decide +kernel

/-- Full endpoint enclosures at precision 2^-144, not merely signs. -/
theorem certified_endpoint_enclosures :
    pointAfter27 lowerParameter = ⟨4251281, 4252485⟩ ∧
    pointAfter27 upperParameter = ⟨-8835097, -8833684⟩ := by
  decide +kernel

theorem derivative_strict_negative :
    (derivativeAt 27).hi < 0 := by
  decide +kernel

theorem critical_period_proper_divisors_nonzero :
    (orbitAt 1).hi < 0 ∧
    (orbitAt 3).lo > 0 ∧
    (orbitAt 9).hi < 0 := by
  decide +kernel

def allNonzeroSignsStrict : Bool :=
  (List.range 26).all (fun j =>
    let x := orbitAt (j + 1)
    decide (x.hi < 0 ∨ x.lo > 0))

def inferredNegatives : List Bool :=
  (List.range 26).map (fun j =>
    decide ((orbitAt (j + 1)).hi < 0))

theorem all_critical_signs_are_certified :
    allNonzeroSignsStrict = true ∧
    inferredNegatives = negatives := by
  decide +kernel

def allOrbitVerticesStrictlyOrdered : Bool :=
  (List.range 26).all (fun j =>
    let a := realIncreasingIndices.getD j 0
    let b := realIncreasingIndices.getD (j + 1) 0
    decide ((orbitAt a).hi < (orbitAt b).lo))

theorem physical_orbit_order_verified_by_intervals :
    allOrbitVerticesStrictlyOrdered = true := by
  decide +kernel

theorem period27_dyadic_matches_symbolic_inputs :
    inferredNegatives = negatives ∧
    allOrbitVerticesStrictlyOrdered = true ∧
    realRanks = twistedRanks := by
  refine ⟨all_critical_signs_are_certified.2,
    physical_orbit_order_verified_by_intervals, ?_⟩
  exact all_27_ranks_agree.1.trans all_27_ranks_agree.2.symm

#print axioms certified_endpoint_enclosures
#print axioms parameter_bracket_straddles_period27_root
#print axioms derivative_strict_negative
#print axioms physical_orbit_order_verified_by_intervals
#print axioms period27_dyadic_matches_symbolic_inputs

end LoopsFormal.Period27
