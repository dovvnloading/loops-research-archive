import TipActualCoarseRays

/-!
Finite, kernel-recomputed 3/9 ray-correspondence and proper-access audit.

Only integer/rational facts are formalized here. The complex-analytic Levin
composition theorem, prime-end homotopy, and properness of actual ray ends
are proved in the companion written note from separately cited sources.
The selected eight physical ambient angles have denominator 523264;
the period-3 internal angles denominator 112, period-9 denominator 4.
-/

namespace LoopsFormal.TipLevinComposition

def ambientNum : Nat → Nat
  | 0 => 116736
  | 1 => 116791
  | 2 => 144841
  | 3 => 144896
  | 4 => 378368
  | 5 => 378423
  | 6 => 406473
  | 7 => 406528
  | _ => 0

def coarseNum : Nat → Nat
  | 0 => 80
  | 1 => 81
  | 2 => 87
  | 3 => 88
  | 4 => 24
  | 5 => 25
  | 6 => 31
  | 7 => 32
  | _ => 0

def fineNum : Nat → Nat
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | 4 => 2
  | 5 => 3
  | 6 => 3
  | 7 => 0
  | _ => 0

def returnIndex : Nat → Nat
  | 0 => 0
  | 1 => 3
  | 2 => 4
  | 3 => 7
  | 4 => 0
  | 5 => 3
  | 6 => 4
  | 7 => 7
  | _ => 0

/-- Only the eight source-proven eligible inputs are semiconjugated.
    This total function has no asserted dynamical meaning elsewhere. -/
def finiteQ (numerator : Nat) : Nat :=
  if numerator = 80 ∨ numerator = 32 then 0
  else if numerator = 81 ∨ numerator = 87 then 1
  else if numerator = 88 ∨ numerator = 24 then 2
  else if numerator = 25 ∨ numerator = 31 then 3
  else 0

def fineNumerators : List Nat :=
  [116736, 116791, 144841, 144896, 378368, 378423, 406473, 406528]

/-- The physically validated parent alpha-puzzle 32-ray sector set
    contains eight fine accesses and twenty-four coarse-only accesses. -/
theorem eight_fine_twenty_four_coarse :
    (LoopsFormal.TipActualCoarseRays.ambient32.filter
       (fun n => fineNumerators.contains n)).length = 8 ∧
    (LoopsFormal.TipActualCoarseRays.ambient32.filter
       (fun n => !(fineNumerators.contains n))).length = 24 ∧
    fineNumerators.Nodup ∧
    (∀ n ∈ fineNumerators, n ∈ LoopsFormal.TipActualCoarseRays.ambient32) := by
  decide +kernel

/-- Exact physical F^9, coarse g^3, and fine polynomial return clocks. -/
theorem all_eight_source_return_equations :
    ∀ i ∈ List.range 8,
      (512 * ambientNum i) % 523264 = ambientNum (returnIndex i) ∧
      (8 * coarseNum i) % 112 = coarseNum (returnIndex i) ∧
      (2 * fineNum i) % 4 = fineNum (returnIndex i) := by
  decide +kernel

/-- All eight coarse internal angles differ. -/
theorem coarse_eight_distinct :
    ((List.range 8).map coarseNum).Nodup := by
  decide +kernel

/-- Exactly two source ray labels for each of four fine angles. -/
theorem four_exact_two_element_fibers :
    ∀ k ∈ List.range 4,
      ((List.range 8).filter (fun i => fineNum i == k)).length = 2 := by
  decide +kernel

/-- Source table is precisely the finite graph of Q o Pi3 = Pi9. -/
theorem all_eight_factor :
    ∀ i ∈ List.range 8, finiteQ (coarseNum i) = fineNum i := by
  decide +kernel

/-- Dynamical commutation only on the selected invariant eight-ray set. -/
theorem eligible_eight_semi :
    ∀ i ∈ List.range 8,
      finiteQ ((8 * coarseNum i) % 112) =
      (2 * finiteQ (coarseNum i)) % 4 := by
  decide +kernel

#print axioms eight_fine_twenty_four_coarse
#print axioms all_eight_source_return_equations
#print axioms coarse_eight_distinct
#print axioms four_exact_two_element_fibers
#print axioms all_eight_factor
#print axioms eligible_eight_semi

end LoopsFormal.TipLevinComposition
