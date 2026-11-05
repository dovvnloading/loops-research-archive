import Lean

/-!
# Kernel-checked finite period-27 kneading and marking information

This module checks finite symbolic transformations:
* 26 signed real critical iterates -> 27-bit kneading angle;
* two airplane substitutions -> the same binary word;
* exact doubling period and unique closest-to-half angle;
* twisted 27-state shift -> every lexical cyclic rank;
* real critical-orbit order -> identical 27 ranks;
* necessary 9-to-3 phase-fiber constancy for a lossless marking.

Finite proofs use decide +kernel, not native_decide, axioms, or holes.

BOUNDARY: the sign list and the strict real orbit order are input
from a separate outward dyadic Python interval certificate.
Lean verifies their combinatorial consequences, not the soundness of
that Python arithmetic or the analytic realization. No actual
parameter-ray landing, KL prime-end access, sheet transport, or MLC
gate is inferred.
-/

namespace LoopsFormal.Period27

/-- Strict signs of x1 through x26, with negative encoded by true. -/
def signString : String := "-++-+--+--++-+--++-++-+--+"

def negatives : List Bool :=
  signString.toList.map (fun c => c == '-')

/-- Real signed kneading-angle bits: keep on +, toggle on -. -/
def kneading : Bool → List Bool → List Bool
  | b, [] => [b]
  | b, h :: t => b :: kneading (if h then !b else b) t

def angleBits : List Bool := kneading false negatives

def binaryValue (bits : List Bool) : Nat :=
  bits.foldl (fun n b => n * 2 + if b then 1 else 0) 0

def sigmaBit (b : Bool) : List Bool :=
  if b then [true, false, false] else [false, true, true]

def tune (bits : List Bool) : List Bool :=
  bits.flatMap sigmaBit

def airplane : List Bool := [false, true, true]
def twiceTuned : List Bool := tune (tune airplane)

def angleNumerator : Nat := binaryValue angleBits
def angleDenominator : Nat := 2 ^ 27 - 1

theorem critical_sign_count : negatives.length = 26 := by decide +kernel

theorem exactly_27_kneading_bits : angleBits.length = 27 := by decide +kernel

theorem kneading_matches_twice_tuned_airplane :
    angleBits = twiceTuned := by decide +kernel

theorem exactly_certified_angle :
    angleNumerator = 59914011 ∧
    angleDenominator = 134217727 ∧
    angleDenominator - angleNumerator = 74303716 := by
  decide +kernel

def angleOrbit : List Nat :=
  (List.range 27).map (fun j =>
    (angleNumerator * (2 ^ j)) % angleDenominator)

theorem period_27_doubling :
    angleOrbit.length = 27 ∧
    angleOrbit.Nodup ∧
    (angleNumerator * (2 ^ 27)) % angleDenominator =
      angleNumerator := by
  decide +kernel

def twiceDistanceToHalf (n : Nat) : Nat :=
  if 2 * n < angleDenominator then angleDenominator - 2 * n
  else 2 * n - angleDenominator

theorem closest_to_half_in_doubling_orbit :
    ((angleOrbit.drop 1).all
      (fun n => twiceDistanceToHalf angleNumerator <
        twiceDistanceToHalf n)) = true := by
  decide +kernel

def complement (word : List Bool) : List Bool :=
  word.map (fun b => !b)

/-- Modified tent-map cyclic shift: rotate, then flip if new head is 0. -/
def twistedShift (word : List Bool) : List Bool :=
  let rotated := word.drop 1 ++ word.take 1
  match rotated with
  | [] => []
  | b :: bs => if b then b :: bs else complement (b :: bs)

def iterateTwisted : Nat → List Bool → List (List Bool)
  | 0, _ => []
  | k + 1, word => word :: iterateTwisted k (twistedShift word)

def codedOrbit : List (List Bool) :=
  iterateTwisted 27 (complement angleBits)

def lexLt : List Bool → List Bool → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs =>
      if a == b then lexLt as bs else (!a && b)

def twistedRanks : List Nat :=
  codedOrbit.map (fun w =>
    1 + (codedOrbit.filter (fun v => lexLt v w)).length)

/-- Independently signed-dyadic sorted indices x_j for j = 0,...,26. -/
def realIncreasingIndices : List Nat :=
  [1, 19, 10, 16, 25, 7, 13, 22, 4, 6,
   24, 15, 9, 0, 18, 12, 21, 3, 5, 23,
   14, 8, 26, 17, 11, 20, 2]

def rankOfOrbitIndex (j : Nat) : Nat :=
  1 + (realIncreasingIndices.takeWhile (fun i => i != j)).length

def realRanks : List Nat :=
  (List.range 27).map (fun j => rankOfOrbitIndex ((j + 1) % 27))

def expectedRanks : List Nat :=
  [1, 27, 18, 9, 19, 10, 6, 22, 13,
   3, 25, 16, 7, 21, 12, 4, 24, 15,
   2, 26, 17, 8, 20, 11, 5, 23, 14]

theorem exact_vertex_order :
    realIncreasingIndices.length = 27 ∧
    realIncreasingIndices.Nodup ∧
    realIncreasingIndices.all (fun j => j < 27) = true := by
  decide +kernel

theorem twisted_cycle_closes :
    (iterateTwisted 28 (complement angleBits)).getLast? =
      some (complement angleBits) := by
  decide +kernel

theorem twisted_cycle_has_distinct_states :
    codedOrbit.length = 27 ∧ codedOrbit.Nodup := by
  decide +kernel

/-- Complete 27-state symbolic rank table agrees with independent
    strict real-orbit ordering, not just with one kneading prefix. -/
theorem all_27_ranks_agree :
    realRanks = expectedRanks ∧
    twistedRanks = expectedRanks := by
  decide +kernel

/-- If a 9-phase labeling factors through mod 3, every mod-3 fiber
    is necessarily constant. No geometric labeling is presumed. -/
theorem mod_three_fiber_indistinguishable
    {α : Type} (L : Nat → α)
    (g : Nat → α)
    (h : ∀ i : Nat, i < 9 → L i = g (i % 3)) :
    L 0 = L 3 := by
  calc
    L 0 = g (0 % 3) := h 0 (by omega)
    _ = g (3 % 3) := by rfl
    _ = L 3 := (h 3 (by omega)).symm

theorem distinct_markings_cannot_factor_through_mod_three
    {α : Type} (L : Nat → α)
    (hdistinct : L 0 ≠ L 3) :
    ¬ ∃ g : Nat → α, ∀ i : Nat, i < 9 →
      L i = g (i % 3) := by
  intro h
  obtain ⟨g, hg⟩ := h
  exact hdistinct (mod_three_fiber_indistinguishable L g hg)

#print axioms kneading_matches_twice_tuned_airplane
#print axioms all_27_ranks_agree
#print axioms distinct_markings_cannot_factor_through_mod_three

end LoopsFormal.Period27
