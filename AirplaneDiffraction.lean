import Period27Kneading
import TipRayPortrait

/-!
# Airplane diffraction and the two portrait diagnostics

The factor identity works over any commutative ring in Lean's core ring
hierarchy. The remaining certificates use the period-27 word and the
period-nine portrait already present in the archive. The extremal upper
bound, classification of arbitrary competitors, and ray landing use the
separate written proofs.
-/

namespace LoopsFormal.AirplaneDiffraction

/-- The middle sign of the factor is positive exactly for the plus choice. -/
def factor {R : Type} [Lean.Grind.CommRing R] (plus : Bool) (x : R) : R :=
  1 + (if plus then x else -x) - x^2

/-- Clearing the denominator in the reciprocal product gives this polynomial.
    Thus a reversal gives the same autocorrelation after substituting any scale. -/
theorem factor_times_reciprocal {R : Type} [Lean.Grind.CommRing R]
    (plus : Bool) (x : R) :
    factor plus x * (x^2 + (if plus then x else -x) - 1) =
      -(x^4) + 3 * x^2 - 1 := by
  cases plus <;> simp [factor] <;> grind

/-- Bits in coefficient order, false for +1. The scale tag preserves or
    complements the middle copy. The last copy is always complemented. -/
def extend (plus : Bool) (w : List Bool) : List Bool :=
  w ++ (if plus then w else Period27.complement w) ++ Period27.complement w

def words27 : List (List Bool) :=
  [false, true].flatMap fun fine =>
    [false, true].flatMap fun middle =>
      [false, true].map fun coarse =>
        extend coarse (extend middle (extend fine [false]))

theorem archive_angle_is_first : words27.head? = some Period27.angleBits := by
  decide +kernel

theorem eight_numerators :
    words27.map Period27.binaryValue =
      [59914011, 59885851, 57820963, 57784611, 31134601, 30993801, 20669361, 20487601] := by
  decide +kernel

/-- Aperiodic correlation at a nonnegative lag, truncating to overlapping sites. -/
def correlationAt (w : List Bool) (lag : Nat) : Int :=
  (List.zipWith (fun a b => if a == b then (1 : Int) else -1) w (w.drop lag)).sum

def correlation (w : List Bool) : List Int :=
  (List.range w.length).map (correlationAt w)

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

theorem eight_equal_full_correlations :
    words27.all (fun w => correlation w == correlation Period27.angleBits) = true := by
  decide +kernel

/-- Kneading at mark j+1 compares the ordinary doubled representative of
    D^j(angle) with the two endpoint numerators, before reducing again. -/
def mark (a j : Nat) : Option Bool :=
  let q := Period27.angleDenominator
  let step := 2 * ((2^j * a) % q)
  if step = a ∨ step = q + a then none else some (decide (a < step ∧ step < q + a))

/-- Zero-based iterates 1, 5, 17 are one-based marks 2, 6, 18. -/
theorem three_marks_separate_eight :
    ((words27.map Period27.binaryValue).map (fun a => [mark a 1, mark a 5, mark a 17])).Nodup := by
  decide +kernel

theorem airplane_rabbit_kneading_difference :
    (List.range 27).filter (fun j => mark Period27.angleNumerator j != mark 59885851 j) = [17] := by
  decide +kernel

def firstGapHit (a : Nat) : Option Nat :=
  ((List.range 27).map (fun i => i + 1)).find? fun i =>
    let d := (2^i * a) % Period27.angleDenominator
    decide (a < d ∧ d < Period27.angleDenominator - a)

theorem period_first_hits :
    (words27.map Period27.binaryValue).map firstGapHit =
      [none, some 9, some 3, some 3, some 1, some 1, some 1, some 1] := by
  decide +kernel

/-- The eighteen endpoints are computed from the archive's two labelled
    dynamical rays at each phase, retaining their coordinates on the 511-grid. -/
def portraitSites : List Nat :=
  (List.finRange 9).flatMap fun i =>
    [(TipRayPortrait.tailRay i 0).val, (TipRayPortrait.tailRay i 1).val]

def gapCount (sites : List Nat) (gap : Nat) : Nat :=
  (sites.filter fun x => sites.contains ((x + gap) % 511)).length

/-- Among all single deletions after adjoining the origin, these two
    multiplicities select the original portrait. The classification of all
    support-compatible competitors is a separate result in the geometry note. -/
theorem two_gaps_select_original :
    ((0 :: portraitSites).filter fun omitted =>
      let remaining := (0 :: portraitSites).erase omitted
      gapCount remaining 55 == 3 && gapCount remaining 57 == 3) = [0] := by
  decide +kernel

end LoopsFormal.AirplaneDiffraction
