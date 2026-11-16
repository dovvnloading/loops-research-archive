import Std

/-!
A purely *finite* checker for the slit marking after the analytic
three-return and Caratheodory hypotheses have been discharged in NOTE.md.
These definitions are just integer labels.  They do not model
holomorphic dynamics, a Julia set, prime ends, or extremal widths.
-/
namespace RealPrimitiveTipPrimeEndDiscrete

def targetCutImages : List Nat := [2, 4, 4, 3, 0]
def oldEdges : List (Nat × Nat) := [(0, 1), (2, 3), (3, 4)]
def edgeHit (input output : Nat × Nat) : Bool :=
  let a := min (targetCutImages[input.1]!) (targetCutImages[input.2]!)
  let b := max (targetCutImages[input.1]!) (targetCutImages[input.2]!)
  decide (a ≤ output.1 ∧ output.2 ≤ b)
def entry (row col : Nat) : Nat :=
  if edgeHit (oldEdges[col]!) (oldEdges[row]!) then 1 else 0
def edgeMatrix : List (List Nat) :=
  (List.range 3).map fun row => (List.range 3).map (entry row)
theorem three_old_edges_once :
    edgeMatrix = [[0, 0, 1], [1, 0, 1], [1, 1, 0]] := by decide

def cover (s : Nat) : Nat := s % 10

theorem each_target_has_two_cover_preimages :
    ∀ t : Fin 10,
      ((List.range 20).filter (fun s => cover s == t.val)).length = 2 := by
  decide

/-- KKL immersion *blocks*, NOT pointwise images of attached prime ends. -/
def immersionBlocks : List (List Nat) :=
  [[18, 19, 0, 1, 2], [3, 4], [5], [6], [7, 8, 9],
   [10], [11, 12, 13], [14], [15], [16, 17]]
def sourceLabels : List Nat :=
  [0, 0, 0, 1, 1, 2, 3, 4, 4, 4, 5, 6, 6, 6, 7, 8, 9, 9, 0, 0]
def attachedSource : List Nat := [19, 0, 1]

theorem blocks_partition_the_inner_source_circle :
    immersionBlocks.flatten.length = 20 ∧
    immersionBlocks.flatten.Nodup ∧
    immersionBlocks.map List.length = [5, 2, 1, 1, 3, 1, 3, 1, 1, 2] := by
  decide

theorem labels_equal_the_declared_blocks :
    ∀ t : Fin 10,
      (immersionBlocks[t.val]!).all
        (fun s => sourceLabels[s]! == t.val) = true := by
  decide

theorem unique_immersion_attachment_block :
    ∀ t : Fin 10,
      ((immersionBlocks[t.val]!).any
         (fun s => attachedSource.contains s) = true) ↔ t.val = 0 := by
  decide

/-- Inclusive number of atoms in the unique non-antipodal shorter cyclic arc. -/
def shortArcAtoms (n a b : Nat) : Nat :=
  min ((b + n - a) % n) ((a + n - b) % n) + 1

theorem filtered_two_crossing_one_avoiding :
    shortArcAtoms 20 3 1 = 3 ∧
    shortArcAtoms 20 19 17 = 3 ∧
    shortArcAtoms 20 3 17 = 7 := by decide

theorem cover_pushed_lengths_are_three_three_five :
    shortArcAtoms 10 (cover 3) (cover 1) = 3 ∧
    shortArcAtoms 10 (cover 19) (cover 17) = 3 ∧
    shortArcAtoms 10 (cover 3) (cover 17) = 5 := by decide

theorem different_immersion_blocks_at_filtered_ends :
    sourceLabels[3]! ≠ sourceLabels[1]! ∧
    sourceLabels[19]! ≠ sourceLabels[17]! ∧
    sourceLabels[3]! ≠ sourceLabels[17]! := by decide

end RealPrimitiveTipPrimeEndDiscrete
