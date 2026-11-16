import Std

/-!
Finite labeled model only. This file does not prove a quadratic parameter exists
for all p, any analytic Rouché bound, KKL prime-end identifications or widths.
Unlike a sentence in the earlier note, avoiding arcs have SEVEN source labels.
-/
namespace RealPrimitiveTipUnconditionalDiscrete

/-- The shorter cyclic route, including both endpoint labels. -/
def shortArc (n a b : Nat) : List Nat := Id.run do
  let f := (b + n - a) % n
  let r := (a + n - b) % n
  let start := if f < r then a else b
  let length := min f r
  return (List.range (length + 1)).map (fun i => (start + i) % n)

theorem source_crossing_1 : shortArc 20 3 1 = [1, 2, 3] := by decide
theorem source_crossing_2 : shortArc 20 19 17 = [17, 18, 19] := by decide
theorem source_avoiding : shortArc 20 3 17 = [17, 18, 19, 0, 1, 2, 3] := by decide
theorem target_crossing_1 : shortArc 10 3 1 = [1, 2, 3] := by decide
theorem target_crossing_2 : shortArc 10 9 7 = [7, 8, 9] := by decide
theorem target_avoiding : shortArc 10 3 7 = [3, 4, 5, 6, 7] := by decide

def covering (s : Nat) : Nat := s % 10
theorem two_preimages_each :
    ∀ t : Fin 10,
      ((List.range 20).filter (fun s => covering s == t.val)).length = 2 := by
  decide

def cutImage : List Nat := [2, 4, 4, 3, 0]
def edgePairs : List (Nat × Nat) := [(0, 1), (2, 3), (3, 4)]
def edgeHit (i j : Nat) : Nat :=
  let a := edgePairs[i]!
  let b := edgePairs[j]!
  let l := min (cutImage[a.1]!) (cutImage[a.2]!)
  let r := max (cutImage[a.1]!) (cutImage[a.2]!)
  if decide (l ≤ b.1 ∧ b.2 ≤ r) then 1 else 0
def edgeMatrix : List (List Nat) :=
  (List.range 3).map (fun j => (List.range 3).map (fun i => edgeHit i j))
theorem old_edge_occurrences :
    edgeMatrix = [[0, 0, 1], [1, 0, 1], [1, 1, 0]] := by decide

/-- Immersion blocks, as distinct from cover fibers. -/
def immersion : List Nat :=
  [0,0,0,1,1,2,3,4,4,4,5,6,6,6,7,8,9,9,0,0]
def blocks : List (List Nat) :=
  [[18,19,0,1,2],[3,4],[5],[6],[7,8,9],[10],[11,12,13],[14],[15],[16,17]]
theorem immersion_partition :
    blocks.flatten.length = 20 ∧ blocks.flatten.Nodup ∧
    blocks.map List.length = [5,2,1,1,3,1,3,1,1,2] := by decide
theorem immersion_labels :
    ∀ t : Fin 10,
      (blocks[t.val]!).all (fun s => immersion[s]! == t.val) = true := by decide

def zeroEdgeAtoms : List Nat := [0,2,5,8]
theorem crests_zero_edge :
    zeroEdgeAtoms.contains 0 = true ∧ zeroEdgeAtoms.contains 2 = true ∧
    zeroEdgeAtoms.contains 8 = true := by decide

/-- A symbolic reciprocal-width coefficient identity, not KKL analysis. -/
theorem harmonic_coefficients : (2 : Nat) = 1 + 1 := by decide

end RealPrimitiveTipUnconditionalDiscrete
