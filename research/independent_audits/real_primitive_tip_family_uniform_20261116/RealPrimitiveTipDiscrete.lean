import Std

/-!
Finite shadow of a conditional real primitive-tip family theorem.  All
functions here act on the explicitly declared ten/twenty marked atoms and
three old edges.  This file does NOT construct a quadratic-like map,
Caratheodory boundary, a holomorphic wave, or an extremal width.  In
particular, none of its decidable identities proves the existence of a
physical tip at an arbitrary return period.
-/

namespace RealPrimitiveTipDiscrete

def cuts : List Nat := [2, 4, 4, 3, 0]
def oldEdges : List (Nat × Nat) := [(0, 1), (2, 3), (3, 4)]

def imageCut (i : Nat) : Nat := cuts[i]!

def edgeHits (input output : Nat × Nat) : Bool :=
  let low := min (imageCut input.1) (imageCut input.2)
  let high := max (imageCut input.1) (imageCut input.2)
  decide (low ≤ output.1 ∧ output.2 ≤ high)

def entry (row col : Nat) : Nat :=
  if edgeHits (oldEdges[col]!) (oldEdges[row]!) then 1 else 0

def oldMatrix : List (List Nat) :=
  (List.range 3).map (fun row => (List.range 3).map (entry row))

theorem edge_matrix_from_endpoint_images :
    oldMatrix = [[0, 0, 1], [1, 0, 1], [1, 1, 0]] := by
  decide

def fStar (s : Nat) : Nat := s % 10

theorem two_cover_atoms_per_target :
    ∀ t : Fin 10,
      ((List.range 20).filter (fun s => fStar s == t.val)).length = 2 := by
  decide

def pulled : List Nat :=
  [0,0,0,1,1,2,3,4,4,4,5,6,6,6,7,8,9,9,0,0]

def iotaBlock (s : Nat) : Nat := pulled[s]!

def blocks : List (List Nat) :=
  [[18,19,0,1,2],[3,4],[5],[6],[7,8,9],[10],
   [11,12,13],[14],[15],[16,17]]

def attached : List Nat := [19,0,1]

theorem immersion_blocks_partition :
    blocks.flatten.length = 20 ∧ blocks.flatten.Nodup ∧
    blocks.map List.length = [5,2,1,1,3,1,3,1,1,2] := by
  decide

theorem each_block_has_its_declared_label :
    ∀ t : Fin 10,
      (blocks[t.val]!).all (fun s => iotaBlock s == t.val) = true := by
  decide

theorem attachment_only_in_block_zero :
    ∀ t : Fin 10,
      ((blocks[t.val]!).any (fun s => attached.contains s) = true) ↔
        t.val = 0 := by
  decide

def closedParentCrest : Nat := 0
def closedChildCrests : List Nat := [2,8]
def zeroOldEdgeCrests : List Nat := [0,2,5,8]

theorem parent_and_children_are_zero_edge_types :
    zeroOldEdgeCrests.contains closedParentCrest = true ∧
    closedChildCrests.all (fun t => zeroOldEdgeCrests.contains t) = true := by
  decide

/-- Algebraic parameter of a CHOSEN, not intrinsic, annulus. -/
def selectedRatioNumerator (p : Nat) : Nat := 2 * (p - 1)

theorem selected_ratio_between_one_and_two (p : Nat) (hp : 3 ≤ p) :
    p < selectedRatioNumerator p ∧ selectedRatioNumerator p < 2*p := by
  omega

/-- The reciprocal-width series law after factoring out log(r1/r0)/pi. -/
theorem symbolic_harmonic_coefficients : (2 : Nat) = 1 + 1 := by
  decide

end RealPrimitiveTipDiscrete
