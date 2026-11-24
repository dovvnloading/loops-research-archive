import TipKKLTreeMarking

/-!
Finite ordered-cut certificate for the selected slit pair, PR #118.

The inputs are the rank order O2 and the two cut lists in the companion
`research/independent_audits/immersion_mark_resolution_20261124/NOTE.md`.
The block ownership is derived from those ranks and checked against the
existing finite table. The endpoint-aware action below retains a punctured
circle when an open lifted interval has length exactly ten; seeing every
atom label does not by itself mean the whole circle has been reached.

This module proves only finite contour bookkeeping. It does not formalize
prime ends, proper paths, homotopies, the meaning of KKL A.3.2, or the
identification of the contour operation with an immersion pullback.
-/

namespace LoopsFormal.ImmersionMarkFinite

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- Ranks in O2: -y1, -y4, y2, y5, -a, y3, y6, a, -y5, -y2, y4, y1.
Only their order matters; these integers are not geometric coordinates. -/
def sourceCutRanks : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
def targetCutRanks : List Nat := [3, 5, 6, 7, 10]

/-- Left real endpoint of an upper source atom, with rank zero at the tip. -/
def sourceLeftRank (s : Nat) : Nat :=
  if s = 0 then 0 else sourceCutRanks[s - 1]!

/-- Number of target cuts passed on the upper bank. -/
def upperOwner (s : Nat) : Nat :=
  (targetCutRanks.filter fun r => decide (r ≤ sourceLeftRank s)).length

/-- Upper bank followed by the lower bank in reverse real order. -/
def owner (s : Nat) : Nat :=
  if s ≤ 10 then upperOwner s else (10 - upperOwner (20 - s)) % 10

/-- Start on the lower bank just after the first target cut. -/
def tipBlockStart : Nat :=
  2 * sourceCutRanks.length -
    (sourceCutRanks.filter fun r => decide (r < targetCutRanks.head!)).length

/-- Begin the cyclic source traversal at the cut-derived start of the tip block. -/
def sourceTraversal : List Nat :=
  (List.range 20).map fun s => (s + tipBlockStart) % 20

def block (i : Nat) : List Nat := sourceTraversal.filter fun s => owner s == i
def blocks : List (List Nat) := (List.range 10).map block

theorem target_cuts_are_source_cuts :
    targetCutRanks.all (fun r => sourceCutRanks.contains r) = true := by
  decide +kernel

/-- The cut-derived blocks coincide with the earlier finite certificate. -/
theorem cut_derived_blocks_match_archive :
    blocks = TipKKLTreeMarking.pullbackBlocks := by
  decide +kernel

theorem cut_derived_owners_match_archive :
    ∀ s : Fin 20, owner s.val = TipKKLTreeMarking.inclusionLabel s.val := by
  decide +kernel

theorem cut_derived_partition :
    blocks.flatten.length = 20 ∧ blocks.flatten.Nodup ∧
      blocks.map List.length = [5, 2, 1, 1, 3, 1, 3, 1, 1, 2] := by
  decide +kernel

/-- Source atom interiors reaching strictly to the left of the target tip.
The target tip has rank two in O2. -/
def attachmentAtoms : List Nat :=
  (List.range 20).filter fun s =>
    decide (sourceLeftRank (if s ≤ 10 then s else 20 - s) < 2)

theorem cut_derived_attachment_atoms : attachmentAtoms = [0, 1, 19] := by
  decide +kernel

theorem cut_derived_end_proper_finite_predicate :
    blocks.all (fun b =>
      !(attachmentAtoms.contains b.head!) &&
      !(attachmentAtoms.contains b.getLast!)) = true := by
  decide +kernel

/-- Covering push-forward uses source label modulo ten, consuming the
analytic alignment in IDEAL_BOUNDARY.md (9), not deducing it from cut ranks. -/
def imageTable : List (List Nat) := blocks.map fun b => b.map fun s => s % 10

theorem cut_derived_contour_image_table :
    imageTable = [[8, 9, 0, 1, 2], [3, 4], [5], [6], [7, 8, 9], [0],
      [1, 2, 3], [4], [5], [6, 7]] := by
  decide +kernel

/-- A nonnegative representative of the cut lift; it is verify.py's CUT_LIFT + 20.
The shift by two full target turns leaves the circle map unchanged. -/
def baseLift (k : Nat) : Nat :=
  tipBlockStart + ((blocks.take k).map List.length).foldl Nat.add 0

def liftedCut (k : Nat) : Nat := baseLift (k % 10) + 20 * (k / 10)

theorem cut_derived_lift :
    (List.range 11).map baseLift = [18, 23, 25, 26, 27, 30, 31, 34, 35, 36, 38] ∧
      baseLift 10 = baseLift 0 + 20 := by
  decide +kernel

/-- An open arc represented by its left cut and positive lifted length.
Length ten is a punctured circle. `none` below denotes the full circle. -/
structure OpenArc where
  left : Nat
  length : Nat
deriving DecidableEq, Repr

def advance : Option OpenArc → Option OpenArc
  | none => none
  | some arc =>
      let a := liftedCut arc.left
      let b := liftedCut (arc.left + arc.length)
      let width := b - a
      if 10 < width then none else some ⟨a % 10, width⟩

def iterate : Nat → Option OpenArc → Option OpenArc
  | 0, arc => arc
  | n + 1, arc => iterate n (advance arc)

/-- All ninety proper open runs of marked atoms reach the entire circle. -/
theorem all_ninety_open_runs_saturate_within_five :
    ∀ start : Fin 10, ∀ len : Fin 9,
      iterate 5 (some ⟨start.val, len.val + 1⟩) = none := by
  decide +kernel

/-- Five is necessary, including the actual omitted endpoint state. -/
theorem five_steps_are_sharp :
    iterate 4 (some ⟨3, 1⟩) ≠ none ∧ iterate 5 (some ⟨3, 1⟩) = none := by
  decide +kernel

/-- These four images meet every atom but omit one endpoint. -/
theorem full_atom_support_can_be_a_punctured_circle :
    advance (some ⟨2, 6⟩) = some ⟨5, 10⟩ ∧
    advance (some ⟨3, 6⟩) = some ⟨6, 10⟩ ∧
    advance (some ⟨8, 4⟩) = some ⟨5, 10⟩ ∧
    advance (some ⟨9, 4⟩) = some ⟨6, 10⟩ := by
  decide +kernel

theorem punctured_circles_saturate_on_the_next_step :
    ∀ start : Fin 10, advance (some ⟨start.val, 10⟩) = none := by
  decide +kernel

#print axioms target_cuts_are_source_cuts
#print axioms cut_derived_blocks_match_archive
#print axioms cut_derived_owners_match_archive
#print axioms cut_derived_partition
#print axioms cut_derived_attachment_atoms
#print axioms cut_derived_end_proper_finite_predicate
#print axioms cut_derived_contour_image_table
#print axioms cut_derived_lift
#print axioms all_ninety_open_runs_saturate_within_five
#print axioms five_steps_are_sharp
#print axioms full_atom_support_can_be_a_punctured_circle
#print axioms punctured_circles_saturate_on_the_next_step

end LoopsFormal.ImmersionMarkFinite
