import TipNativeFullBoundaryTypes

/-!
Finite layer for the actual KKL tree-complement marking of physical G=f^3.
The companion Python certificate derives the finite tables from exact real
orbit/phase geometry. This file checks their cyclic partition, refinement,
end-atom and marked-path filter consequences. It does NOT formalize the
complex quadratic-like representative, prime ends, KKL Proposition 6.5,
extremal width, or the homotopy/breakage theorem.
-/

namespace LoopsFormal.TipKKLTreeMarking

def pullbackLabels : List Nat :=
  [0,0,0,1,1,2,3,4,4,4,5,6,6,6,7,8,9,9,0,0]

def inclusionLabel (s : Nat) : Nat := pullbackLabels[s]!
def coveringLabel (s : Nat) : Nat := s % 10

def pullbackBlocks : List (List Nat) :=
  [[18,19,0,1,2], [3,4], [5], [6], [7,8,9], [10],
   [11,12,13], [14], [15], [16,17]]

def attachmentAtoms : List Nat := [19,0,1]

def blockEnds : List (Nat × Nat) :=
  [(18,2),(3,4),(5,5),(6,6),(7,9),(10,10),
   (11,13),(14,14),(15,15),(16,17)]

def cyclicSpan (n a b : Nat) : Nat :=
  1 + min ((b+n-a) % n) ((a+n-b) % n)

/-- All twenty source atoms occur once in the ten native pullback blocks. -/
theorem inner_pullback_partition :
    pullbackBlocks.flatten.length = 20 ∧
    pullbackBlocks.flatten.Nodup ∧
    pullbackBlocks.map List.length = [5,2,1,1,3,1,3,1,1,2] := by
  decide +kernel

/-- Every source covering-marking atom has the correct pullback host. -/
theorem refinement_block_labels :
    ∀ i : Fin 10,
      (pullbackBlocks[i.val]!).all (fun s => inclusionLabel s == i.val) = true := by
  decide +kernel

/-- Degree two on the ideal marking, not degree eight of the global f^3. -/
theorem two_source_atoms_over_each_target_atom :
    ∀ i : Fin 10,
      ((List.range 20).filter (fun s => coveringLabel s == i.val)).length = 2 := by
  decide +kernel

/-- The source attachment atoms are internal, never end-atoms of a block. -/
theorem all_inner_blocks_end_proper_finite_predicate :
    blockEnds.all (fun p =>
      !(attachmentAtoms.contains p.1) && !(attachmentAtoms.contains p.2)) = true := by
  decide +kernel

/-- Only pullback block zero contains newly attached inner boundary atoms. -/
theorem one_attachment_host_block :
    ∀ i : Fin 10,
      ((pullbackBlocks[i.val]!).any (fun s => attachmentAtoms.contains s) = true)
        ↔ i.val = 0 := by
  decide +kernel

/-- Target and both crossing source pieces avoid KKL A.1's <=2 filter. -/
theorem crossing_path_source_and_target_spans :
    cyclicSpan 10 1 9 = 3 ∧
    cyclicSpan 20 3 1 = 3 ∧
    cyclicSpan 20 19 17 = 3 := by
  decide +kernel

/-- Both actual crossing pieces have endpoints in different pullback cells. -/
theorem both_crossing_pieces_escape_single_interval_filter :
    (inclusionLabel 3, inclusionLabel 1) = (1,0) ∧
    (inclusionLabel 19, inclusionLabel 17) = (0,9) := by
  decide +kernel

/-- The two marked dynamical images are different non-short atom pairs. -/
theorem two_distinct_marked_pushforward_pairs :
    (coveringLabel 3, coveringLabel 1) = (3,1) ∧
    (coveringLabel 19, coveringLabel 17) = (9,7) ∧
    cyclicSpan 10 3 1 = 3 ∧ cyclicSpan 10 9 7 = 3 := by
  decide +kernel

/-- The avoiding representative survives both source filters and its push. -/
theorem avoiding_path_marked_filter_data :
    cyclicSpan 20 3 17 = 7 ∧
    (inclusionLabel 3, inclusionLabel 17) = (1,9) ∧
    (coveringLabel 3, coveringLabel 17) = (3,7) ∧
    cyclicSpan 10 3 7 = 5 := by
  decide +kernel

/-- Deliberate negative controls: adjacency and one coarse cell are distinct. -/
theorem source_filter_negative_controls :
    cyclicSpan 20 1 2 = 2 ∧ inclusionLabel 1 = inclusionLabel 2 := by
  decide +kernel

#print axioms inner_pullback_partition
#print axioms refinement_block_labels
#print axioms all_inner_blocks_end_proper_finite_predicate
#print axioms both_crossing_pieces_escape_single_interval_filter
#print axioms two_distinct_marked_pushforward_pairs
#print axioms avoiding_path_marked_filter_data

end LoopsFormal.TipKKLTreeMarking
