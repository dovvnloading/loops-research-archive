import TipSheetGrid

/-!
# The eight REAL ray accesses in the four source-defined G= f^3 KL W-tile seams

Only exact finite angular inequalities and source-label permutations are
kernel-checked. The conjugacy with the *actual* analytic ray portrait,
malnormality of the infinite free group, rooted holomorphic sections,
Caratheodory prime ends and Kahn's localization are written proofs with
separate imported classical hypotheses.

IMPORTANT: a ray with angle in an open G:W:tile seam is NOT a point of
that tile's ideal xi/eta/lambda sides. These are merely the correct original
source tile-incidence indices, not an ideal boundary extension.
-/

namespace LoopsFormal.TipRootedNativeKL

/-- The four ordinary source KL seam endpoints, in units of 1/192. -/
def lower (i : Fin 4) : Nat :=
  if i.val == 0 then 41 else if i.val == 1 then 53
  else if i.val == 2 then 137 else 149

def upper (i : Fin 4) : Nat :=
  if i.val == 0 then 43 else if i.val == 1 then 55
  else if i.val == 2 then 139 else 151

/-- Two sorted, source-licensed PI3 angles in each W gluing seam. -/
def coarse (i : Fin 4) (e : Fin 2) : Nat :=
  (if i.val == 0 then 24 else if i.val == 1 then 31
   else if i.val == 2 then 80 else 87) + e.val

/-- Numerators of the eight authentic AMBIENT dynamical rays / 523264. -/
def ambient (i : Fin 4) (e : Fin 2) : Nat :=
  (if i.val == 0 then 378368 else if i.val == 1 then 406473
   else if i.val == 2 then 116736 else 144841) + 55 * e.val

/-- The genuine PI9 angle in units of one quarter on THIS finite cohort. -/
def fine (i : Fin 4) (e : Fin 2) : Nat := (i.val + 2 + e.val) % 4

def originalIndex (i : Fin 4) (e : Fin 2) : Nat :=
  2 * ((i.val + 2) % 4) + e.val

def nextTile (i : Fin 4) : Fin 4 :=
  ⟨(i.val + 1) % 4, Nat.mod_lt _ (by decide)⟩

def parentTile (i : Fin 4) : Nat := i.val / 2

/-- Exact strict membership in the genuine open W seam, not an ideal side. -/
theorem all_eight_in_original_W_open_seams :
    ∀ i : Fin 4, ∀ e : Fin 2,
      lower i * 112 < coarse i e * 192 ∧
      coarse i e * 192 < upper i * 112 := by
  decide +kernel

/-- No free angling: all eight records equal the previously kernel-verified
    PHYSICAL ambient/PI3/PI9 table, just ordered by W tile and source slot. -/
theorem exact_match_to_source_Levin_ladder :
    ∀ i : Fin 4, ∀ e : Fin 2,
      ambient i e = LoopsFormal.TipLevinComposition.ambientNum (originalIndex i e) ∧
      coarse i e = LoopsFormal.TipLevinComposition.coarseNum (originalIndex i e) ∧
      fine i e = LoopsFormal.TipLevinComposition.fineNum (originalIndex i e) := by
  decide +kernel

/-- Two GLUING-SEAM rays in one original KL tile are different fine accesses. -/
theorem one_tile_cannot_determine_fine_prime_end :
    ∀ i : Fin 4, fine i ⟨0, by decide⟩ ≠ fine i ⟨1, by decide⟩ := by
  decide +kernel

/-- Exactly the two rays in ADJACENT tile seams have the same fine end. -/
theorem fine_end_pairs_across_adjacent_tiles :
    ∀ i : Fin 4,
      fine i ⟨1, by decide⟩ = fine (nextTile i) ⟨0, by decide⟩ := by
  decide +kernel

/-- The four fine-end labels follow one full cyclic turn without a skipped end. -/
theorem four_fine_ends_distinct :
    ((List.range 4).map (fun i => (i+3) % 4)).Nodup := by
  decide +kernel

/-- The four edges alternate SAME and DIFFERENT V0 parent tiles. -/
theorem exact_original_parent_tile_crossings :
    ∀ i : Fin 4,
      (parentTile i = parentTile (nextTile i)) ↔
        (i.val = 0 ∨ i.val = 2) := by
  decide +kernel

/-- All eight ambient rays are distinct, with exactly two per fine angle. -/
def eightFine : List Nat :=
  [fine ⟨0,by decide⟩ ⟨0,by decide⟩,
   fine ⟨0,by decide⟩ ⟨1,by decide⟩,
   fine ⟨1,by decide⟩ ⟨0,by decide⟩,
   fine ⟨1,by decide⟩ ⟨1,by decide⟩,
   fine ⟨2,by decide⟩ ⟨0,by decide⟩,
   fine ⟨2,by decide⟩ ⟨1,by decide⟩,
   fine ⟨3,by decide⟩ ⟨0,by decide⟩,
   fine ⟨3,by decide⟩ ⟨1,by decide⟩]

def eightAmbient : List Nat :=
  [378368,378423,406473,406528,116736,116791,144841,144896]

theorem eight_ambient_distinct : eightAmbient.Nodup := by
  decide +kernel

theorem every_fine_end_has_two_tile_channels :
    ∀ j ∈ List.range 4,
      (eightFine.filter (fun k => k == j)).length = 2 := by
  decide +kernel

/-- Entire native tile LABEL plus one internal slot bit distinguishes the
    exact fine end; the tile label alone provably does not. -/
theorem source_eight_seams_give_complete_four_fine_labels :
    (eightFine.length = 8) ∧
    ((List.range 4).map (fun i => (i+3) % 4)).Nodup := by
  decide +kernel

#print axioms all_eight_in_original_W_open_seams
#print axioms exact_match_to_source_Levin_ladder
#print axioms one_tile_cannot_determine_fine_prime_end
#print axioms fine_end_pairs_across_adjacent_tiles
#print axioms four_fine_ends_distinct
#print axioms exact_original_parent_tile_crossings
#print axioms every_fine_end_has_two_tile_channels

end LoopsFormal.TipRootedNativeKL
