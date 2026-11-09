import TipNativeFullBoundaryTypes

/-!
Original source G-stage W -> V0 KL Lemma 3.4 natural inclusion.

ONLY finite original seam inequalities, two genuine source channels per
V parent and universal-integer strict endpoint arithmetic are proved
in this Lean layer. The proper path / KKL A.3.2 pullback claim is
written mathematics citing the actual KL universal-tile gluing.
-/

namespace LoopsFormal.TipNativeProperRestriction

open LoopsFormal.TipRootedNativeKL

/-- True original V parent seam endpoints in units of 1/192:
(5,7)/24=(40,56)/192, (17,19)/24=(136,152)/192. -/
def VLower192 (i : Fin 4) : Nat :=
  if i.val < 2 then 40 else 136

def VUpper192 (i : Fin 4) : Nat :=
  if i.val < 2 then 56 else 152

/-- Exact strict containment of EACH original W child gluing interval in
the correct source V parent interval (not an invented collapsed tile). -/
theorem original_four_W_seams_strict_inside_original_V_parent :
    ∀ i : Fin 4,
      0 < VLower192 i ∧
      VLower192 i < lower i ∧
      lower i < upper i ∧
      upper i < VUpper192 i ∧
      VUpper192 i < 192 := by
  decide +kernel

/-- Genuine source J-side points STRICTLY inside the parent V gluing
interval exist on BOTH source xi and eta for every original W tile.
Their coordinates have denominators 384. -/
theorem every_W_original_J_side_has_nonproper_parent_interior_open_subarc :
    ∀ i : Fin 4,
      2 * VLower192 i < VLower192 i + lower i ∧
      VLower192 i + lower i < 2 * lower i ∧
      2 * upper i < upper i + VUpper192 i ∧
      upper i + VUpper192 i < 2 * VUpper192 i := by
  decide +kernel

/-- The literal original tile route j |-> j/2 has two distinct source
channels for EACH V parent p. -/
theorem original_two_distinct_W_tiles_per_V_parent :
   parentTile ⟨0, by decide⟩ = 0 ∧
   parentTile ⟨1, by decide⟩ = 0 ∧
   parentTile ⟨2, by decide⟩ = 1 ∧
   parentTile ⟨3, by decide⟩ = 1 := by
  decide +kernel

/-- For every integer path winding m>=0, the target proper path has
strictly J-side endpoints at unwrapped x=-m, x=m+1. The same endpoints
lie in both original source W sides. This is integer inequality only. -/
theorem all_integer_winding_source_and_target_endpoint_brackets
    (m : Nat) (i : Fin 4) :
      (-(Int.ofNat m) * 192 < (VLower192 i : Int)) ∧
      ((VUpper192 i : Int) < Int.ofNat (m+1) * 192) ∧
      (-(Int.ofNat m) * 192 < (lower i : Int)) ∧
      ((upper i : Int) < Int.ofNat (m+1) * 192) := by
  have h := original_four_W_seams_strict_inside_original_V_parent i
  omega

/-- The independent source KL 11/48 collision lies strictly in the
V0 gluing interval while outside W0 and W1 own gluing seams. -/
theorem actual_source_11_over_48_J_side_collision_brackets :
    upper ⟨0, by decide⟩ < 44 ∧
    44 < lower ⟨1, by decide⟩ ∧
    VLower192 ⟨0, by decide⟩ < 44 ∧
    44 < VUpper192 ⟨0, by decide⟩ := by
  decide +kernel

#print axioms original_four_W_seams_strict_inside_original_V_parent
#print axioms every_W_original_J_side_has_nonproper_parent_interior_open_subarc
#print axioms original_two_distinct_W_tiles_per_V_parent
#print axioms all_integer_winding_source_and_target_endpoint_brackets
#print axioms actual_source_11_over_48_J_side_collision_brackets

end LoopsFormal.TipNativeProperRestriction
