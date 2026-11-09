import TipNativeRootDeck

/-!
Four original KL W native tiles and their exact source W->V0 routing.
Only finite source-angle inequalities and the integer potential/cocycle are
formalized. The physical G external-ray Jordan-wake separation, source
holomorphic naturality and root convergence are written mathematical inputs.
The table is not a claimed formalization of prime ends or actual loops.
-/
namespace LoopsFormal.TipNativeC4Wake

open LoopsFormal.TipRootedNativeKL

/-- Actual partner W tile within the very same original V0 parent. -/
def mate (i : Fin 4) : Fin 4 :=
  if i.val = 0 then ⟨1, by decide⟩
  else if i.val = 1 then ⟨0, by decide⟩
  else if i.val = 2 then ⟨3, by decide⟩
  else ⟨2, by decide⟩

/-- The source-certified two-to-one W->V0 routing. -/
theorem original_same_parent_mates :
    ∀ i : Fin 4,
      mate i ≠ i ∧ parentTile (mate i) = parentTile i := by
  decide +kernel

/-- On each original W gluing seam, the *other* same-parent tile has
a genuine finite remaining xi-ideal J-side point at exactly the same
unwrapped angle for tiles 0,2, or eta for tiles 1,3. -/
theorem exact_strict_same_parent_Jside_brackets :
    ∀ i : Fin 4, ∀ e : Fin 2,
      (i.val % 2 = 0 →
        coarse i e * 192 < lower (mate i) * 112) ∧
      (i.val % 2 = 1 →
        upper (mate i) * 112 < coarse i e * 192) := by
  decide +kernel

/-- The entire original open own-seam interval lies strictly on the mate's
remaining J-side (xi for even source indices, eta for odd), not just the
eight finite authenticated ray angles. -/
theorem whole_open_source_seam_in_mate_Jside :
    ∀ i : Fin 4,
      (i.val % 2 = 0 → upper i < lower (mate i)) ∧
      (i.val % 2 = 1 → upper (mate i) < lower i) := by
  decide +kernel

/-- Source C4 Jordan-wake physical right/left charges are documented
separately: the finite kernel checks the exact integer C4 cocycle. -/
def wakeRightCharge (i : Fin 4) : Int :=
  if i.val = 1 then 1 else 0

def wakeLeftCharge (i : Fin 4) : Int :=
  if i.val = 3 then 1 else 0

def transversePotential (i : Fin 4) : Int :=
  Int.ofNat (parentTile i)

/-- Four genuine W ray-pair edge labels give an exact closed C4 cocycle
provided the analytic wake-to-physical-winding identification in the note. -/
theorem c4_wake_charge_is_parent_difference :
    ∀ i : Fin 4,
      wakeRightCharge i - wakeLeftCharge i =
        transversePotential (nextTile i) - transversePotential i := by
  decide +kernel

/-- For every original W ray and target tile, the source-computed
transverse obstruction is zero exactly in the same-parent cases. -/
theorem transverse_zero_iff_source_parent_same (i j : Fin 4) :
    (transversePotential j - transversePotential i = 0) ↔
      parentTile i = parentTile j := by
  dsimp [transversePotential]
  omega

/-- Native KL coarse winding n adds to both excluded fine phase
charges. No integer n can erase a nonzero transverse obstruction. -/
theorem no_native_winding_repairs_cross_parent
    (i j : Fin 4) (n : Int)
    (h : parentTile i ≠ parentTile j) :
    ((transversePotential j + n) - (transversePotential i + n)) ≠ 0 := by
  intro hz
  have eq : transversePotential j = transversePotential i := by omega
  have same : parentTile i = parentTile j :=
    (transverse_zero_iff_source_parent_same i j).mp (by omega)
  exact h same

/-- Every authenticated own-seam root ray has one source-mate
finite J-side candidate in the same parent, not a synthetic fifth tile. -/
theorem eight_exact_source_mate_root_angle_candidates :
    ∀ i : Fin 4, ∀ e : Fin 2,
      parentTile (mate i) = parentTile i ∧
      ((i.val % 2 = 0 ∧
        coarse i e * 192 < lower (mate i) * 112) ∨
       (i.val % 2 = 1 ∧
        upper (mate i) * 112 < coarse i e * 192)) := by
  decide +kernel

#print axioms original_same_parent_mates
#print axioms exact_strict_same_parent_Jside_brackets
#print axioms whole_open_source_seam_in_mate_Jside
#print axioms c4_wake_charge_is_parent_difference
#print axioms transverse_zero_iff_source_parent_same
#print axioms no_native_winding_repairs_cross_parent
#print axioms eight_exact_source_mate_root_angle_candidates

end LoopsFormal.TipNativeC4Wake
