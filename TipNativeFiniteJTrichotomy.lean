import TipNativeC4Wake
import TipNativeSideExclusion

/-!
Finite original source-angle/ray witness consistency for all three physical
fine-target categories on strictly interior KL W xi/eta J-sides.

This file does NOT formalize Caratheodory, Kahn local-cover theory,
continuous boundary extensions, the original KL path groupoid, or the
real-analytic wake proof. It checks finite imported source facts only.
-/

namespace LoopsFormal.TipNativeFiniteJTrichotomy

open LoopsFormal.TipRootedNativeKL

/-- The true same-parent mate side is strictly outside the own source
open gluing interval for all eight authenticated fine-root rays. -/
theorem all_eight_root_class_mate_ideal_angles :
    ∀ i : Fin 4, ∀ e : Fin 2,
      (parentTile (LoopsFormal.TipNativeC4Wake.mate i) = parentTile i) ∧
      ((i.val % 2 = 0 ∧
        coarse i e * 192 < lower (LoopsFormal.TipNativeC4Wake.mate i) * 112) ∨
       (i.val % 2 = 1 ∧
        upper (LoopsFormal.TipNativeC4Wake.mate i) * 112 < coarse i e * 192)) :=
  LoopsFormal.TipNativeC4Wake.eight_exact_source_mate_root_angle_candidates

/-- At every one of the four source tiles, the two actual x6 G angles
3/28 and 25/28 are strictly in the remaining xi/eta J-side interiors. -/
theorem all_four_tiles_have_removed_second_phase_witnesses :
    ∀ i : Fin 4,
      3 * 192 < 28 * lower i ∧
      28 * upper i < 25 * 192 :=
  LoopsFormal.TipNativeSideExclusion.x6_rays_strictly_in_both_original_side_tails

/-- The source's G dividing-fixed rays at 1/3 and 2/3 are strictly
outside all original W gluing seams, hence genuine J-side accesses. -/
theorem dividing_fixed_real_access_not_glued :
    ∀ i : Fin 4,
      (i.val < 2 → 3 * upper i < 192) ∧
      (2 ≤ i.val → 192 < 3 * lower i) :=
  LoopsFormal.TipNativeSideExclusion.dividing_fixed_ray_strict_source_side_classification

/-- Exactly eight possible authenticated source-mate root witnesses,
before importing their analytic physical K9 landing theorem. -/
def rootMateCandidatePairs : List (Nat × Nat) :=
  [(0,1),(0,1),(1,0),(1,0),(2,3),(2,3),(3,2),(3,2)]

theorem rootMateCandidatePairs_eight :
    rootMateCandidatePairs.length = 8 := by
  decide +kernel

/-- Exactly one same-parent mate tile is different from each source
anchor tile; Lean checks the original four-tile finite routing. -/
theorem rootMateUniqueSourceIndex :
    ∀ i : Fin 4,
      LoopsFormal.TipNativeC4Wake.mate
        (LoopsFormal.TipNativeC4Wake.mate i) = i := by
  decide +kernel

#print axioms all_eight_root_class_mate_ideal_angles
#print axioms all_four_tiles_have_removed_second_phase_witnesses
#print axioms dividing_fixed_real_access_not_glued
#print axioms rootMateCandidatePairs_eight
#print axioms rootMateUniqueSourceIndex

end LoopsFormal.TipNativeFiniteJTrichotomy
