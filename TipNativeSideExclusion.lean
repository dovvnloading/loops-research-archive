import TipRootedNativeKL

/-!
Exact finite angle layer for a first failure at genuine *remaining* KL
G-stage W ideal J-sides. These are NOT the open central gluing seams.
Only arithmetic and authentic ray label equalities are kernel-checked.
The analytic landing and target-exclusion argument is in the manuscript.
-/

namespace LoopsFormal.TipNativeSideExclusion

open LoopsFormal.TipRootedNativeKL

/-- Previously certified rays at physical 0, numerators over 112. -/
def criticalAtZero : List Nat := [25, 31, 81, 87]

/-- Finite source authentication, rather than inventing a new ray cohort. -/
theorem authentic_K3_critical_quartet :
    coarse ⟨0, by decide⟩ ⟨1, by decide⟩ = 25 ∧
    coarse ⟨1, by decide⟩ ⟨0, by decide⟩ = 31 ∧
    coarse ⟨2, by decide⟩ ⟨1, by decide⟩ = 81 ∧
    coarse ⟨3, by decide⟩ ⟨0, by decide⟩ = 87 := by
  decide +kernel

/-- Each marked G-doubling is modulo one; all four critical rays
    collapse to the two angles 25/56 and 31/56 at x3=G(0). -/
theorem critical_value_ray_doubling :
    (2 * 25) % 112 = 50 ∧ (2 * 31) % 112 = 62 ∧
    (2 * 81) % 112 = 50 ∧ (2 * 87) % 112 = 62 := by
  decide +kernel

/-- The x3 pair doubles to 3/28 and 25/28 at x6=G²(0). -/
theorem second_critical_value_ray_doubling :
    (2 * 50) % 112 = 100 ∧ (2 * 62) % 112 = 12 := by
  decide +kernel

/-- The two x6 access angles are strictly inside the opposite original
    source KL J-side half-lines (not source vertices or W gluing seams). -/
theorem x6_rays_strictly_in_both_original_side_tails :
    ∀ i : Fin 4,
      3 * 192 < 28 * lower i ∧
      28 * upper i < 25 * 192 := by
  decide +kernel

/-- The original x3 ray at 25/56 is strictly outside every W seam:
    right of W tiles 0,1 and left of W tiles 2,3. -/
theorem x3_ray_strict_original_side_classification :
    ∀ i : Fin 4,
      (i.val < 2 → 56 * upper i < 25 * 192) ∧
      (2 ≤ i.val → 25 * 192 < 56 * lower i) := by
  decide +kernel

/-- The G dividing fixed-point rays at 1/3 and 2/3 are also finite
    ORIGINAL J-side points, not W gluing-seam points. Unlike x3/x6,
    the fixed point itself lies in the fine exterior Omega9. -/
theorem dividing_fixed_ray_strict_source_side_classification :
    ∀ i : Fin 4,
      (i.val < 2 → 3 * upper i < 192) ∧
      (2 ≤ i.val → 192 < 3 * lower i) := by
  decide +kernel

/-- Every original W seam sits strictly inside a period-one angle interval.
    Consequently any theta with 0<theta<1 has all theta+n, n<=-1 in xi
    and theta+n, n>=1 in eta, for all original W tiles. -/
theorem all_seams_in_open_unit_angle :
    ∀ i : Fin 4,
      0 < lower i ∧ lower i < upper i ∧ upper i < 192 := by
  decide +kernel

/-- The physical postcritical angle labels are distinct within each pair. -/
theorem four_postcritical_angles_are_distinct :
    ([50, 62, 12, 100] : List Nat).Nodup := by
  decide +kernel

#print axioms authentic_K3_critical_quartet
#print axioms critical_value_ray_doubling
#print axioms second_critical_value_ray_doubling
#print axioms x6_rays_strictly_in_both_original_side_tails
#print axioms x3_ray_strict_original_side_classification
#print axioms dividing_fixed_ray_strict_source_side_classification
#print axioms all_seams_in_open_unit_angle
#print axioms four_postcritical_angles_are_distinct

end LoopsFormal.TipNativeSideExclusion
