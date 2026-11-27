import ActualCrestSupport
import ThreeReturnParent

/-!
# The crest support belongs to the actual proper central return

The proper degree-two parent restriction is supplied by the archived
three-return construction. The new bridge identifies the entire crest
input disk with points of that same central component, for every return index
at least seventeen. Scaling gives inclusion in the literal physical
parent and in the archive's original return component. No equality of
these two components or prime-end marking is asserted.
-/

namespace ActualCrestProperReturn

open Set Function Filter
open scoped Topology
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn LimitingCrest
open LoopsLimitingCrestParameter QuadraticCrestDividedDifference ThreeReturnParent

noncomputable section

/-- Exact signed fibers of the already constructed proper parent exhaust
every inverse point in the control disk. -/
theorem actual_parent_exhaustion {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : ‖z‖ ≤ 23/20)
    (himage : ‖normalizedReturn c p z‖ < 23/20) :
    z ∈ parentSource c p := by
  have hparent := actual_parent_restriction hp hc
  have hmem : normalizedReturn c p z ∈ normalizedReturn c p '' parentSource c p := by
    rw [hparent.image_eq]
    simpa only [Metric.mem_ball, dist_zero_right] using himage
  obtain ⟨w,hw,hwe⟩ := hmem
  have hwn : ‖w‖ ≤ 23/20 := by
    have h := hparent.closure_inside (subset_closure hw)
    exact (show ‖w‖ < 23/20 by simpa using h).le
  have hband := parameter_band hp hc.1
  have hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p := by
    simpa only [scale, one_div_pow, mul_one_div] using hc.2.2.1
  rcases (normalized_return_collision_iff c p (by omega)
    ⟨hband.1,by linarith [hband.2]⟩ hc.2.1 hsmall hc.2.2.2.1 hwn hz).mp hwe
      with he | he
  · exact he ▸ hw
  · have hzw : z = -w := by rw [he,neg_neg]
    rw [hzw]
    exact parent_source_symmetric c p (by omega) hc.2.1.ne' w hw

/-- The complete crest disk is well inside the approximation disk, and
its first actual image lies in radius 7/20, uniformly from return index seventeen. -/
theorem actual_initialDisk_bounds {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : z ∈ initialDisk) :
    ‖z‖ < 23/20 ∧ ‖normalizedReturn c p z‖ < 7/20 := by
  have hzd : ‖z+(3/4 : ℂ)‖ ≤ (133/2000 : ℝ) := hz
  have hnorm : ‖z‖ ≤ (133/2000 : ℝ)+3/4 := by
    calc
      ‖z‖ = ‖(z+(3/4 : ℂ))-(3/4 : ℂ)‖ := by congr 1; ring
      _ ≤ ‖z+(3/4 : ℂ)‖+‖(3/4 : ℂ)‖ := norm_sub_le _ _
      _ ≤ (133/2000 : ℝ)+3/4 := by
        rw [show ‖(3/4 : ℂ)‖ = (3/4 : ℝ) by norm_num]
        linarith
  have hzR : ‖z‖ < 23/20 := by linarith
  have hk := hc.2.2.2.1
  have hcenter : ‖complexMap (kappa p c) (-(3/4 : ℂ))‖ ≤ (1/100 : ℝ) := by
    rw [show (-(3/4 : ℂ)) = ((-3/4 : ℝ) : ℂ) by norm_num,
      complexMap_real, Complex.norm_real, Real.norm_eq_abs, abs_le]
    dsimp [realMap]
    constructor <;> nlinarith [hk.1,hk.2]
  have hdiff := LimitingCrestPerturbation.quadratic_disk_lipschitz (kappa p c)
    (by linarith [hk.1]) (by linarith [hk.2]) z (-(3/4 : ℂ)) hzR.le
    (by norm_num)
  rw [sub_neg_eq_add] at hdiff
  change ‖complexMap (kappa p c) z-complexMap (kappa p c) (-(3/4 : ℂ))‖ ≤
    5*‖z+(3/4 : ℂ)‖ at hdiff
  have hqnorm := norm_le_norm_sub_add (complexMap (kappa p c) z)
    (complexMap (kappa p c) (-(3/4 : ℂ)))
  have hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p := by
    simpa only [scale,one_div_pow,mul_one_div] using hc.2.2.1
  have herror : ‖normalizedReturn c p z-complexMap (kappa p c) z‖ ≤ 24*scale p := by
    simpa only [scale,one_div_pow,mul_one_div,kappa] using
      normalized_return_error c p (by omega) hc.2.2.2.2.2.2 hc.2.1 hsmall z hzR.le
  have hnormH := norm_le_norm_sub_add (normalizedReturn c p z) (complexMap (kappa p c) z)
  refine ⟨hzR,?_⟩
  linarith [scale_small hp]

/-- The entire closed disk containing every selected crest circle is
inside the same actual proper central p-return component. -/
theorem initialDisk_subset_parent {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : initialDisk ⊆ parentSource c p := by
  intro z hz
  have hb := actual_initialDisk_bounds hp hc hz
  exact actual_parent_exhaustion hp hc hb.1.le (hb.2.trans (by norm_num))

/-- In physical coordinates this is the disk centered at -3x_p/4,
with radius (133/2000)x_p. The inclusion concerns the literal same
parameter and polynomial return as the crest construction. -/
theorem physical_initialDisk_subset_parent {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    {w : ℂ | ‖w+((3*criticalValue c p/4 : ℝ) : ℂ)‖ ≤
      criticalValue c p*(133/2000)} ⊆ physicalParentSource c p := by
  intro w hw
  change ‖w+((3*criticalValue c p/4 : ℝ) : ℂ)‖ ≤
    criticalValue c p*(133/2000) at hw
  let d := criticalValue c p
  have hd : 0 < d := hc.2.1
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hz : w/(d : ℂ) ∈ initialDisk := by
    change ‖w/(d : ℂ)+(3/4 : ℂ)‖ ≤ (133/2000 : ℝ)
    have he : w/(d : ℂ)+(3/4 : ℂ) =
        (w+((3*d/4 : ℝ) : ℂ))/(d : ℂ) := by
      push_cast
      field_simp
    rw [he,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hd]
    exact (div_le_iff₀ hd).mpr (by simpa only [d,mul_comm] using hw)
  refine ⟨w/(d : ℂ),initialDisk_subset_parent hp hc hz,?_⟩
  change (d : ℂ)*(w/(d : ℂ)) = w
  field_simp

/-- The same physical crest disk lies in the original archived return
component. Only inclusion is used; the two parent components are not
identified or assigned the same ideal marking. -/
theorem physical_initialDisk_subset_archived {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    {w : ℂ | ‖w+((3*criticalValue c p/4 : ℝ) : ℂ)‖ ≤
      criticalValue c p*(133/2000)} ⊆ archivedParentSource c p :=
  (physical_initialDisk_subset_parent hp hc).trans
    (physical_parent_subset_archived c p hc.2.1 (actual_parent_restriction hp hc)
      (actual_parent_scale_bound hp hc))

end
end ActualCrestProperReturn
