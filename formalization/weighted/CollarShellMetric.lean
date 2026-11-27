import CollarExtremalLength
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# A shell density for every rectifiable collar crossing

The final arclength interval after the last contact with the inner round
ball has length at least the radial gap. A density supported on the round
shell is therefore admissible for the whole rectifiable joining family.
This gives a direct `19π` two-modulus bound on the physical collars, without
identifying two-modulus with Dirichlet capacity.
-/

namespace CollarShellMetric

open Set Metric MeasureTheory
open CollarExtremalLength
open scoped ENNReal NNReal Topology

noncomputable section

/-- The constant reciprocal-gap density on the closed outer round shell. -/
def shellMetric (r R : ℝ) : ℂ → ℝ≥0∞ :=
  (closedBall (0 : ℂ) R \ ball 0 r).indicator
    (fun _ => ENNReal.ofReal (1 / (R-r)))

theorem shellMetric_measurable (r R : ℝ) : Measurable (shellMetric r R) :=
  measurable_const.indicator (isClosed_closedBall.measurableSet.diff isOpen_ball.measurableSet)

private theorem arcParameter_zero (γ : RectifiableCurve) : arcParameter γ 0 = γ 0 := by
  have h := edist_naturalParameterization_eq_zero γ.finite.locallyBoundedVariationOn
    (by norm_num : (0 : ℝ) ∈ Icc 0 1) (by norm_num : (0 : ℝ) ∈ Icc 0 1)
  simpa [arcParameter, variationOnFromTo.self] using edist_eq_zero.mp h

private theorem arcParameter_end (γ : RectifiableCurve) :
    arcParameter γ (curveLength γ) = γ 1 := by
  have h := edist_naturalParameterization_eq_zero γ.finite.locallyBoundedVariationOn
    (by norm_num : (0 : ℝ) ∈ Icc 0 1) (by norm_num : (1 : ℝ) ∈ Icc 0 1)
  simpa [arcParameter, curveLength, variationOnFromTo.eq_of_le] using edist_eq_zero.mp h

/-- Every joining curve has a final interval in the round shell whose
arclength is at least the radial gap. Last contact, rather than first
contact, permits every possible earlier backtracking and repeated turn. -/
theorem exists_final_shell_interval {K : Set ℂ} {r R : ℝ}
    (hK : K ⊆ closedBall 0 r) (hrR : r < R)
    {γ : RectifiableCurve} (hγ : Joining K R γ) :
    ∃ s ∈ Icc 0 (curveLength γ), R-r ≤ curveLength γ-s ∧
      ∀ t ∈ Ioc s (curveLength γ),
        arcParameter γ t ∈ closedBall (0 : ℂ) R \ ball 0 r := by
  have hL : 0 ≤ curveLength γ := ENNReal.toReal_nonneg
  let S : Set ℝ := Icc 0 (curveLength γ) ∩ arcParameter γ ⁻¹' closedBall 0 r
  have hS : IsCompact S := isCompact_Icc.of_isClosed_subset
    ((arcParameter_lipschitz γ).continuousOn.preimage_isClosed_of_isClosed
      isClosed_Icc isClosed_closedBall) inter_subset_left
  have hS0 : (0 : ℝ) ∈ S := by
    refine ⟨⟨le_rfl, hL⟩, ?_⟩
    change arcParameter γ 0 ∈ closedBall 0 r
    rw [arcParameter_zero]
    exact hK hγ.1
  obtain ⟨s, hs⟩ := hS.exists_isGreatest ⟨0, hS0⟩
  have hsI : s ∈ Icc 0 (curveLength γ) := hs.1.1
  have hsNorm : ‖arcParameter γ s‖ ≤ r := by simpa using hs.1.2
  have hendNorm : ‖arcParameter γ (curveLength γ)‖ = R := by
    rw [arcParameter_end]
    simpa using hγ.2.1
  have hdist : dist (arcParameter γ (curveLength γ)) (arcParameter γ s) ≤
      curveLength γ-s := by
    have h := (arcParameter_lipschitz γ).dist_le_mul
      (curveLength γ) ⟨hL, le_rfl⟩ s hsI
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr hsI.2)] using h
  have hgap : R-r ≤ curveLength γ-s := by
    have hnorm := norm_sub_norm_le (arcParameter γ (curveLength γ)) (arcParameter γ s)
    rw [dist_eq_norm] at hdist
    linarith
  have hrange : γ.toFun '' Icc 0 1 ⊆ closedBall 0 R := by
    rintro _ ⟨u, hu, rfl⟩
    rcases eq_or_lt_of_le hu.1 with h | h
    · subst u
      exact closedBall_subset_closedBall hrR.le (hK hγ.1)
    · rcases eq_or_lt_of_le hu.2 with h' | h'
      · subst u
        exact sphere_subset_closedBall hγ.2.1
      · exact ball_subset_closedBall (hγ.2.2 u ⟨h, h'⟩).1
  refine ⟨s, hsI, hgap, ?_⟩
  intro t ht
  have htI : t ∈ Icc 0 (curveLength γ) := ⟨hsI.1.trans ht.1.le, ht.2⟩
  refine ⟨hrange (arcParameter_mem_image γ htI), ?_⟩
  intro hin
  have htS : t ∈ S := ⟨htI, ball_subset_closedBall hin⟩
  exact (not_le_of_gt ht.1) (hs.2 htS)

/-- The shell density is admissible for every continuous rectifiable
joining curve, with no simplicity or differentiability condition. -/
theorem shellMetric_admissible {K : Set ℂ} {r R : ℝ}
    (hK : K ⊆ closedBall 0 r) (hrR : r < R) :
    admissibleMetric K R (shellMetric r R) := by
  refine ⟨shellMetric_measurable r R, ?_⟩
  intro γ hγ
  obtain ⟨s, hs, hgap, htail⟩ := exists_final_shell_interval hK hrR hγ
  have hlength : (∫⁻ t in Ioc s (curveLength γ), shellMetric r R (arcParameter γ t)) =
      ENNReal.ofReal (1/(R-r)) * ENNReal.ofReal (curveLength γ-s) := by
    calc
      (∫⁻ t in Ioc s (curveLength γ), shellMetric r R (arcParameter γ t)) =
          ∫⁻ _t in Ioc s (curveLength γ), ENNReal.ofReal (1/(R-r)) := by
        apply setLIntegral_congr_fun measurableSet_Ioc
        intro t ht
        exact indicator_of_mem (htail t ht) _
      _ = _ := by simp
  have hone : (1/(R-r))*(R-r) = (1 : ℝ) := by
    field_simp [sub_ne_zero.mpr hrR.ne']
  have hprod : (1 : ℝ) ≤ (1/(R-r))*(curveLength γ-s) := by
    have h := mul_le_mul_of_nonneg_left hgap (by positivity : (0 : ℝ) ≤ 1/(R-r))
    rwa [hone] at h
  calc
    (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1/(R-r)) * ENNReal.ofReal (curveLength γ-s) := by
      rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1/(R-r))]
      simpa using ENNReal.ofReal_le_ofReal hprod
    _ = ∫⁻ t in Ioc s (curveLength γ), shellMetric r R (arcParameter γ t) := hlength.symm
    _ ≤ metricLength (shellMetric r R) γ :=
      lintegral_mono_set (fun _ ht => ⟨hs.1.trans ht.1.le, ht.2⟩)

/-- Exact Euclidean area of the shell density. -/
theorem shellMetric_area {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) :
    metricArea (shellMetric r R) =
      ENNReal.ofReal (Real.pi * (R^2-r^2)/(R-r)^2) := by
  have hR : 0 ≤ R := hr.trans hrR.le
  have hgap : 0 ≤ 1/(R-r) := by positivity
  have hvol : volume (closedBall (0 : ℂ) R \ ball 0 r) =
      ENNReal.ofReal ((R^2-r^2)*Real.pi) := by
    rw [measure_sdiff (ball_subset_closedBall.trans (closedBall_subset_closedBall hrR.le))
      isOpen_ball.measurableSet.nullMeasurableSet measure_ball_lt_top.ne]
    simp only [Complex.volume_closedBall, Complex.volume_ball]
    rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
      ← ENNReal.ofReal_pow hR, ← ENNReal.ofReal_pow hr,
      ← ENNReal.ofReal_mul (sq_nonneg R), ← ENNReal.ofReal_mul (sq_nonneg r),
      ← ENNReal.ofReal_sub _ (by positivity : (0 : ℝ) ≤ r^2*Real.pi)]
    congr 1
    ring
  have heq : (fun z : ℂ => shellMetric r R z ^ 2) =
      (closedBall (0 : ℂ) R \ ball 0 r).indicator
        (fun _ => ENNReal.ofReal (1/(R-r)) ^ 2) := by
    funext z
    by_cases hz : z ∈ closedBall (0 : ℂ) R \ ball 0 r <;> simp [shellMetric, hz]
  rw [metricArea, heq,
    lintegral_indicator (isClosed_closedBall.measurableSet.diff isOpen_ball.measurableSet),
    lintegral_const, Measure.restrict_apply_univ, hvol,
    ← ENNReal.ofReal_pow hgap,
    ← ENNReal.ofReal_mul (sq_nonneg (1/(R-r)))]
  congr 1
  field_simp

/-- A shell rather than a whole-disk density gives the improved direct
bound on the actual all-rectifiable-curve two-modulus. -/
theorem curveModulus_le_shell_ratio {K : Set ℂ} {r R : ℝ}
    (hK : K ⊆ closedBall 0 r) (hr : 0 ≤ r) (hrR : r < R) :
    curveModulus K R ≤ ENNReal.ofReal (Real.pi*(R^2-r^2)/(R-r)^2) := by
  have h := curveModulus_le_area (shellMetric_admissible hK hrR)
  rwa [shellMetric_area hr hrR] at h

/-- The fixed physical radii give `19π` uniformly at every scale. -/
theorem physical_curveModulus_le_19pi {d : ℝ} (hd : 0 < d) {K : Set ℂ}
    (hK : K ⊆ closedBall 0 (3*d/20)) :
    curveModulus K (d/6) ≤ ENNReal.ofReal (19*Real.pi) := by
  have h := curveModulus_le_shell_ratio hK (by positivity : (0 : ℝ) ≤ 3*d/20)
    (by linarith : 3*d/20 < d/6)
  convert h using 1
  congr 1
  field_simp
  ring

theorem physical_curveModulus_lt_sixty {d : ℝ} (hd : 0 < d) {K : Set ℂ}
    (hK : K ⊆ closedBall 0 (3*d/20)) :
    curveModulus K (d/6) < 60 := by
  apply (physical_curveModulus_le_19pi hd hK).trans_lt
  have hpi : 19*Real.pi < (60 : ℝ) := by nlinarith [Real.pi_lt_d4]
  simpa using (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 60)).2 hpi

/-- The direct standard joining-curve extremal length is strictly
larger than `1/60`, independently of Dirichlet-capacity duality. -/
theorem physical_extremalLength_gt_one_sixty {d : ℝ} (hd : 0 < d) {K : Set ℂ}
    (hK : K ⊆ closedBall 0 (3*d/20)) :
    (60 : ℝ≥0∞)⁻¹ < extremalLength K (d/6) :=
  ENNReal.inv_lt_inv.mpr (physical_curveModulus_lt_sixty hd hK)

end
end CollarShellMetric
