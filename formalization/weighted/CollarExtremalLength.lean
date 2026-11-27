import Mathlib.Analysis.ConstantSpeed
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.LeftRight
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The joining-curve extremal length of a physical collar

The family here contains every continuous rectifiable joining curve, with
arbitrary parametrization and with multiplicity retained. Metric length is
the integral of the density in Mathlib's natural unit-speed parameter.
The two-modulus infimizes area over all measurable admissible densities;
its reciprocal is the joining-curve extremal length. No identification
with a uniformizing round-annulus parameter is made here.
-/

namespace CollarExtremalLength

open Set MeasureTheory Filter Metric
open scoped ENNReal NNReal Topology

noncomputable section

/-- A continuous rectifiable complex curve, with its original arbitrary
parameter on the unit interval. -/
structure RectifiableCurve where
  toFun : ℝ → ℂ
  continuous : ContinuousOn toFun (Icc 0 1)
  finite : BoundedVariationOn toFun (Icc 0 1)

instance : CoeFun RectifiableCurve (fun _ => ℝ → ℂ) := ⟨RectifiableCurve.toFun⟩

def curveLength (γ : RectifiableCurve) : ℝ :=
  (eVariationOn γ.toFun (Icc 0 1)).toReal

def arcParameter (γ : RectifiableCurve) : ℝ → ℂ :=
  naturalParameterization γ.toFun (Icc 0 1) 0

private theorem curve_variation_continuous (γ : RectifiableCurve) :
    ContinuousOn (variationOnFromTo γ.toFun (Icc 0 1) 0) (Icc 0 1) := by
  intro x hx
  apply continuousWithinAt_iff_continuous_left'_right'.mpr
  constructor
  · have h := variationOnFromTo.tendsto_left (f := γ.toFun)
      (by norm_num : (0 : ℝ) ∈ Icc 0 1) hx γ.finite.locallyBoundedVariationOn
      ((γ.continuous x hx).mono inter_subset_left)
    simpa [ContinuousWithinAt] using h
  · have h := variationOnFromTo.tendsto_right (f := γ.toFun)
      (by norm_num : (0 : ℝ) ∈ Icc 0 1) hx γ.finite.locallyBoundedVariationOn
      ((γ.continuous x hx).mono inter_subset_left)
    simpa [ContinuousWithinAt] using h

/-- The original variation parameter covers the complete arclength
interval. In particular no gaps or constant pieces are discarded as
unaccounted curve length. -/
theorem variation_parameter_image (γ : RectifiableCurve) :
    variationOnFromTo γ.toFun (Icc 0 1) 0 '' Icc 0 1 =
      Icc 0 (curveLength γ) := by
  have h := (curve_variation_continuous γ).image_Icc_of_monotoneOn
    (by norm_num : (0 : ℝ) ≤ 1)
    (variationOnFromTo.monotoneOn γ.finite.locallyBoundedVariationOn
      (by norm_num : (0 : ℝ) ∈ Icc 0 1))
  simpa [curveLength, variationOnFromTo.eq_of_le, variationOnFromTo.self] using h

/-- The arclength representative remains on the original geometric
curve at every parameter, not just almost everywhere. -/
theorem arcParameter_mem_image (γ : RectifiableCurve) {s : ℝ}
    (hs : s ∈ Icc 0 (curveLength γ)) :
    arcParameter γ s ∈ γ.toFun '' Icc 0 1 := by
  rw [← variation_parameter_image γ] at hs
  obtain ⟨t, ht, rfl⟩ := hs
  have heq := edist_naturalParameterization_eq_zero γ.finite.locallyBoundedVariationOn
    (by norm_num : (0 : ℝ) ∈ Icc 0 1) ht
  exact ⟨t, ht, (edist_eq_zero.mp heq).symm⟩

/-- The chosen parameter has unit speed in the literal total-variation
sense supplied by Mathlib. This justifies using Lebesgue arclength below. -/
theorem arcParameter_unit_speed (γ : RectifiableCurve) :
    HasUnitSpeedOn (arcParameter γ) (Icc 0 (curveLength γ)) := by
  rw [← variation_parameter_image γ]
  exact has_unit_speed_naturalParameterization γ.toFun
    γ.finite.locallyBoundedVariationOn (by norm_num)

/-- Arclength parametrization is genuinely one-Lipschitz on its whole
parameter interval. In particular metric-length integrands for measurable
densities are measurable on that interval. -/
theorem arcParameter_lipschitz (γ : RectifiableCurve) :
    LipschitzOnWith 1 (arcParameter γ) (Icc 0 (curveLength γ)) := by
  have H (s t : ℝ) (hs : s ∈ Icc 0 (curveLength γ))
      (ht : t ∈ Icc 0 (curveLength γ)) (hst : s ≤ t) :
      edist (arcParameter γ s) (arcParameter γ t) ≤ edist s t := by
    calc
      edist (arcParameter γ s) (arcParameter γ t) ≤
          eVariationOn (arcParameter γ) (Icc 0 (curveLength γ) ∩ Icc s t) :=
        eVariationOn.edist_le _ ⟨hs, le_rfl, hst⟩ ⟨ht, hst, le_rfl⟩
      _ = ENNReal.ofReal (t-s) := by
        simpa [HasUnitSpeedOn, HasConstantSpeedOnWith] using
          arcParameter_unit_speed γ hs ht
      _ = edist s t := by
        rw [edist_dist, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst), neg_sub]
  intro s hs t ht
  simp only [ENNReal.coe_one, one_mul]
  rcases le_total s t with hst | hts
  · exact H s t hs ht hst
  · simpa only [edist_comm] using H t s ht hs hts

theorem arcParameter_image (γ : RectifiableCurve) :
    arcParameter γ '' Icc 0 (curveLength γ) = γ.toFun '' Icc 0 1 := by
  apply Subset.antisymm
  · rintro _ ⟨s, hs, rfl⟩
    exact arcParameter_mem_image γ hs
  · rintro _ ⟨t, ht, rfl⟩
    refine ⟨variationOnFromTo γ.toFun (Icc 0 1) 0 t, ?_, ?_⟩
    · rw [← variation_parameter_image γ]
      exact mem_image_of_mem _ ht
    · exact edist_eq_zero.mp (edist_naturalParameterization_eq_zero
        γ.finite.locallyBoundedVariationOn (by norm_num : (0 : ℝ) ∈ Icc 0 1) ht)

/-- Integration in arclength retains arbitrary repeated traversals. -/
def metricLength (ρ : ℂ → ℝ≥0∞) (γ : RectifiableCurve) : ℝ≥0∞ :=
  ∫⁻ s in Icc 0 (curveLength γ), ρ (arcParameter γ s)

def metricArea (ρ : ℂ → ℝ≥0∞) : ℝ≥0∞ := ∫⁻ z, (ρ z) ^ 2

/-- Joining curves run from the inner plate to the actual outer circle,
with their open parameter interval in the intervening physical collar. -/
def Joining (K : Set ℂ) (R : ℝ) (γ : RectifiableCurve) : Prop :=
  γ 0 ∈ K ∧ γ 1 ∈ sphere 0 R ∧
    ∀ t ∈ Ioo (0 : ℝ) 1, γ t ∈ ball 0 R \ K

def admissibleMetric (K : Set ℂ) (R : ℝ) (ρ : ℂ → ℝ≥0∞) : Prop :=
  Measurable ρ ∧ ∀ γ : RectifiableCurve, Joining K R γ → 1 ≤ metricLength ρ γ

/-- Standard planar two-modulus, for the complete rectifiable joining
family above and every measurable nonnegative conformal density. -/
def curveModulus (K : Set ℂ) (R : ℝ) : ℝ≥0∞ :=
  sInf (metricArea '' {ρ | admissibleMetric K R ρ})

/-- Joining-curve extremal length is reciprocal two-modulus. -/
def extremalLength (K : Set ℂ) (R : ℝ) : ℝ≥0∞ := (curveModulus K R)⁻¹

theorem curveModulus_le_area {K : Set ℂ} {R : ℝ} {ρ : ℂ → ℝ≥0∞}
    (hρ : admissibleMetric K R ρ) : curveModulus K R ≤ metricArea ρ :=
  sInf_le ⟨ρ, hρ, rfl⟩

def diskMetric (R a : ℝ) : ℂ → ℝ≥0∞ :=
  (closedBall (0 : ℂ) R).indicator (fun _ => ENNReal.ofReal a)

theorem diskMetric_measurable (R a : ℝ) : Measurable (diskMetric R a) :=
  measurable_const.indicator isClosed_closedBall.measurableSet

theorem diskMetric_area {R a : ℝ} (hR : 0 ≤ R) (ha : 0 ≤ a) :
    metricArea (diskMetric R a) = ENNReal.ofReal (a^2 * R^2 * Real.pi) := by
  have heq : (fun z : ℂ => diskMetric R a z ^ 2) =
      (closedBall (0 : ℂ) R).indicator (fun _ => ENNReal.ofReal a ^ 2) := by
    funext z
    by_cases hz : z ∈ closedBall (0 : ℂ) R <;> simp [diskMetric, hz]
  rw [metricArea, heq, lintegral_indicator isClosed_closedBall.measurableSet,
    lintegral_const, Measure.restrict_apply_univ, Complex.volume_closedBall]
  rw [← ENNReal.ofReal_pow ha, ← ENNReal.ofReal_pow hR,
    ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi,
    ← ENNReal.ofReal_mul (sq_nonneg R), ← ENNReal.ofReal_mul (sq_nonneg a)]
  congr 1
  ring

private theorem joining_range_subset {K : Set ℂ} {r R : ℝ}
    (hK : K ⊆ closedBall 0 r) (hrR : r ≤ R)
    {γ : RectifiableCurve} (hγ : Joining K R γ) :
    γ.toFun '' Icc 0 1 ⊆ closedBall 0 R := by
  rintro _ ⟨t, ht, rfl⟩
  rcases eq_or_lt_of_le ht.1 with h | h
  · subst t
    exact closedBall_subset_closedBall hrR (hK hγ.1)
  · rcases eq_or_lt_of_le ht.2 with h' | h'
    · subst t
      exact sphere_subset_closedBall hγ.2.1
    · exact ball_subset_closedBall (hγ.2.2 t ⟨h, h'⟩).1

theorem curveLength_ge_gap {K : Set ℂ} {r R : ℝ}
    (hK : K ⊆ closedBall 0 r) {γ : RectifiableCurve} (hγ : Joining K R γ) :
    R - r ≤ curveLength γ := by
  have hzero : ‖γ 0‖ ≤ r := by simpa using hK hγ.1
  have hone : ‖γ 1‖ = R := by simpa using hγ.2.1
  have hdist : dist (γ 1) (γ 0) ≤ curveLength γ := by
    rw [dist_edist]
    exact ENNReal.toReal_mono γ.finite
      (eVariationOn.edist_le γ.toFun (by norm_num : (1 : ℝ) ∈ Icc 0 1)
        (by norm_num : (0 : ℝ) ∈ Icc 0 1))
  have hnorm := norm_sub_norm_le (γ 1) (γ 0)
  rw [dist_eq_norm] at hdist
  linarith

theorem diskMetric_length {K : Set ℂ} {r R a : ℝ}
    (hK : K ⊆ closedBall 0 r) (hrR : r ≤ R)
    {γ : RectifiableCurve} (hγ : Joining K R γ) :
    metricLength (diskMetric R a) γ =
      ENNReal.ofReal a * ENNReal.ofReal (curveLength γ) := by
  unfold metricLength
  calc
    (∫⁻ s in Icc 0 (curveLength γ), diskMetric R a (arcParameter γ s)) =
        ∫⁻ s in Icc 0 (curveLength γ), ENNReal.ofReal a := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro s hs
      exact indicator_of_mem
        (joining_range_subset hK hrR hγ (arcParameter_mem_image γ hs)) _
    _ = _ := by simp

/-- One explicit finite-area density is admissible for every continuous
rectifiable joining curve, including curves with repeated traversals. -/
theorem diskMetric_admissible {K : Set ℂ} {r R : ℝ}
    (hK : K ⊆ closedBall 0 r) (hrR : r < R) :
    admissibleMetric K R (diskMetric R (1 / (R-r))) := by
  refine ⟨diskMetric_measurable _ _, ?_⟩
  intro γ hγ
  rw [diskMetric_length hK hrR.le hγ,
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / (R-r))]
  have h := mul_le_mul_of_nonneg_left (curveLength_ge_gap hK hγ)
    (by positivity : (0 : ℝ) ≤ 1 / (R-r))
  have hgap : R-r ≠ 0 := sub_ne_zero.mpr hrR.ne'
  have hone : (1 / (R-r)) * (R-r) = (1 : ℝ) := by field_simp
  rw [hone] at h
  simpa using ENNReal.ofReal_le_ofReal h

/-- A direct estimate on the complete joining-curve two-modulus, using
the actual Euclidean area and the arclength of every rectifiable curve. -/
theorem curveModulus_le_disk_ratio {K : Set ℂ} {r R : ℝ}
    (hK : K ⊆ closedBall 0 r) (hR : 0 ≤ R) (hrR : r < R) :
    curveModulus K R ≤ ENNReal.ofReal (Real.pi * R^2 / (R-r)^2) := by
  have h := curveModulus_le_area (diskMetric_admissible hK hrR)
  rw [diskMetric_area hR (by positivity)] at h
  convert h using 1
  congr 1
  field_simp

/-- Positive geometric separation gives a positive joining-curve
extremal-length lower bound, independently of capacity duality. -/
theorem extremalLength_ge_disk_ratio {K : Set ℂ} {r R : ℝ}
    (hK : K ⊆ closedBall 0 r) (hR : 0 ≤ R) (hrR : r < R) :
    (ENNReal.ofReal (Real.pi * R^2 / (R-r)^2))⁻¹ ≤ extremalLength K R := by
  exact ENNReal.inv_le_inv.mpr (curveModulus_le_disk_ratio hK hR hrR)

/-- The fixed physical radii from the actual three-return construction
give the same joining-curve bound at every physical scale. -/
theorem physical_curveModulus_le {d : ℝ} (hd : 0 < d) {K : Set ℂ}
    (hK : K ⊆ closedBall 0 (3*d/20)) :
    curveModulus K (d/6) ≤ ENNReal.ofReal (100 * Real.pi) := by
  have h := curveModulus_le_disk_ratio hK (by positivity : (0 : ℝ) ≤ d/6)
    (by linarith : 3*d/20 < d/6)
  convert h using 1
  congr 1
  field_simp
  ring

/-- This is a lower bound for the standard arclength/density joining
family, not a renaming of the Dirichlet-capacity invariant. -/
theorem physical_extremalLength_ge {d : ℝ} (hd : 0 < d) {K : Set ℂ}
    (hK : K ⊆ closedBall 0 (3*d/20)) :
    (ENNReal.ofReal (100 * Real.pi))⁻¹ ≤ extremalLength K (d/6) :=
  ENNReal.inv_le_inv.mpr (physical_curveModulus_le hd hK)

end
end CollarExtremalLength
