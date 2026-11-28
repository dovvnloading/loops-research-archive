import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Tactic

/-!
# Finite planar energy of the three-root cubic differential

The explicit squared magnitude is locally integrable at its three simple
poles in the plane and is bounded at infinity by a multiple of
`(1 + ‖z‖)^(-3)`. No boundary smoothness or uniformization is assumed.
-/

namespace SlitCubicArea

open Set Filter MeasureTheory Asymptotics
open scoped Topology ENNReal

noncomputable section

def densitySq (a b c : ℝ) (z : ℂ) : ℝ :=
  1 / (‖z-(a:ℂ)‖ * ‖z-(b:ℂ)‖ * ‖z-(c:ℂ)‖)

theorem densitySq_nonneg (a b c : ℝ) (z : ℂ) : 0 ≤ densitySq a b c z := by
  unfold densitySq
  positivity

theorem densitySq_measurable (a b c : ℝ) : Measurable (densitySq a b c) := by
  unfold densitySq
  fun_prop

private def factor (a : ℝ) (z : ℂ) : ℝ := ‖z-(a:ℂ)‖⁻¹

private theorem factor_nonneg (a : ℝ) (z : ℂ) : 0 ≤ factor a z := by
  unfold factor
  positivity

private theorem factor_measurable (a : ℝ) : Measurable (factor a) := by
  unfold factor
  fun_prop

private theorem densitySq_eq_factors (a b c : ℝ) (z : ℂ) :
    densitySq a b c z = factor a z * factor b z * factor c z := by
  simp [densitySq, factor, one_div, mul_inv_rev, mul_comm, mul_assoc]

private theorem continuousAt_factor {a : ℝ} {z : ℂ} (hz : z ≠ (a:ℂ)) :
    ContinuousAt (factor a) z := by
  exact ((continuous_id.sub continuous_const).norm.continuousAt).inv₀
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hz))

private theorem locallyIntegrable_factor_zero : LocallyIntegrable (factor 0) := by
  apply locallyIntegrable_of_norm_le_rpow (E := ℂ) (C := 1) (α := (1 : ℝ))
    (by norm_num [Complex.finrank_real_complex])
    (by norm_num [Complex.finrank_real_complex])
  · filter_upwards [] with z
    simp [factor, Real.rpow_neg_one]
  · exact (factor_measurable 0).aestronglyMeasurable

private theorem locallyIntegrable_factor (a : ℝ) : LocallyIntegrable (factor a) := by
  intro z
  let e : ℂ ≃ₜ ℂ := Homeomorph.addRight (-(a:ℂ))
  have he := e.measurableEmbedding.integrableAtFilter_map_iff
    (l := 𝓝 z) (μ := volume) (f := factor 0)
  have hmap : Filter.map e (𝓝 z) = 𝓝 (z-(a:ℂ)) := by
    change Filter.map (Homeomorph.addRight (-(a:ℂ))) (𝓝 z) = 𝓝 (z + -(a:ℂ))
    exact (Homeomorph.addRight (-(a:ℂ))).map_nhds_eq z
  have hvol : Measure.map e volume = volume :=
    map_add_right_eq_self volume (-(a:ℂ))
  rw [hmap, hvol] at he
  have h := he.mp (locallyIntegrable_factor_zero (z-(a:ℂ)))
  convert h using 1
  all_goals first | rfl | (funext w; simp [e, factor, sub_eq_add_neg])

private theorem locallyIntegrable_densitySq {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    LocallyIntegrable (densitySq a b c) := by
  intro z
  have hab' : (a:ℂ) ≠ (b:ℂ) := by exact_mod_cast hab.ne
  have hac' : (a:ℂ) ≠ (c:ℂ) := by exact_mod_cast (hab.trans hbc).ne
  have hbc' : (b:ℂ) ≠ (c:ℂ) := by exact_mod_cast hbc.ne
  have hmeas := (densitySq_measurable a b c).aestronglyMeasurable.stronglyMeasurableAtFilter
    (l := 𝓝 z) (μ := volume)
  by_cases hza : z = (a:ℂ)
  · subst z
    have hb := (continuousAt_factor hab').tendsto.isBigO_one ℝ
    have hc := (continuousAt_factor hac').tendsto.isBigO_one ℝ
    have hO : densitySq a b c =O[𝓝 (a:ℂ)] factor a := by
      simpa only [← densitySq_eq_factors, mul_one] using
        ((isBigO_refl (factor a) (𝓝 (a:ℂ))).mul hb).mul hc
    exact hO.integrableAtFilter hmeas (locallyIntegrable_factor a (a:ℂ))
  by_cases hzb : z = (b:ℂ)
  · subst z
    have ha := (continuousAt_factor hab'.symm).tendsto.isBigO_one ℝ
    have hc := (continuousAt_factor hbc').tendsto.isBigO_one ℝ
    have hO : densitySq a b c =O[𝓝 (b:ℂ)] factor b := by
      simpa only [← densitySq_eq_factors, one_mul, mul_one] using
        (ha.mul (isBigO_refl (factor b) (𝓝 (b:ℂ)))).mul hc
    exact hO.integrableAtFilter hmeas (locallyIntegrable_factor b (b:ℂ))
  · have ha := (continuousAt_factor hza).tendsto.isBigO_one ℝ
    have hb := (continuousAt_factor hzb).tendsto.isBigO_one ℝ
    have hO : densitySq a b c =O[𝓝 z] factor c := by
      simpa only [← densitySq_eq_factors, one_mul] using
        (ha.mul hb).mul (isBigO_refl (factor c) (𝓝 z))
    exact hO.integrableAtFilter hmeas (locallyIntegrable_factor c z)

private theorem factor_isBigO_cocompact (a : ℝ) :
    factor a =O[cocompact ℂ] (fun z : ℂ => (1+‖z‖)⁻¹) := by
  refine isBigO_iff.mpr ⟨4, ?_⟩
  filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop
    (max 1 (2*‖(a:ℂ)‖))] with z hz
  have h1 : 1 ≤ ‖z‖ := (le_max_left _ _).trans hz
  have ha : 2*‖(a:ℂ)‖ ≤ ‖z‖ := (le_max_right _ _).trans hz
  have htri : ‖z‖ ≤ ‖z-(a:ℂ)‖ + ‖(a:ℂ)‖ := by
    simpa only [dist_eq_norm, sub_zero] using dist_triangle z (a:ℂ) 0
  have hd : 0 < ‖z-(a:ℂ)‖ := by linarith
  have hb : 1+‖z‖ ≤ 4*‖z-(a:ℂ)‖ := by linarith
  calc
    ‖factor a z‖ = 1 / ‖z-(a:ℂ)‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (factor_nonneg a z)]
      simp only [factor, one_div]
    _ ≤ 4 / (1+‖z‖) := (div_le_div_iff₀ hd (by positivity)).mpr (by simpa using hb)
    _ = 4 * ‖(1+‖z‖)⁻¹‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (by positivity))]
      rfl

private theorem integrable_tail_reference :
    Integrable (fun z : ℂ => (1+‖z‖)⁻¹ * (1+‖z‖)⁻¹ * (1+‖z‖)⁻¹) := by
  have h := integrable_one_add_norm (E := ℂ) (μ := volume) (r := (3:ℝ))
    (by norm_num [Complex.finrank_real_complex])
  convert h using 1
  funext z
  rw [Real.rpow_neg (by positivity)]
  norm_num [Real.rpow_natCast, pow_succ, mul_inv_rev, mul_assoc]

private theorem integrableAtCocompact_densitySq (a b c : ℝ) :
    IntegrableAtFilter (densitySq a b c) (cocompact ℂ) volume := by
  have hO := ((factor_isBigO_cocompact a).mul (factor_isBigO_cocompact b)).mul
    (factor_isBigO_cocompact c)
  have hO' : densitySq a b c =O[cocompact ℂ]
      (fun z : ℂ => (1+‖z‖)⁻¹ * (1+‖z‖)⁻¹ * (1+‖z‖)⁻¹) := by
    simpa only [← densitySq_eq_factors] using hO
  exact hO'.integrableAtFilter
    (densitySq_measurable a b c).aestronglyMeasurable.stronglyMeasurableAtFilter
    (integrable_tail_reference.integrableAtFilter _)

/-- The actual cubic squared magnitude has finite planar integral. -/
theorem integrable_densitySq {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    Integrable (densitySq a b c) :=
  integrable_iff_integrableAtFilter_cocompact.mpr
    ⟨integrableAtCocompact_densitySq a b c, locallyIntegrable_densitySq hab hbc⟩

/-- The same finite-energy assertion in the extended nonnegative integral
used by the curve-family modulus definitions. -/
theorem lintegral_densitySq_lt_top {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    (∫⁻ z : ℂ, ENNReal.ofReal (densitySq a b c z)) < ∞ :=
  (integrable_densitySq hab hbc).lintegral_lt_top

end
end SlitCubicArea
