import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Tactic

/-!
# Integrability of the three-root boundary kernel

The real boundary magnitude of the cubic slit differential has integrable
square-root singularities at three distinct real roots and decays with
exponent `-3/2` at infinity. These are estimates on the actual kernel.
-/

namespace SlitCubicIntegrability

open Set Filter MeasureTheory Asymptotics
open scoped Topology

noncomputable section

def kernel (a b c x : ℝ) : ℝ :=
  1 / (Real.sqrt |x-a| * Real.sqrt |x-b| * Real.sqrt |x-c|)

theorem kernel_nonneg (a b c x : ℝ) : 0 ≤ kernel a b c x := by
  unfold kernel
  positivity

theorem kernel_pos {a b c x : ℝ} (ha : x ≠ a) (hb : x ≠ b) (hc : x ≠ c) :
    0 < kernel a b c x := by
  apply one_div_pos.mpr
  exact mul_pos (mul_pos
    (Real.sqrt_pos.mpr (abs_pos.mpr (sub_ne_zero.mpr ha)))
    (Real.sqrt_pos.mpr (abs_pos.mpr (sub_ne_zero.mpr hb))))
    (Real.sqrt_pos.mpr (abs_pos.mpr (sub_ne_zero.mpr hc)))

theorem kernel_measurable (a b c : ℝ) : Measurable (kernel a b c) := by
  unfold kernel
  fun_prop

private def factor (a x : ℝ) : ℝ := (Real.sqrt |x-a|)⁻¹

private theorem factor_eq_rpow (a x : ℝ) :
    factor a x = |x-a| ^ (-(1/2 : ℝ)) := by
  rw [factor, Real.sqrt_eq_rpow, Real.rpow_neg (abs_nonneg _)]

private theorem factor_nonneg (a x : ℝ) : 0 ≤ factor a x := by
  unfold factor
  positivity

private theorem factor_measurable (a : ℝ) : Measurable (factor a) := by
  unfold factor
  fun_prop

private theorem kernel_eq_factors (a b c x : ℝ) :
    kernel a b c x = factor a x * factor b x * factor c x := by
  simp [kernel, factor, one_div, mul_inv_rev, mul_comm, mul_assoc]

private theorem continuousAt_factor {a x : ℝ} (hx : x ≠ a) :
    ContinuousAt (factor a) x := by
  apply ((Real.continuous_sqrt.comp ((continuous_id.sub continuous_const).abs)).continuousAt).inv₀
  exact (Real.sqrt_pos.mpr (abs_pos.mpr (sub_ne_zero.mpr hx))).ne'

private theorem locallyIntegrable_factor_zero : LocallyIntegrable (factor 0) := by
  apply locallyIntegrable_of_norm_le_rpow (E := ℝ) (C := 1) (α := (1/2 : ℝ))
    (by simp) (by norm_num)
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (factor_nonneg 0 x),
      factor_eq_rpow, sub_zero, Real.norm_eq_abs, one_mul]
  · exact (factor_measurable 0).aestronglyMeasurable

private theorem locallyIntegrable_factor (a : ℝ) : LocallyIntegrable (factor a) := by
  intro x
  let e : ℝ ≃ₜ ℝ := Homeomorph.addRight (-a)
  have he := e.measurableEmbedding.integrableAtFilter_map_iff
    (l := 𝓝 x) (μ := volume) (f := factor 0)
  have hmap : Filter.map e (𝓝 x) = 𝓝 (x-a) := by
    change Filter.map (Homeomorph.addRight (-a)) (𝓝 x) = 𝓝 (x + -a)
    exact (Homeomorph.addRight (-a)).map_nhds_eq x
  have hvol : Measure.map e volume = volume := by
    exact map_add_right_eq_self volume (-a)
  rw [hmap, hvol] at he
  have h := he.mp (locallyIntegrable_factor_zero (x-a))
  convert h using 1
  all_goals first | rfl | (funext y; simp [e, factor, sub_eq_add_neg])

private theorem locallyIntegrable_kernel {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    LocallyIntegrable (kernel a b c) := by
  intro x
  have hmeas := (kernel_measurable a b c).aestronglyMeasurable.stronglyMeasurableAtFilter
    (l := 𝓝 x) (μ := volume)
  by_cases hxa : x = a
  · subst x
    have hb := (continuousAt_factor (a := b) hab.ne).tendsto.isBigO_one ℝ
    have hc := (continuousAt_factor (a := c) (hab.trans hbc).ne).tendsto.isBigO_one ℝ
    have hO : kernel a b c =O[𝓝 a] factor a := by
      simpa only [← kernel_eq_factors, mul_one] using
        ((isBigO_refl (factor a) (𝓝 a)).mul hb).mul hc
    exact hO.integrableAtFilter hmeas (locallyIntegrable_factor a a)
  by_cases hxb : x = b
  · subst x
    have ha := (continuousAt_factor (a := a) hab.ne').tendsto.isBigO_one ℝ
    have hc := (continuousAt_factor (a := c) hbc.ne).tendsto.isBigO_one ℝ
    have hO : kernel a b c =O[𝓝 b] factor b := by
      simpa only [← kernel_eq_factors, one_mul, mul_one] using
        (ha.mul (isBigO_refl (factor b) (𝓝 b))).mul hc
    exact hO.integrableAtFilter hmeas (locallyIntegrable_factor b b)
  · have ha := (continuousAt_factor hxa).tendsto.isBigO_one ℝ
    have hb := (continuousAt_factor hxb).tendsto.isBigO_one ℝ
    have hO : kernel a b c =O[𝓝 x] factor c := by
      simpa only [← kernel_eq_factors, one_mul] using
        (ha.mul hb).mul (isBigO_refl (factor c) (𝓝 x))
    exact hO.integrableAtFilter hmeas (locallyIntegrable_factor c x)

private theorem factor_equivalent_atTop (a : ℝ) :
    factor a ~[atTop] (fun x : ℝ => |x| ^ (-(1/2 : ℝ))) := by
  have hid : (fun x : ℝ => x) ~[atTop] (fun x : ℝ => x) := IsEquivalent.refl
  have hshift : (fun x : ℝ => x-a) ~[atTop] (fun x : ℝ => x) := by
    simpa only [sub_eq_add_neg] using
      hid.add_const_of_norm_tendsto_atTop (c := -a) tendsto_norm_atTop_atTop
  have hleft : (fun x : ℝ => x-a) =ᶠ[atTop] (fun x : ℝ => |x-a|) := by
    filter_upwards [eventually_ge_atTop a] with x hx
    exact (abs_of_nonneg (sub_nonneg.mpr hx)).symm
  have hright : (fun x : ℝ => x) =ᶠ[atTop] (fun x : ℝ => |x|) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact (abs_of_nonneg hx).symm
  have h := (hshift.congr_left hleft).congr_right hright
  have hp := IsEquivalent.rpow (show (0 : ℝ → ℝ) ≤ fun x => |x| from fun x => abs_nonneg x)
    h (r := -(1/2 : ℝ))
  exact hp.congr_left (Eventually.of_forall fun x => (factor_eq_rpow a x).symm)

private theorem kernel_isBigO_atTop (a b c : ℝ) :
    kernel a b c =O[atTop] (fun x : ℝ => x ^ (-(3/2 : ℝ))) := by
  have h := ((factor_equivalent_atTop a).mul (factor_equivalent_atTop b)).mul
    (factor_equivalent_atTop c)
  apply h.isBigO.congr'
  · filter_upwards [] with x
    exact (kernel_eq_factors a b c x).symm
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    dsimp only [Pi.mul_apply]
    rw [abs_of_pos hx, ← Real.rpow_add hx, ← Real.rpow_add hx]
    norm_num

private theorem integrableAtTop_kernel (a b c : ℝ) :
    IntegrableAtFilter (kernel a b c) atTop volume := by
  apply (kernel_isBigO_atTop a b c).integrableAtFilter
    (kernel_measurable a b c).aestronglyMeasurable.stronglyMeasurableAtFilter
  exact integrableAtFilter_rpow_atTop_iff.mpr (by norm_num)

/-- The boundary kernel decays faster than the reciprocal radius on the
positive ray; this controls the vertical edges in Green's formula. -/
theorem tendsto_mul_kernel_atTop (a b c : ℝ) :
    Tendsto (fun x : ℝ => x * kernel a b c x) atTop (𝓝 0) := by
  have hO := (isBigO_refl (fun x : ℝ => x) atTop).mul (kernel_isBigO_atTop a b c)
  have hO' : (fun x : ℝ => x * kernel a b c x) =O[atTop]
      (fun x : ℝ => x ^ (-(1/2 : ℝ))) := by
    apply hO.congr'
    · exact Eventually.of_forall fun _ => rfl
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      change x * x ^ (-(3/2 : ℝ)) = x ^ (-(1/2 : ℝ))
      calc
        _ = x ^ ((1 : ℝ) + -(3/2 : ℝ)) := by rw [Real.rpow_add hx, Real.rpow_one]
        _ = _ := by norm_num
  exact hO'.trans_tendsto (tendsto_rpow_neg_atTop (by norm_num))

/-- The same reciprocal-radius decay on the negative ray. -/
theorem tendsto_mul_kernel_neg_atTop (a b c : ℝ) :
    Tendsto (fun x : ℝ => x * kernel a b c (-x)) atTop (𝓝 0) := by
  convert tendsto_mul_kernel_atTop (-a) (-b) (-c) using 1
  funext x
  have he (t : ℝ) : |-x-t| = |x-(-t)| := by
    rw [show -x-t = -(x-(-t)) by ring, abs_neg]
  simp only [kernel, he]

private theorem integrableAtBot_kernel (a b c : ℝ) :
    IntegrableAtFilter (kernel a b c) atBot volume := by
  have he := (Homeomorph.neg ℝ).measurableEmbedding.integrableAtFilter_map_iff
    (l := atBot) (μ := volume) (f := kernel (-a) (-b) (-c))
  have hmap : Filter.map (Homeomorph.neg ℝ) atBot = atTop := map_neg_atBot
  have hvol : Measure.map (Homeomorph.neg ℝ) volume = volume :=
    Measure.map_neg_eq_self volume
  rw [hmap, hvol] at he
  have h := he.mp (integrableAtTop_kernel (-a) (-b) (-c))
  convert h using 1
  funext x
  change kernel a b c x = kernel (-a) (-b) (-c) (-x)
  have he (t : ℝ) : |-x - (-t)| = |x-t| := by
    rw [show -x - (-t) = -(x-t) by ring, abs_neg]
  simp only [kernel, he]

/-- The boundary magnitude of the three-root cubic differential is
integrable on the whole real axis for every strictly ordered triple. -/
theorem integrable_kernel {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    Integrable (kernel a b c) :=
  integrable_iff_integrableAtFilter_atBot_atTop.mpr
    ⟨⟨integrableAtBot_kernel a b c, integrableAtTop_kernel a b c⟩,
      locallyIntegrable_kernel hab hbc⟩

/-- The finite interval between the first two roots has strictly positive
period; positivity is derived from the explicit kernel. -/
theorem integral_Ioo_pos {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    0 < ∫ x in Ioo a b, kernel a b c x := by
  have hs : Ioo a b ⊆ Function.support (kernel a b c) := by
    intro x hx
    exact (kernel_pos hx.1.ne' hx.2.ne (hx.2.trans hbc).ne).ne'
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall fun x => kernel_nonneg a b c x)
    (integrable_kernel hab hbc).integrableOn,
    inter_eq_self_of_subset_right hs, Real.volume_Ioo]
  exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)

end
end SlitCubicIntegrability
