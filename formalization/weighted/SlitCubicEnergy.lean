import SlitCubicBoundary
import SlitCubicArea
import SlitEnergyExhaustion
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# Energy from the actual cubic primitive

The Green field is `Re F * F'`.  Its antiholomorphic derivative is the
energy density; this computes the energy from actual boundary values and
decay, without assuming a rectangle uniformization or an area identity.
-/

namespace SlitCubicEnergy

open Set Filter Metric MeasureTheory Complex
open scoped Topology ComplexOrder ENNReal NNReal Interval

noncomputable section

def flux (F g : ℂ → ℂ) (z : ℂ) : ℂ := ((F z).re : ℂ) * g z

def fluxDerivative (F g h : ℂ → ℂ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  ((F z).re : ℂ) • (h z • (1 : ℂ →L[ℝ] ℂ)) +
    g z • (ofRealCLM.comp (reCLM.comp (g z • (1 : ℂ →L[ℝ] ℂ))))

theorem flux_hasFDerivAt {F g h : ℂ → ℂ} {z : ℂ}
    (hF : HasDerivAt F (g z) z) (hg : HasDerivAt g (h z) z) :
    HasFDerivAt (flux F g) (fluxDerivative F g h z) z := by
  change HasFDerivAt ((fun w => ((F w).re : ℂ)) * g) _ z
  simpa only [flux, fluxDerivative, Function.comp_def, ofRealCLM_apply,
    reCLM_apply, Pi.mul_apply] using
    (ofRealCLM.hasFDerivAt.comp z
      (reCLM.hasFDerivAt.comp z hF.complexToReal_fderiv)).mul
      hg.complexToReal_fderiv

theorem fluxDerivative_green (F g h : ℂ → ℂ) (z : ℂ) :
    I * fluxDerivative F g h z 1 - fluxDerivative F g h z I =
      I * (‖g z‖ ^ 2 : ℝ) := by
  apply Complex.ext <;>
    simp [fluxDerivative, ContinuousLinearMap.comp_apply,
      smul_eq_mul, Complex.sq_norm, Complex.normSq_apply] <;> ring

/-- Green's identity on every compact rectangle strictly above the real
axis, with the analytic energy density on the right. -/
theorem flux_rectangle {F g : ℂ → ℂ}
    (hF : ∀ z : ℂ, 0 < z.im → HasDerivAt F (g z) z)
    (hg : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ g z)
    {a b c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) :
    (∫ x : ℝ in a..b, flux F g (x + c * I)) -
        (∫ x : ℝ in a..b, flux F g (x + d * I)) +
        I * (∫ y : ℝ in c..d, flux F g (b + y * I)) -
        I * (∫ y : ℝ in c..d, flux F g (a + y * I)) =
      I * ((∫ x : ℝ in a..b, ∫ y : ℝ in c..d,
        ‖g (x + y * I)‖ ^ 2) : ℝ) := by
  let H := fluxDerivative F g (deriv g)
  have hpos : ∀ z ∈ ([[a, b]] ×ℂ [[c, d]]), 0 < z.im := by
    intro z hz
    exact hc.trans_le ((uIcc_of_le hcd ▸ hz.2).1)
  have hderiv : ∀ z : ℂ, 0 < z.im → HasFDerivAt (flux F g) (H z) z :=
    fun z hz => flux_hasFDerivAt (hF z hz) (hg z hz).hasDerivAt
  have hcont : ContinuousOn (flux F g) ([[a, b]] ×ℂ [[c, d]]) :=
    fun z hz => (hderiv z (hpos z hz)).continuousAt.continuousWithinAt
  have hi : IntegrableOn (fun z => I • H z 1 - H z I)
      ([[a, b]] ×ℂ [[c, d]]) := by
    have hce : ContinuousOn (fun z => I * (‖g z‖ ^ 2 : ℝ))
        ([[a, b]] ×ℂ [[c, d]]) := by
      have hcg : ContinuousOn g ([[a, b]] ×ℂ [[c, d]]) :=
        fun z hz => (hg z (hpos z hz)).continuousAt.continuousWithinAt
      exact continuousOn_const.mul (Complex.continuous_ofReal.continuousOn.comp
        (hcg.norm.pow 2) (mapsTo_univ _ _))
    simpa only [H, smul_eq_mul, fluxDerivative_green] using
      hce.integrableOn_compact (isCompact_uIcc.reProdIm isCompact_uIcc)
  have he := integral_boundary_rect_of_continuousOn_of_hasFDerivAt_real
    (flux F g) H (a + c * I) (b + d * I) (by simpa using hcont)
    (by
      intro z hz
      apply hderiv z
      simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
        mul_one, sub_zero, add_zero, add_im, mul_im, zero_mul, zero_add,
        min_eq_left hcd, max_eq_right hcd] at hz
      exact hc.trans hz.2.1)
    (by simpa using hi)
  simpa only [H, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero,
    mul_one, sub_zero, add_zero, add_im, mul_im, zero_mul, zero_add, smul_eq_mul,
    fluxDerivative_green, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_ofReal] using he

/-- Horizontal sides may move towards the real boundary or towards
infinity while the horizontal cutoffs exhaust the line. -/
theorem tendsto_horizontal_cutoff {r : ℕ → ℝ}
    (hr : ∀ n, 0 ≤ r n) (hrlim : Tendsto r atTop atTop)
    {f : ℕ → ℝ → ℂ} {f₀ : ℝ → ℂ} {k : ℝ → ℝ}
    (hm : ∀ n, AEStronglyMeasurable (f n)) (hk : Integrable k)
    (hb : ∀ n, ∀ᵐ x, ‖f n x‖ ≤ k x)
    (hf : ∀ᵐ x, Tendsto (fun n => f n x) atTop (𝓝 (f₀ x))) :
    Tendsto (fun n => ∫ x in -(r n)..r n, f n x) atTop (𝓝 (∫ x, f₀ x)) := by
  have hlim := tendsto_integral_of_dominated_convergence k
    (F := fun n => (Ioc (-(r n)) (r n)).indicator (f n))
    (fun n => (hm n).indicator measurableSet_Ioc) hk
    (fun n => (hb n).mono fun x hx => by
      by_cases hmem : x ∈ Ioc (-(r n)) (r n)
      · simpa only [indicator_of_mem hmem] using hx
      · simpa only [indicator_of_notMem hmem, norm_zero] using
          (norm_nonneg (f n x)).trans hx)
    (hf.mono fun x hx => hx.congr' (by
      filter_upwards [hrlim.eventually (eventually_gt_atTop (-x)),
        hrlim.eventually (eventually_ge_atTop x)] with n hn₁ hn₂
      exact (indicator_of_mem (show x ∈ Ioc (-(r n)) (r n) from
        ⟨by linarith, hn₂⟩) _).symm))
  apply hlim.congr'
  filter_upwards [] with n
  rw [integral_indicator measurableSet_Ioc, intervalIntegral.integral_of_le]
  linarith [hr n]

/-- A uniform bound on each vertical side, with its height accounted for,
forces the side integral to vanish. -/
theorem tendsto_vertical_side {r : ℕ → ℝ} (hr : ∀ n, 1 ≤ r n)
    {H : ℂ → ℂ} {x k : ℕ → ℝ}
    (hk : ∀ n, 0 ≤ k n)
    (hb : ∀ᶠ n in atTop, ∀ y ∈ Icc (r n)⁻¹ (r n), ‖H (x n + y * I)‖ ≤ k n)
    (hlim : Tendsto (fun n => r n * k n) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ y in (r n)⁻¹..r n, H (x n + y * I)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ hlim
  filter_upwards [hb] with n hbn
  have hr0 : 0 < r n := lt_of_lt_of_le zero_lt_one (hr n)
  have hir : (r n)⁻¹ ≤ r n := (inv_le_one_of_one_le₀ (hr n)).trans (hr n)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (r n)⁻¹) (b := r n) (f := fun y => H (x n + y * I))
    (fun y hy => hbn y ⟨(uIoc_of_le hir ▸ hy).1.le, (uIoc_of_le hir ▸ hy).2⟩)
  rw [abs_of_nonneg (sub_nonneg.mpr hir)] at h
  calc
    ‖∫ y in (r n)⁻¹..r n, H (x n + y * I)‖ ≤ k n * (r n - (r n)⁻¹) := h
    _ ≤ r n * k n := by
      calc
        k n * (r n - (r n)⁻¹) ≤ k n * r n :=
          mul_le_mul_of_nonneg_left (sub_le_self _ (inv_nonneg.mpr hr0.le)) (hk n)
        _ = r n * k n := mul_comm _ _

open SlitCubicCalibration

def cubicFlux (a b c : ℝ) : ℂ → ℂ :=
  flux (tail a b c) (fun z => -differential a b c z)

theorem cubicFlux_continuous_upper {a b c : ℝ}
    (hi : Integrable (realDensity a b c)) : ContinuousOn (cubicFlux a b c) upper := by
  intro z hz
  have hd := (differential_differentiableOn a b c z hz).differentiableAt
    (upper_open.mem_nhds hz)
  exact (flux_hasFDerivAt (tail_hasDerivAt hi hz) hd.neg.hasDerivAt).continuousAt.continuousWithinAt

theorem cubicFlux_slice_continuous {a b c y : ℝ}
    (hi : Integrable (realDensity a b c)) (hy : 0 < y) :
    Continuous (fun x : ℝ => cubicFlux a b c (x + y * I)) := by
  apply (cubicFlux_continuous_upper hi).comp_continuous (by fun_prop)
  intro x
  simpa [upper] using hy

private theorem mass_nonneg (a b c : ℝ) : 0 ≤ ∫ x, realDensity a b c x :=
  integral_nonneg (SlitCubicIntegrability.kernel_nonneg a b c)

theorem cubicFlux_horizontal_bound {a b c x y : ℝ}
    (hi : Integrable (realDensity a b c)) (hy : 0 ≤ y)
    (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) :
    ‖cubicFlux a b c (x + y * I)‖ ≤
      (∫ t, realDensity a b c t) * realDensity a b c x := by
  unfold cubicFlux flux
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
  apply mul_le_mul
    ((Complex.abs_re_le_norm _).trans (tail_norm_le hi (by simpa [closedUpper] using hy)))
    (differential_horizontal_bound hy hxa hxb hxc) (norm_nonneg _) (mass_nonneg a b c)

theorem cubicFlux_horizontal_bound_ae {a b c y : ℝ}
    (hi : Integrable (realDensity a b c)) (hy : 0 ≤ y) :
    ∀ᵐ x : ℝ, ‖cubicFlux a b c (x + y * I)‖ ≤
      (∫ t, realDensity a b c t) * realDensity a b c x := by
  filter_upwards [volume.ae_ne a, volume.ae_ne b, volume.ae_ne c] with x ha hb hc
  exact cubicFlux_horizontal_bound hi hy ha hb hc

theorem cubicFlux_bottom_tendsto {a b c : ℝ}
    (hi : Integrable (realDensity a b c)) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop atTop)
    (hir : Tendsto (fun n => (r n)⁻¹) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x in -(r n)..r n,
      cubicFlux a b c (x + (r n)⁻¹ * I)) atTop
      (𝓝 (∫ x : ℝ, cubicFlux a b c x)) := by
  apply tendsto_horizontal_cutoff (fun n => (hr n).le) hrlim
    (fun n => (cubicFlux_slice_continuous hi (inv_pos.mpr (hr n))).aestronglyMeasurable)
    (hi.const_mul _) (fun n => cubicFlux_horizontal_bound_ae hi (inv_pos.mpr (hr n)).le)
  filter_upwards [volume.ae_ne a, volume.ae_ne b, volume.ae_ne c] with x ha hb hc
  have hzlim : Tendsto (fun n => (x : ℂ) + ((r n)⁻¹ : ℂ) * I) atTop (𝓝 (x : ℂ)) := by
    simpa using tendsto_const_nhds.add
      ((Complex.continuous_ofReal.tendsto 0).comp hir |>.mul_const I)
  have htc : Tendsto (tail a b c) (𝓝[closedUpper] (x : ℂ))
      (𝓝 (tail a b c (x : ℂ))) :=
    tail_continuousOn_closedUpper hi (x : ℂ) (by simp [closedUpper])
  have hzn : Tendsto (fun n => (x : ℂ) + ((r n)⁻¹ : ℂ) * I) atTop
      (𝓝[closedUpper] (x : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzlim, Eventually.of_forall (fun n => by
      simpa [closedUpper] using (inv_pos.mpr (hr n)).le)⟩
  have ht := htc.comp hzn
  have hd := (differential_continuousAt (a := a) (b := b) (c := c)
    (z := (x : ℂ)) (by simp) (by simpa using ha) (by simpa using hb)
    (by simpa using hc)).tendsto.comp hzlim
  simpa only [cubicFlux, flux, Function.comp_apply, Complex.ofReal_inv] using
    ((Complex.continuous_ofReal.tendsto _).comp
      ((Complex.continuous_re.tendsto _).comp ht)).mul hd.neg

theorem cubicFlux_top_tendsto {a b c : ℝ}
    (hi : Integrable (realDensity a b c)) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (hrlim : Tendsto r atTop atTop) :
    Tendsto (fun n => ∫ x in -(r n)..r n,
      cubicFlux a b c (x + r n * I)) atTop (𝓝 0) := by
  have h := tendsto_horizontal_cutoff (fun n => (hr n).le) hrlim
    (fun n => (cubicFlux_slice_continuous hi (hr n)).aestronglyMeasurable)
    (hi.const_mul _) (fun n => cubicFlux_horizontal_bound_ae hi (hr n).le)
    (f₀ := fun _ => 0) (Eventually.of_forall (fun x => by
      have ht := (tail_vertical_tendsto_atTop hi x).comp hrlim
      have hd := (differential_vertical_tendsto_atTop a b c x).comp hrlim
      simpa [cubicFlux, flux] using
        ((Complex.continuous_ofReal.tendsto _).comp
          ((Complex.continuous_re.tendsto _).comp ht)).mul hd.neg))
  simpa only [integral_zero] using h

theorem cubicFlux_side_tendsto {a b c : ℝ}
    (hi : Integrable (realDensity a b c)) {r x : ℕ → ℝ}
    (hr : ∀ n, 1 ≤ r n)
    (ha : ∀ᶠ n in atTop, x n ≠ a) (hb : ∀ᶠ n in atTop, x n ≠ b)
    (hc : ∀ᶠ n in atTop, x n ≠ c)
    (hdecay : Tendsto (fun n => r n * realDensity a b c (x n)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ y in (r n)⁻¹..r n,
      cubicFlux a b c (x n + y * I)) atTop (𝓝 0) := by
  apply tendsto_vertical_side hr
    (k := fun n => (∫ t, realDensity a b c t) * realDensity a b c (x n))
    (fun n => mul_nonneg (mass_nonneg a b c)
      (SlitCubicIntegrability.kernel_nonneg a b c (x n)))
  · filter_upwards [ha, hb, hc] with n hna hnb hnc
    intro y hy
    apply cubicFlux_horizontal_bound hi _ hna hnb hnc
    exact (inv_nonneg.mpr (zero_le_one.trans (hr n))).trans hy.1
  · have hJ : Tendsto (fun _ : ℕ => ∫ t, realDensity a b c t) atTop
        (𝓝 (∫ t, realDensity a b c t)) := tendsto_const_nhds
    simpa only [mul_zero, mul_left_comm] using hJ.mul hdecay

theorem differential_sq_norm {a b c : ℝ} {z : ℂ} (hz : 0 ≤ z.im) :
    ‖differential a b c z‖ ^ 2 = SlitCubicArea.densitySq a b c z := by
  rw [differential_norm hz]
  simp only [SlitCubicArea.densitySq, div_pow, one_pow, mul_pow, Real.sq_sqrt (norm_nonneg _)]

theorem cubicFlux_real_integrable {a b c : ℝ}
    (hi : Integrable (realDensity a b c)) :
    Integrable (fun x : ℝ => cubicFlux a b c x) := by
  have ht : Continuous (fun x : ℝ => tail a b c (x : ℂ)) :=
    (tail_continuousOn_closedUpper hi).comp_continuous Complex.continuous_ofReal
      (fun x => by simp [closedUpper])
  have hm : Measurable (fun x : ℝ => cubicFlux a b c x) :=
    (Complex.continuous_ofReal.measurable.comp
      (Complex.continuous_re.measurable.comp ht.measurable)).mul
      ((differential_measurable a b c).comp Complex.continuous_ofReal.measurable).neg
  exact (hi.const_mul _).mono' hm.aestronglyMeasurable (by
    simpa using cubicFlux_horizontal_bound_ae hi (show (0 : ℝ) ≤ 0 by rfl))

theorem cubicFlux_real_integral_im {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    (∫ x : ℝ, cubicFlux a b c x).im =
      SlitCubicBoundary.period a b c * ∫ x in Ioo b c, realDensity a b c x := by
  have hIm := Complex.imCLM.integral_comp_comm
    (cubicFlux_real_integrable (realDensity_integrable hab hbc))
  simp only [Complex.imCLM_apply] at hIm
  rw [← hIm]
  simpa only [cubicFlux, flux, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero] using
      SlitCubicBoundary.integral_boundary_flux hab hbc

private theorem energy_eq_of_rectangular_limit {a b c E : ℝ}
    (hab : a < b) (hbc : b < c) {r : ℕ → ℝ}
    (hr : ∀ n, 1 ≤ r n) (hrlim : Tendsto r atTop atTop)
    (hE : Tendsto (fun n => ∫ x in -(r n)..r n, ∫ y in (r n)⁻¹..r n,
      SlitCubicArea.densitySq a b c (x + y * I)) atTop (𝓝 E)) :
    E = SlitCubicBoundary.period a b c * ∫ x in Ioo b c, realDensity a b c x := by
  let hi := realDensity_integrable hab hbc
  have hr0 : ∀ n, 0 < r n := fun n => zero_lt_one.trans_le (hr n)
  have hir := tendsto_inv_atTop_zero.comp hrlim
  have hbottom := cubicFlux_bottom_tendsto hi hr0 hrlim hir
  have htop := cubicFlux_top_tendsto hi hr0 hrlim
  have hne (t : ℝ) : ∀ᶠ n in atTop, r n ≠ t :=
    hrlim.eventually (eventually_ne_atTop t)
  have hnne (t : ℝ) : ∀ᶠ n in atTop, -(r n) ≠ t := by
    filter_upwards [hrlim.eventually (eventually_gt_atTop (-t))] with n hn
    linarith
  have hright := cubicFlux_side_tendsto hi hr (hne a) (hne b) (hne c)
    ((SlitCubicIntegrability.tendsto_mul_kernel_atTop a b c).comp hrlim)
  have hleft := cubicFlux_side_tendsto hi hr (hnne a) (hnne b) (hnne c)
    ((SlitCubicIntegrability.tendsto_mul_kernel_neg_atTop a b c).comp hrlim)
  have hI : Tendsto (fun _ : ℕ => I) atTop (𝓝 I) := tendsto_const_nhds
  have hboundary : Tendsto (fun n =>
      (∫ x in -(r n)..r n, cubicFlux a b c (x + (r n)⁻¹ * I)) -
        (∫ x in -(r n)..r n, cubicFlux a b c (x + r n * I)) +
        I * (∫ y in (r n)⁻¹..r n, cubicFlux a b c (r n + y * I)) -
        I * (∫ y in (r n)⁻¹..r n, cubicFlux a b c (-(r n) + y * I)))
      atTop (𝓝 (∫ x : ℝ, cubicFlux a b c x)) := by
    simpa only [sub_zero, mul_zero, add_zero, Complex.ofReal_neg] using
      ((hbottom.sub htop).add (hI.mul hright)).sub (hI.mul hleft)
  have henergy := hI.mul ((Complex.continuous_ofReal.tendsto E).comp hE)
  have hrectangle (n : ℕ) :
      (∫ x in -(r n)..r n, cubicFlux a b c (x + (r n)⁻¹ * I)) -
        (∫ x in -(r n)..r n, cubicFlux a b c (x + r n * I)) +
        I * (∫ y in (r n)⁻¹..r n, cubicFlux a b c (r n + y * I)) -
        I * (∫ y in (r n)⁻¹..r n, cubicFlux a b c (-(r n) + y * I)) =
      I * ((∫ x in -(r n)..r n, ∫ y in (r n)⁻¹..r n,
        SlitCubicArea.densitySq a b c (x + y * I)) : ℝ) := by
    have horder : (r n)⁻¹ ≤ r n := (inv_le_one_of_one_le₀ (hr n)).trans (hr n)
    have hrec := flux_rectangle
      (F := tail a b c) (g := fun z => -differential a b c z)
      (fun z hz => tail_hasDerivAt hi hz)
      (fun z hz => ((differential_differentiableOn a b c z hz).differentiableAt
        (upper_open.mem_nhds hz)).neg)
      (a := -(r n)) (b := r n) (inv_pos.mpr (hr0 n)) horder
    have he : (∫ x in -(r n)..r n, ∫ y in (r n)⁻¹..r n,
        ‖-differential a b c (x + y * I)‖ ^ 2) =
        (∫ x in -(r n)..r n, ∫ y in (r n)⁻¹..r n,
          SlitCubicArea.densitySq a b c (x + y * I)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      apply intervalIntegral.integral_congr
      intro y hy
      dsimp only
      rw [norm_neg, differential_sq_norm]
      simpa using (inv_nonneg.mpr (hr0 n).le).trans ((uIcc_of_le horder ▸ hy).1)
    rw [he] at hrec
    simpa only [cubicFlux, Complex.ofReal_neg] using hrec
  have heq := tendsto_nhds_unique hboundary
    (henergy.congr' (Eventually.of_forall fun n => (hrectangle n).symm))
  have him := congrArg Complex.im heq
  rw [cubicFlux_real_integral_im hab hbc] at him
  simpa using him.symm

/-- Exact energy of the actual cubic differential on the upper
half-plane.  The only assumptions are the strict order of its three real
branch points.  The energy is the product of the two finite real periods. -/
theorem integral_upper_densitySq {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    (∫ z in upper, SlitCubicArea.densitySq a b c z) =
      SlitCubicBoundary.period a b c * ∫ x in Ioo b c, realDensity a b c x := by
  apply energy_eq_of_rectangular_limit hab hbc SlitEnergyExhaustion.one_le_radius
    SlitEnergyExhaustion.radius_tendsto_atTop
  have hP := SlitEnergyExhaustion.integrable_complex_pullback
    (SlitCubicArea.integrable_densitySq hab hbc)
  have hlim := (SlitEnergyExhaustion.tendsto_integral_box hP).congr'
    (Eventually.of_forall fun n =>
      (SlitEnergyExhaustion.intervalIntegral_eq_integral_box hP n).symm)
  simpa only [SlitEnergyExhaustion.integral_upperHalfPlane_complex_pullback, upper] using hlim

theorem integral_upper_differential_sq {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    (∫ z in upper, ‖differential a b c z‖ ^ 2) =
      SlitCubicBoundary.period a b c * ∫ x in Ioo b c, realDensity a b c x := by
  rw [← integral_upper_densitySq hab hbc]
  exact setIntegral_congr_fun upper_open.measurableSet
    (fun z hz => differential_sq_norm hz.le)

end
end SlitCubicEnergy
