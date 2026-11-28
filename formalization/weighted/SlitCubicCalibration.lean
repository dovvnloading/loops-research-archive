import SlitCubicIntegrability
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-!
# The cubic differential for the left slit extremal problem

This file constructs the holomorphic differential and an actual primitive
on the upper half-plane.  Rectangle uniformization, boundary values of the
primitive, and the complete path-family calibration are separate claims.
-/

namespace SlitCubicCalibration

open Set Filter Function MeasureTheory
open scoped Topology ComplexOrder
noncomputable section

def upper : Set ℂ := {z | 0 < z.im}

theorem upper_open : IsOpen upper := isOpen_lt continuous_const Complex.continuous_im

theorem upper_convex : Convex ℝ upper := convex_halfSpace_im_gt 0

/-- Principal upper-side square root, continuously filled on the real line. -/
def upperRoot (t : ℝ) (z : ℂ) : ℂ :=
  (Real.sqrt ((‖z-(t:ℂ)‖ + z.re-t)/2) : ℂ) +
    (Real.sqrt ((‖z-(t:ℂ)‖ - (z.re-t))/2) : ℂ)*Complex.I

theorem upperRoot_continuous (t : ℝ) : Continuous (upperRoot t) := by
  unfold upperRoot
  fun_prop

theorem upperRoot_eq_sqrt {t : ℝ} {z : ℂ} (hz : 0 ≤ z.im) :
    upperRoot t z = Complex.sqrt (z-(t:ℂ)) := by
  rw [Complex.sqrt_eq_real_add_ite]
  simp [upperRoot, hz, sub_eq_add_neg, add_assoc]

theorem sqrt_sq (z : ℂ) : (Complex.sqrt z)^2 = z := by
  rw [Complex.sqrt, ← Complex.cpow_mul_nat]
  norm_num

theorem upperRoot_sq {t : ℝ} {z : ℂ} (hz : 0 ≤ z.im) :
    (upperRoot t z)^2 = z-(t:ℂ) := by
  rw [upperRoot_eq_sqrt hz, sqrt_sq]

theorem upperRoot_ne_zero {t : ℝ} {z : ℂ} (hz : 0 ≤ z.im) (hne : z ≠ (t:ℂ)) :
    upperRoot t z ≠ 0 := by
  intro hzero
  have h := upperRoot_sq (t := t) hz
  rw [hzero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
  exact hne (sub_eq_zero.mp h.symm)

theorem upperRoot_differentiableAt {t : ℝ} {z : ℂ} (hz : z ∈ upper) :
    DifferentiableAt ℂ (upperRoot t) z := by
  have hslit : z-(t:ℂ) ∈ Complex.slitPlane := by
    right
    simpa using (ne_of_gt hz : z.im ≠ 0)
  have hd := (Complex.differentiableAt_sqrt hslit).comp z
    (differentiableAt_id.sub_const (t:ℂ))
  apply hd.congr_of_eventuallyEq
  filter_upwards [upper_open.mem_nhds hz] with w hw
  exact upperRoot_eq_sqrt (t := t) (le_of_lt hw)

/-- The upper-side cubic Schwarz--Christoffel differential. -/
def differential (a b c : ℝ) (z : ℂ) : ℂ :=
  (upperRoot a z * upperRoot b z * upperRoot c z)⁻¹

theorem differential_differentiableOn (a b c : ℝ) :
    DifferentiableOn ℂ (differential a b c) upper := by
  intro z hz
  have hne (t : ℝ) : z ≠ (t:ℂ) := by
    intro heq
    have := congrArg Complex.im heq
    simpa using (ne_of_gt hz : z.im ≠ 0) this
  exact (((upperRoot_differentiableAt (t := a) hz).mul
    (upperRoot_differentiableAt (t := b) hz)).mul
    (upperRoot_differentiableAt (t := c) hz)).inv
      (mul_ne_zero (mul_ne_zero (upperRoot_ne_zero hz.le (hne a))
        (upperRoot_ne_zero hz.le (hne b))) (upperRoot_ne_zero hz.le (hne c)))
      |>.differentiableWithinAt

theorem exists_primitive (a b c : ℝ) :
    ∃ F : ℂ → ℂ, F Complex.I = 0 ∧
      ∀ z ∈ upper, HasDerivAt F (differential a b c z) z := by
  obtain ⟨G,hG⟩ := upper_convex.exists_forall_hasDerivWithinAt
    (differential_differentiableOn a b c)
  refine ⟨fun z => G z-G Complex.I, sub_self _, ?_⟩
  intro z hz
  exact ((hG z hz).hasDerivAt (upper_open.mem_nhds hz)).sub_const _


theorem upperRoot_norm {t : ℝ} {z : ℂ} (hz : 0 ≤ z.im) :
    ‖upperRoot t z‖ = Real.sqrt ‖z-(t:ℂ)‖ := by
  have h := congrArg norm (upperRoot_sq (t := t) hz)
  rw [norm_pow] at h
  rw [← h, Real.sqrt_sq (norm_nonneg _)]

theorem differential_norm {a b c : ℝ} {z : ℂ} (hz : 0 ≤ z.im) :
    ‖differential a b c z‖ =
      1 / (Real.sqrt ‖z-(a:ℂ)‖ * Real.sqrt ‖z-(b:ℂ)‖ *
        Real.sqrt ‖z-(c:ℂ)‖) := by
  simp only [differential, norm_inv, norm_mul, upperRoot_norm hz, one_div]

theorem upperRoot_real_right {t x : ℝ} (hx : t ≤ x) :
    upperRoot t (x:ℂ) = (Real.sqrt (x-t) : ℂ) := by
  have hxt : 0 ≤ x-t := sub_nonneg.mpr hx
  simp only [upperRoot, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    Complex.ofReal_re, abs_of_nonneg hxt]
  have h1 : (x-t+x-t)/2 = x-t := by ring
  have h0 : (x-t-(x-t))/2 = 0 := by ring
  rw [h1,h0]
  simp

theorem upperRoot_real_left {t x : ℝ} (hx : x ≤ t) :
    upperRoot t (x:ℂ) = (Real.sqrt (t-x) : ℂ)*Complex.I := by
  have hxt : x-t ≤ 0 := sub_nonpos.mpr hx
  simp only [upperRoot, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    Complex.ofReal_re, abs_of_nonpos hxt]
  have h0 : (-(x-t)+x-t)/2 = 0 := by ring
  have h1 : (-(x-t)-(x-t))/2 = t-x := by ring
  rw [h0,h1]
  simp

def realDensity (a b c x : ℝ) : ℝ :=
  1 / (Real.sqrt |x-a| * Real.sqrt |x-b| * Real.sqrt |x-c|)

theorem norm_differential_real (a b c x : ℝ) :
    ‖differential a b c (x:ℂ)‖ = realDensity a b c x := by
  rw [differential_norm (by simp)]
  simp [realDensity, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

theorem differential_real_left {a b c x : ℝ} (hxa : x ≤ a)
    (hxb : x ≤ b) (hxc : x ≤ c) :
    differential a b c (x:ℂ) = (realDensity a b c x : ℂ)*Complex.I := by
  rw [differential, upperRoot_real_left hxa, upperRoot_real_left hxb,
    upperRoot_real_left hxc]
  have hprod : (Real.sqrt (a-x):ℂ)*Complex.I * ((Real.sqrt (b-x):ℂ)*Complex.I) *
      ((Real.sqrt (c-x):ℂ)*Complex.I) =
      -((Real.sqrt (a-x):ℂ)*(Real.sqrt (b-x):ℂ)*(Real.sqrt (c-x):ℂ))*Complex.I := by
    calc
      _ = ((Real.sqrt (a-x):ℂ)*(Real.sqrt (b-x):ℂ)*(Real.sqrt (c-x):ℂ))*
        (Complex.I^2*Complex.I) := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  rw [hprod, mul_inv_rev, inv_neg, Complex.inv_I]
  simp only [realDensity, abs_of_nonpos (sub_nonpos.mpr hxa),
    abs_of_nonpos (sub_nonpos.mpr hxb), abs_of_nonpos (sub_nonpos.mpr hxc),
    neg_sub, one_div]
  push_cast
  ring

theorem differential_real_first {a b c x : ℝ} (hax : a ≤ x)
    (hxb : x ≤ b) (hxc : x ≤ c) :
    differential a b c (x:ℂ) = -(realDensity a b c x : ℂ) := by
  rw [differential, upperRoot_real_right hax, upperRoot_real_left hxb,
    upperRoot_real_left hxc]
  have hprod : (Real.sqrt (x-a):ℂ)*((Real.sqrt (b-x):ℂ)*Complex.I) *
      ((Real.sqrt (c-x):ℂ)*Complex.I) =
      -((Real.sqrt (x-a):ℂ)*(Real.sqrt (b-x):ℂ)*(Real.sqrt (c-x):ℂ)) := by
    calc
      _ = ((Real.sqrt (x-a):ℂ)*(Real.sqrt (b-x):ℂ)*(Real.sqrt (c-x):ℂ))*
        Complex.I^2 := by ring
      _ = _ := by rw [Complex.I_sq]; ring
  rw [hprod, inv_neg]
  simp [realDensity, abs_of_nonneg (sub_nonneg.mpr hax),
    abs_of_nonpos (sub_nonpos.mpr hxb), abs_of_nonpos (sub_nonpos.mpr hxc), neg_sub]

theorem differential_real_gap {a b c x : ℝ} (hax : a ≤ x)
    (hbx : b ≤ x) (hxc : x ≤ c) :
    differential a b c (x:ℂ) = -(realDensity a b c x : ℂ)*Complex.I := by
  rw [differential, upperRoot_real_right hax, upperRoot_real_right hbx,
    upperRoot_real_left hxc]
  simp only [mul_assoc, mul_inv_rev, Complex.inv_I]
  simp only [realDensity, abs_of_nonneg (sub_nonneg.mpr hax),
    abs_of_nonneg (sub_nonneg.mpr hbx), abs_of_nonpos (sub_nonpos.mpr hxc),
    neg_sub, Complex.ofReal_mul, one_div,
    mul_inv_rev]
  push_cast
  ring

theorem differential_real_right {a b c x : ℝ} (hax : a ≤ x)
    (hbx : b ≤ x) (hcx : c ≤ x) :
    differential a b c (x:ℂ) = (realDensity a b c x : ℂ) := by
  rw [differential, upperRoot_real_right hax, upperRoot_real_right hbx,
    upperRoot_real_right hcx]
  simp [realDensity, abs_of_nonneg (sub_nonneg.mpr hax),
    abs_of_nonneg (sub_nonneg.mpr hbx), abs_of_nonneg (sub_nonneg.mpr hcx)]

/-- The only exceptional real parameters are the three branch points,
where the real-valued inverse is conventionally zero. -/
theorem differential_horizontal_bound {a b c x y : ℝ}
    (hy : 0 ≤ y) (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) :
    ‖differential a b c ((x:ℂ)+(y:ℂ)*Complex.I)‖ ≤ realDensity a b c x := by
  rw [differential_norm (by simpa using hy)]
  have hb (t : ℝ) : Real.sqrt |x-t| ≤
      Real.sqrt ‖(x:ℂ)+(y:ℂ)*Complex.I-(t:ℂ)‖ := by
    apply Real.sqrt_le_sqrt
    simpa using Complex.abs_re_le_norm ((x:ℂ)+(y:ℂ)*Complex.I-(t:ℂ))
  have hp : 0 < Real.sqrt |x-a| * Real.sqrt |x-b| * Real.sqrt |x-c| := by
    exact mul_pos (mul_pos (Real.sqrt_pos.2 (abs_pos.2 (sub_ne_zero.mpr hxa)))
      (Real.sqrt_pos.2 (abs_pos.2 (sub_ne_zero.mpr hxb))))
      (Real.sqrt_pos.2 (abs_pos.2 (sub_ne_zero.mpr hxc)))
  apply one_div_le_one_div_of_le hp
  exact mul_le_mul (mul_le_mul (hb a) (hb b) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (hb c) (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))


theorem differential_measurable (a b c : ℝ) : Measurable (differential a b c) := by
  exact (((upperRoot_continuous a).measurable.mul (upperRoot_continuous b).measurable).mul
    (upperRoot_continuous c).measurable).inv

theorem differential_continuousAt {a b c : ℝ} {z : ℂ} (hz : 0 ≤ z.im)
    (hza : z ≠ (a:ℂ)) (hzb : z ≠ (b:ℂ)) (hzc : z ≠ (c:ℂ)) :
    ContinuousAt (differential a b c) z := by
  exact (((upperRoot_continuous a).continuousAt.mul
    (upperRoot_continuous b).continuousAt).mul
    (upperRoot_continuous c).continuousAt).inv₀
      (mul_ne_zero (mul_ne_zero (upperRoot_ne_zero hz hza)
        (upperRoot_ne_zero hz hzb)) (upperRoot_ne_zero hz hzc))

def closedUpper : Set ℂ := {z | 0 ≤ z.im}

theorem realDensity_integrable {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    Integrable (realDensity a b c) := SlitCubicIntegrability.integrable_kernel hab hbc

/-- The horizontal tail, defined also at all three boundary branch points. -/
def tailIntegrand (a b c : ℝ) (z : ℂ) : ℝ → ℂ :=
  (Ioi z.re).indicator (fun t => differential a b c ((t:ℂ)+(z.im:ℂ)*Complex.I))

def tail (a b c : ℝ) (z : ℂ) : ℂ := ∫ t : ℝ, tailIntegrand a b c z t

theorem tailIntegrand_measurable (a b c : ℝ) (z : ℂ) :
    Measurable (tailIntegrand a b c z) := by
  exact ((differential_measurable a b c).comp
    (Complex.measurable_ofReal.add measurable_const)).indicator measurableSet_Ioi

private theorem ae_real_ne (a : ℝ) : ∀ᵐ t : ℝ, t ≠ a := by
  exact volume.ae_ne a

theorem differential_horizontal_bound_ae (a b c : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    ∀ᵐ t : ℝ, ‖differential a b c ((t:ℂ)+(y:ℂ)*Complex.I)‖ ≤ realDensity a b c t := by
  filter_upwards [ae_real_ne a, ae_real_ne b, ae_real_ne c] with t ha hb hc
  exact differential_horizontal_bound hy ha hb hc

theorem tailIntegrand_bound_ae (a b c : ℝ) {z : ℂ} (hz : z ∈ closedUpper) :
    ∀ᵐ t : ℝ, ‖tailIntegrand a b c z t‖ ≤ realDensity a b c t := by
  filter_upwards [differential_horizontal_bound_ae a b c hz] with t ht
  exact (norm_indicator_le_norm_self (s := Ioi z.re)
    (f := fun t => differential a b c ((t:ℂ)+(z.im:ℂ)*Complex.I)) (a := t)).trans ht

theorem integrable_tailIntegrand {a b c : ℝ}
    (hi : Integrable (realDensity a b c)) {z : ℂ} (hz : z ∈ closedUpper) :
    Integrable (tailIntegrand a b c z) := by
  exact hi.mono' (tailIntegrand_measurable a b c z).aestronglyMeasurable
    (tailIntegrand_bound_ae a b c hz)

private theorem tailIntegrand_continuousAt {a b c t : ℝ} {z : ℂ}
    (hz : z ∈ closedUpper) (ha : t ≠ a) (hb : t ≠ b) (hc : t ≠ c)
    (ht : t ≠ z.re) : ContinuousAt (fun w => tailIntegrand a b c w t) z := by
  have hn (u : ℝ) (hu : t ≠ u) : (t:ℂ)+(z.im:ℂ)*Complex.I ≠ (u:ℂ) := by
    intro heq
    exact hu (by simpa using congrArg Complex.re heq)
  have hcont : ContinuousAt (fun w : ℂ =>
      differential a b c ((t:ℂ)+(w.im:ℂ)*Complex.I)) z := by
    exact (differential_continuousAt (by simpa [closedUpper] using hz) (hn a ha) (hn b hb) (hn c hc)).comp
      (f := fun w : ℂ => (t:ℂ)+(w.im:ℂ)*Complex.I) (by fun_prop)
  rcases lt_or_gt_of_ne ht with ht | ht
  · apply (continuousAt_const (y := (0:ℂ))).congr_of_eventuallyEq
    filter_upwards [((isOpen_lt continuous_const Complex.continuous_re).mem_nhds ht)] with w hw
    simp [tailIntegrand, not_lt.mpr hw.le]
  · apply hcont.congr_of_eventuallyEq
    filter_upwards [((isOpen_lt Complex.continuous_re continuous_const).mem_nhds ht)] with w hw
    simp [tailIntegrand, hw]

/-- A single integrable boundary majorant gives continuity all the way to
all boundary points, including the three square-root singularities. -/
theorem tail_continuousOn_closedUpper {a b c : ℝ}
    (hi : Integrable (realDensity a b c)) : ContinuousOn (tail a b c) closedUpper := by
  intro z hz
  unfold ContinuousWithinAt tail
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence (realDensity a b c)
  · exact Eventually.of_forall (fun w => (tailIntegrand_measurable a b c w).aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with w hw
    exact tailIntegrand_bound_ae a b c hw
  · exact hi
  · filter_upwards [ae_real_ne a, ae_real_ne b, ae_real_ne c, ae_real_ne z.re] with t ha hb hc ht
    exact (tailIntegrand_continuousAt hz ha hb hc ht).tendsto.mono_left nhdsWithin_le_nhds

/-- The same majorant bounds the complete constructed potential, including
its boundary values. -/
theorem tail_norm_le {a b c : ℝ} (hi : Integrable (realDensity a b c))
    {z : ℂ} (hz : z ∈ closedUpper) :
    ‖tail a b c z‖ ≤ ∫ t : ℝ, realDensity a b c t := by
  exact norm_integral_le_of_norm_le hi (tailIntegrand_bound_ae a b c hz)


/-- A fixed-domain expression for the horizontal tail. -/
theorem tail_eq_shift_integral (a b c : ℝ) (z : ℂ) :
    tail a b c z = ∫ s in Ioi (0:ℝ), differential a b c (z+(s:ℂ)) := by
  rw [tail, ← integral_add_right_eq_self _ z.re,
    ← integral_indicator measurableSet_Ioi]
  apply integral_congr_ae
  filter_upwards [] with s
  have he : ((s+z.re:ℝ):ℂ)+(z.im:ℂ)*Complex.I = z+(s:ℂ) := by
    apply Complex.ext <;> simp [add_comm, add_assoc]
  by_cases hs : 0 < s
  · simpa [tailIntegrand, hs] using congrArg (differential a b c) he
  · simp [tailIntegrand, hs]

private theorem near_upper {z w : ℂ} (hz : z ∈ upper)
    (hw : ‖w-z‖ ≤ z.im/2) : w ∈ upper := by
  have hi := Complex.abs_im_le_norm (w-z)
  have hil : -(w.im-z.im) ≤ ‖w-z‖ := by
    exact (neg_le_abs _).trans (by simpa using hi)
  change 0 < w.im
  change 0 < z.im at hz
  linarith

private theorem near_sqrt_bound {z w : ℂ} {t : ℝ} (_hz : z ∈ upper)
    (hw : ‖w-z‖ ≤ z.im/2) :
    Real.sqrt |z.re-t| ≤ 2*Real.sqrt ‖w-(t:ℂ)‖ := by
  have ht : z.im ≤ ‖z-(t:ℂ)‖ := by
    simpa using (Complex.im_le_norm (z-(t:ℂ)))
  have hn : ‖z-(t:ℂ)‖ ≤ ‖z-w‖+‖w-(t:ℂ)‖ := by
    calc
      _ = ‖(z-w)+(w-(t:ℂ))‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  rw [norm_sub_rev z w] at hn
  have ha : |z.re-t| ≤ 2*‖w-(t:ℂ)‖ := by
    have hr := Complex.abs_re_le_norm (z-(t:ℂ))
    simp only [Complex.sub_re, Complex.ofReal_re] at hr
    linarith
  have hsq1 := Real.sq_sqrt (abs_nonneg (z.re-t))
  have hsq2 := Real.sq_sqrt (norm_nonneg (w-(t:ℂ)))
  have hn1 := Real.sqrt_nonneg |z.re-t|
  have hn2 := Real.sqrt_nonneg ‖w-(t:ℂ)‖
  nlinarith [sq_nonneg (Real.sqrt |z.re-t|-2*Real.sqrt ‖w-(t:ℂ)‖)]

/-- On a half-height neighborhood the cubic differential is controlled by
one fixed integrable real-axis majorant. -/
theorem differential_near_bound {a b c : ℝ} {z w : ℂ} (hz : z ∈ upper)
    (hw : ‖w-z‖ ≤ z.im/2) (ha : z.re ≠ a) (hb : z.re ≠ b) (hc : z.re ≠ c) :
    ‖differential a b c w‖ ≤ 8*realDensity a b c z.re := by
  have hwu := near_upper hz hw
  rw [differential_norm hwu.le]
  have ha' := near_sqrt_bound (t := a) hz hw
  have hb' := near_sqrt_bound (t := b) hz hw
  have hc' := near_sqrt_bound (t := c) hz hw
  have hp : 0 < Real.sqrt |z.re-a| * Real.sqrt |z.re-b| * Real.sqrt |z.re-c| := by
    exact mul_pos (mul_pos (Real.sqrt_pos.2 (abs_pos.2 (sub_ne_zero.mpr ha)))
      (Real.sqrt_pos.2 (abs_pos.2 (sub_ne_zero.mpr hb))))
      (Real.sqrt_pos.2 (abs_pos.2 (sub_ne_zero.mpr hc)))
  have hpw : 0 < Real.sqrt ‖w-(a:ℂ)‖ * Real.sqrt ‖w-(b:ℂ)‖ * Real.sqrt ‖w-(c:ℂ)‖ := by
    have hnorm (t : ℝ) : 0 < ‖w-(t:ℂ)‖ := by
      have hn := Complex.im_le_norm (w-(t:ℂ))
      simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at hn
      exact lt_of_lt_of_le hwu hn
    exact mul_pos (mul_pos (Real.sqrt_pos.2 (hnorm a)) (Real.sqrt_pos.2 (hnorm b)))
      (Real.sqrt_pos.2 (hnorm c))
  have hm := mul_le_mul (mul_le_mul ha' hb' (Real.sqrt_nonneg _) (by positivity))
    hc' (Real.sqrt_nonneg _) (by positivity)
  unfold realDensity
  rw [mul_one_div]
  apply (div_le_div_iff₀ hpw hp).2
  nlinarith

private theorem shift_integrable {a b c : ℝ} (hi : Integrable (realDensity a b c))
    {z : ℂ} (hz : z ∈ upper) :
    Integrable (fun s : ℝ => differential a b c (z+(s:ℂ))) := by
  apply (hi.comp_add_right z.re).mono'
  · exact ((differential_measurable a b c).comp
      (measurable_const.add Complex.measurable_ofReal)).aestronglyMeasurable
  · filter_upwards [ae_real_ne (a-z.re), ae_real_ne (b-z.re), ae_real_ne (c-z.re)]
      with s ha hb hc
    have he : z+(s:ℂ) = ((s+z.re:ℝ):ℂ)+(z.im:ℂ)*Complex.I := by
      apply Complex.ext <;> simp [add_comm, add_assoc]
    rw [he]
    exact differential_horizontal_bound hz.le (by intro h; apply ha; linarith)
      (by intro h; apply hb; linarith) (by intro h; apply hc; linarith)


private theorem shift_near_upper {z w : ℂ} (hz : z ∈ upper)
    (hw : w ∈ Metric.ball z (z.im/4)) (s : ℝ) : w+(s:ℂ) ∈ upper := by
  have hn : ‖w-z‖ ≤ z.im/2 := by
    have ht := Metric.mem_ball.1 hw
    rw [dist_eq_norm] at ht
    change 0 < z.im at hz
    linarith
  simpa [upper] using near_upper hz hn

private theorem shift_deriv_bound {a b c : ℝ} {z w : ℂ} (hz : z ∈ upper)
    (hw : w ∈ Metric.ball z (z.im/4)) {s : ℝ}
    (ha : s+z.re ≠ a) (hb : s+z.re ≠ b) (hc : s+z.re ≠ c) :
    ‖deriv (differential a b c) (w+(s:ℂ))‖ ≤
      (32/z.im)*realDensity a b c (s+z.re) := by
  have hzpos : 0 < z.im := hz
  have hr : 0 < z.im/4 := by positivity
  have hzu : z+(s:ℂ) ∈ upper := by simpa [upper] using hz
  have hnear {u : ℂ} (hu : u ∈ Metric.closedBall (w+(s:ℂ)) (z.im/4)) :
      ‖u-(z+(s:ℂ))‖ ≤ (z+(s:ℂ)).im/2 := by
    have ht := norm_sub_le_norm_sub_add_norm_sub u (w+(s:ℂ)) (z+(s:ℂ))
    have he : w+(s:ℂ)-(z+(s:ℂ)) = w-z := by ring
    rw [he] at ht
    have hu' := Metric.mem_closedBall.1 hu
    have hw' := Metric.mem_ball.1 hw
    simp only [dist_eq_norm] at hu' hw'
    simp only [Complex.add_im, Complex.ofReal_im, add_zero]
    linarith
  have hd := (differential_differentiableOn a b c).diffContOnCl_ball
    (c := w+(s:ℂ)) (R := z.im/4) (by
      intro u hu
      exact near_upper hzu (hnear hu))
  have hbnd := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hd
    (C := 8*realDensity a b c (s+z.re)) (by
      intro u hu
      have hu' : u ∈ Metric.closedBall (w+(s:ℂ)) (z.im/4) := Metric.sphere_subset_closedBall hu
      simpa [add_comm] using differential_near_bound hzu (hnear hu')
        (by simpa [add_comm] using ha) (by simpa [add_comm] using hb)
        (by simpa [add_comm] using hc))
  calc
    _ ≤ (8*realDensity a b c (s+z.re))/(z.im/4) := hbnd
    _ = _ := by ring

private theorem shift_hasDerivAt {a b c : ℝ} {z : ℂ} (hz : z ∈ upper) (s : ℝ) :
    HasDerivAt (fun w : ℂ => differential a b c (w+(s:ℂ)))
      (deriv (differential a b c) (z+(s:ℂ))) z := by
  have hzu : z+(s:ℂ) ∈ upper := by simpa [upper] using hz
  have hd := ((differential_differentiableOn a b c).differentiableAt
    (upper_open.mem_nhds hzu)).hasDerivAt
  convert hd.comp z ((hasDerivAt_id z).add_const (s:ℂ)) using 1 <;>
    first | rfl | simp only [mul_one]

private theorem shiftIntegral_hasDerivAt_integral (S : Set ℝ) {a b c : ℝ}
    (hi : Integrable (realDensity a b c)) {z : ℂ} (hz : z ∈ upper) :
    IntegrableOn (fun s : ℝ => deriv (differential a b c) (z+(s:ℂ))) S ∧
    HasDerivAt (fun w : ℂ => ∫ s in S, differential a b c (w+(s:ℂ)))
      (∫ s in S, deriv (differential a b c) (z+(s:ℂ))) z := by
  have hball : Metric.ball z (z.im/4) ∈ 𝓝 z := Metric.ball_mem_nhds _ (by exact div_pos hz (by norm_num))
  have hmeas (w : ℂ) : AEStronglyMeasurable
      (fun s : ℝ => differential a b c (w+(s:ℂ))) (volume.restrict S) :=
    ((differential_measurable a b c).comp
      (measurable_const.add Complex.measurable_ofReal)).aestronglyMeasurable
  have hdmeas : AEStronglyMeasurable
      (fun s : ℝ => deriv (differential a b c) (z+(s:ℂ))) (volume.restrict S) :=
    ((measurable_deriv (differential a b c)).comp
      (measurable_const.add Complex.measurable_ofReal)).aestronglyMeasurable
  have hbound : ∀ᵐ (s : ℝ) ∂volume.restrict S, ∀ w ∈ Metric.ball z (z.im/4),
      ‖deriv (differential a b c) (w+(s:ℂ))‖ ≤
        (32/z.im)*realDensity a b c (s+z.re) := by
    apply ae_restrict_of_ae
    filter_upwards [ae_real_ne (a-z.re), ae_real_ne (b-z.re), ae_real_ne (c-z.re)]
      with s ha hb hc w hw
    exact shift_deriv_bound hz hw (by intro h; apply ha; linarith)
      (by intro h; apply hb; linarith) (by intro h; apply hc; linarith)
  have hdiff : ∀ᵐ (s : ℝ) ∂volume.restrict S, ∀ w ∈ Metric.ball z (z.im/4),
      HasDerivAt (fun u : ℂ => differential a b c (u+(s:ℂ)))
        (deriv (differential a b c) (w+(s:ℂ))) w := by
    exact Eventually.of_forall (fun s w hw => shift_hasDerivAt
      (by simpa [upper] using shift_near_upper hz hw 0) s)
  obtain ⟨hint,hderiv⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (w : ℂ) (s : ℝ) => differential a b c (w+(s:ℂ)))
    (F' := fun (w : ℂ) (s : ℝ) => deriv (differential a b c) (w+(s:ℂ))) hball
    (Eventually.of_forall hmeas) (shift_integrable hi hz).integrableOn hdmeas hbound
    (((hi.comp_add_right z.re).const_mul (32/z.im)).integrableOn) hdiff
  exact ⟨hint,hderiv⟩



private theorem tail_hasDerivAt_integral {a b c : ℝ}
    (hi : Integrable (realDensity a b c)) {z : ℂ} (hz : z ∈ upper) :
    IntegrableOn (fun s : ℝ => deriv (differential a b c) (z+(s:ℂ))) (Ioi 0) ∧
    HasDerivAt (tail a b c)
      (∫ s in Ioi (0:ℝ), deriv (differential a b c) (z+(s:ℂ))) z := by
  simpa only [← tail_eq_shift_integral] using shiftIntegral_hasDerivAt_integral (Ioi 0) hi hz

/-- The differential vanishes at the right end of every horizontal line. -/
theorem differential_shift_tendsto_atTop (a b c : ℝ) {z : ℂ} (hz : z ∈ upper) :
    Tendsto (fun s : ℝ => differential a b c (z+(s:ℂ))) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.2
  have hn (t : ℝ) : Tendsto (fun s : ℝ => ‖z+(s:ℂ)-(t:ℂ)‖) atTop atTop := by
    apply tendsto_atTop_mono (f := fun s : ℝ => s+(z.re-t))
    · intro s
      have h := Complex.re_le_norm (z+(s:ℂ)-(t:ℂ))
      convert h using 1 <;> first | rfl | (simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re]; ring)
    · exact tendsto_atTop_add_const_right atTop (z.re-t) tendsto_id
  have ha := Real.tendsto_sqrt_atTop.comp (hn a)
  have hb := Real.tendsto_sqrt_atTop.comp (hn b)
  have hc := Real.tendsto_sqrt_atTop.comp (hn c)
  have hp := (ha.atTop_mul_atTop₀ hb).atTop_mul_atTop₀ hc
  have hinv := tendsto_inv_atTop_zero.comp hp
  convert hinv using 1
  ext s
  rw [differential_norm (by simpa [upper] using hz.le), one_div]
  rfl

/-- Differentiating the explicitly constructed horizontal tail gives the
negative cubic differential, with no assumed uniformizing chart. -/
theorem tail_hasDerivAt {a b c : ℝ}
    (hi : Integrable (realDensity a b c)) {z : ℂ} (hz : z ∈ upper) :
    HasDerivAt (tail a b c) (-differential a b c z) z := by
  obtain ⟨hint,hderiv⟩ := tail_hasDerivAt_integral hi hz
  have hreal (s : ℝ) : HasDerivAt (fun t : ℝ => differential a b c (z+(t:ℂ)))
      (deriv (differential a b c) (z+(s:ℂ))) s := by
    have hzu : z+(s:ℂ) ∈ upper := by simpa [upper] using hz
    have hd := ((differential_differentiableOn a b c).differentiableAt
      (upper_open.mem_nhds hzu)).hasDerivAt
    exact (hd.comp_const_add z (s:ℂ)).comp_ofReal
  have heq := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun s (_ : s ∈ Ici (0:ℝ)) => hreal s) hint (differential_shift_tendsto_atTop a b c hz)
  simp only [Complex.ofReal_zero, add_zero, zero_sub] at heq
  rwa [heq] at hderiv


/-- Decay of the actual cubic differential at infinity in the closed
upper half-plane, along an arbitrary filter. -/
theorem differential_tendsto_zero_of_norm_atTop {ι : Type*} {l : Filter ι}
    {a b c : ℝ} {f : ι → ℂ} (hupper : ∀ᶠ i in l, 0 ≤ (f i).im)
    (hnorm : Tendsto (fun i => ‖f i‖) l atTop) :
    Tendsto (fun i => differential a b c (f i)) l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.2
  have hn (t : ℝ) : Tendsto (fun i => ‖f i-(t:ℂ)‖) l atTop := by
    apply tendsto_atTop_mono (f := fun i => ‖f i‖-‖(t:ℂ)‖)
    · intro i
      exact norm_sub_norm_le _ _
    · simpa only [sub_eq_add_neg] using
        tendsto_atTop_add_const_right l (-‖(t:ℂ)‖) hnorm
  have hp := ((Real.tendsto_sqrt_atTop.comp (hn a)).atTop_mul_atTop₀
    (Real.tendsto_sqrt_atTop.comp (hn b))).atTop_mul_atTop₀
    (Real.tendsto_sqrt_atTop.comp (hn c))
  have hinv := tendsto_inv_atTop_zero.comp hp
  apply hinv.congr'
  filter_upwards [hupper] with i hi
  simpa only [Function.comp_def, one_div] using
    (differential_norm (a := a) (b := b) (c := c) hi).symm

/-- In particular the differential vanishes along every upward vertical
line. This controls the top sides of the Green rectangles. -/
theorem differential_vertical_tendsto_atTop (a b c x : ℝ) :
    Tendsto (fun y : ℝ => differential a b c ((x:ℂ)+(y:ℂ)*Complex.I)) atTop (𝓝 0) := by
  apply differential_tendsto_zero_of_norm_atTop
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with y hy
    simpa using hy
  · apply tendsto_atTop_mono (f := fun y : ℝ => y)
    · intro y
      simpa using Complex.im_le_norm ((x:ℂ)+(y:ℂ)*Complex.I)
    · exact tendsto_id

/-- The constructed primitive vanishes along every upward vertical line,
including vertical lines through the boundary singularities. -/
theorem tail_vertical_tendsto_atTop {a b c : ℝ}
    (hi : Integrable (realDensity a b c)) (x : ℝ) :
    Tendsto (fun y : ℝ => tail a b c ((x:ℂ)+(y:ℂ)*Complex.I)) atTop (𝓝 0) := by
  have hlim : ∀ᵐ t : ℝ, Tendsto
      (fun y : ℝ => tailIntegrand a b c ((x:ℂ)+(y:ℂ)*Complex.I) t) atTop (𝓝 (0:ℂ)) := by
    filter_upwards [] with t
    by_cases ht : x < t
    · simpa [tailIntegrand, ht] using differential_vertical_tendsto_atTop a b c t
    · simp [tailIntegrand, ht]
  have h := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (realDensity a b c)
    (Eventually.of_forall (fun y : ℝ =>
      (tailIntegrand_measurable a b c ((x:ℂ)+(y:ℂ)*Complex.I)).aestronglyMeasurable))
    (show ∀ᶠ y : ℝ in atTop, ∀ᵐ t : ℝ,
      ‖tailIntegrand a b c ((x:ℂ)+(y:ℂ)*Complex.I) t‖ ≤ realDensity a b c t by
      filter_upwards [eventually_ge_atTop (0:ℝ)] with y hy
      exact tailIntegrand_bound_ae a b c (by simpa [closedUpper] using hy)) hi hlim
  simpa only [tail, integral_zero] using h


/-- Cancellation of the cubic differential on a complete horizontal line. -/
def lineIntegral (a b c : ℝ) (z : ℂ) : ℂ :=
  ∫ s : ℝ, differential a b c (z+(s:ℂ))

private theorem differential_shift_tendsto_atBot (a b c : ℝ) {z : ℂ} (hz : z ∈ upper) :
    Tendsto (fun s : ℝ => differential a b c (z+(s:ℂ))) atBot (𝓝 0) := by
  apply differential_tendsto_zero_of_norm_atTop
  · exact Eventually.of_forall (fun s => by simpa [upper] using hz.le)
  · apply tendsto_atTop_mono (f := fun s : ℝ => -s+(-z.re))
    · intro s
      have hn := (neg_le_abs (z+(s:ℂ)).re).trans (Complex.abs_re_le_norm (z+(s:ℂ)))
      simpa [neg_add, add_comm] using hn
    · exact tendsto_atTop_add_const_right atBot (-z.re) tendsto_neg_atBot_atTop

private theorem lineIntegral_hasDerivAt_zero {a b c : ℝ}
    (hi : Integrable (realDensity a b c)) {z : ℂ} (hz : z ∈ upper) :
    HasDerivAt (lineIntegral a b c) 0 z := by
  obtain ⟨hint,hderiv⟩ := shiftIntegral_hasDerivAt_integral univ hi hz
  simp only [integrableOn_univ, setIntegral_univ] at hint hderiv
  have hreal (s : ℝ) : HasDerivAt (fun t : ℝ => differential a b c (z+(t:ℂ)))
      (deriv (differential a b c) (z+(s:ℂ))) s := by
    have hzu : z+(s:ℂ) ∈ upper := by simpa [upper] using hz
    have hd := ((differential_differentiableOn a b c).differentiableAt
      (upper_open.mem_nhds hzu)).hasDerivAt
    exact (hd.comp_const_add z (s:ℂ)).comp_ofReal
  have heq := integral_of_hasDerivAt_of_tendsto hreal hint
    (differential_shift_tendsto_atBot a b c hz) (differential_shift_tendsto_atTop a b c hz)
  rw [sub_self] at heq
  rw [heq] at hderiv
  exact hderiv

private theorem lineIntegral_vertical_tendsto_atTop {a b c : ℝ}
    (hi : Integrable (realDensity a b c)) :
    Tendsto (fun y : ℝ => lineIntegral a b c ((y:ℂ)*Complex.I)) atTop (𝓝 0) := by
  have hlim : ∀ᵐ s : ℝ, Tendsto
      (fun y : ℝ => differential a b c ((y:ℂ)*Complex.I+(s:ℂ))) atTop (𝓝 (0:ℂ)) := by
    exact Eventually.of_forall (fun s => by
      simpa only [add_comm] using differential_vertical_tendsto_atTop a b c s)
  have hmeas (y : ℝ) : AEStronglyMeasurable
      (fun s : ℝ => differential a b c ((y:ℂ)*Complex.I+(s:ℂ))) volume :=
    ((differential_measurable a b c).comp
      (measurable_const.add Complex.measurable_ofReal)).aestronglyMeasurable
  have hb : ∀ᶠ y : ℝ in atTop, ∀ᵐ s : ℝ,
      ‖differential a b c ((y:ℂ)*Complex.I+(s:ℂ))‖ ≤ realDensity a b c s := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with y hy
    simpa only [add_comm] using differential_horizontal_bound_ae a b c hy
  simpa only [lineIntegral, integral_zero] using
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (realDensity a b c) (Eventually.of_forall hmeas) hb hi hlim

/-- The full horizontal integral is identically zero; this derives both
real and imaginary period cancellation from the constructed differential. -/
theorem lineIntegral_eq_zero {a b c : ℝ}
    (hi : Integrable (realDensity a b c)) {z : ℂ} (hz : z ∈ upper) :
    lineIntegral a b c z = 0 := by
  have hconst (w : ℂ) (hw : w ∈ upper) : lineIntegral a b c w = lineIntegral a b c z := by
    exact upper_open.is_const_of_deriv_eq_zero upper_convex.isPreconnected
      (fun u hu => (lineIntegral_hasDerivAt_zero hi hu).differentiableAt.differentiableWithinAt)
      (fun u hu => (lineIntegral_hasDerivAt_zero hi hu).deriv) hw hz
  have heq : (fun y : ℝ => lineIntegral a b c ((y:ℂ)*Complex.I)) =ᶠ[atTop]
      (fun _ => lineIntegral a b c z) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
    exact hconst _ (by simpa [upper] using hy)
  exact tendsto_nhds_unique (tendsto_const_nhds.congr' heq.symm)
    (lineIntegral_vertical_tendsto_atTop hi)


private theorem horizontal_integrable {a b c : ℝ}
    (hi : Integrable (realDensity a b c)) {y : ℝ} (hy : 0 ≤ y) :
    Integrable (fun t : ℝ => differential a b c ((t:ℂ)+(y:ℂ)*Complex.I)) := by
  exact hi.mono' (((differential_measurable a b c).comp
    (Complex.measurable_ofReal.add measurable_const)).aestronglyMeasurable)
    (differential_horizontal_bound_ae a b c hy)

private theorem horizontal_integral_continuousOn {a b c : ℝ}
    (hi : Integrable (realDensity a b c)) :
    ContinuousOn (fun y : ℝ => ∫ t : ℝ, differential a b c ((t:ℂ)+(y:ℂ)*Complex.I)) (Ici 0) := by
  intro y hy
  apply MeasureTheory.tendsto_integral_filter_of_dominated_convergence (realDensity a b c)
  · exact Eventually.of_forall (fun v => ((differential_measurable a b c).comp
      (Complex.measurable_ofReal.add measurable_const)).aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with v hv
    exact differential_horizontal_bound_ae a b c hv
  · exact hi
  · filter_upwards [ae_real_ne a, ae_real_ne b, ae_real_ne c] with t ha hb hc
    have hn (u : ℝ) (hu : t ≠ u) : (t:ℂ)+(y:ℂ)*Complex.I ≠ (u:ℂ) := by
      intro heq
      exact hu (by simpa using congrArg Complex.re heq)
    have hcont := (differential_continuousAt (by simpa using hy) (hn a ha) (hn b hb) (hn c hc)).comp
      (f := fun v : ℝ => (t:ℂ)+(v:ℂ)*Complex.I) (by fun_prop)
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds

/-- Full horizontal cancellation holds also on the singular boundary line. -/
theorem horizontal_integral_eq_zero {a b c : ℝ}
    (hi : Integrable (realDensity a b c)) {y : ℝ} (hy : 0 ≤ y) :
    (∫ t : ℝ, differential a b c ((t:ℂ)+(y:ℂ)*Complex.I)) = 0 := by
  have hpos (v : ℝ) (hv : 0 < v) :
      (∫ t : ℝ, differential a b c ((t:ℂ)+(v:ℂ)*Complex.I)) = 0 := by
    simpa only [lineIntegral, add_comm] using
      lineIntegral_eq_zero hi (z := (v:ℂ)*Complex.I) (by simpa [upper] using hv)
  rcases eq_or_lt_of_le hy with rfl | hy
  · have hc := (horizontal_integral_continuousOn hi 0 self_mem_Ici).mono
      (Ioi_subset_Ici_self : Ioi (0:ℝ) ⊆ Ici 0)
    have heq : (fun v : ℝ => ∫ t : ℝ, differential a b c ((t:ℂ)+(v:ℂ)*Complex.I))
        =ᶠ[𝓝[>] (0:ℝ)] (fun _ => (0:ℂ)) := by
      filter_upwards [self_mem_nhdsWithin] with v hv
      exact hpos v hv
    exact tendsto_nhds_unique hc (tendsto_const_nhds.congr' heq.symm)
  · exact hpos y hy

theorem tail_eq_horizontal_Ioi (a b c : ℝ) (z : ℂ) :
    tail a b c z = ∫ t in Ioi z.re, differential a b c ((t:ℂ)+(z.im:ℂ)*Complex.I) := by
  exact integral_indicator measurableSet_Ioi

/-- Cancellation makes the same primitive a left tail with opposite sign. -/
theorem tail_eq_neg_horizontal_Iic {a b c : ℝ}
    (hi : Integrable (realDensity a b c)) {z : ℂ} (hz : z ∈ closedUpper) :
    tail a b c z = -(∫ t in Iic z.re, differential a b c ((t:ℂ)+(z.im:ℂ)*Complex.I)) := by
  have hint := horizontal_integrable hi hz
  have heq := integral_add_compl (s := Iic z.re) measurableSet_Iic hint
  rw [compl_Iic, horizontal_integral_eq_zero hi hz] at heq
  rw [tail_eq_horizontal_Ioi]
  exact eq_neg_of_add_eq_zero_right heq

/-- Uniform right-tail control, independent of height. -/
theorem tail_norm_le_right_tail {a b c : ℝ}
    (hi : Integrable (realDensity a b c)) {z : ℂ} (hz : z ∈ closedUpper) :
    ‖tail a b c z‖ ≤ ∫ t in Ioi z.re, realDensity a b c t := by
  rw [tail_eq_horizontal_Ioi]
  exact norm_integral_le_of_norm_le hi.integrableOn
    (ae_restrict_of_ae (differential_horizontal_bound_ae a b c hz))

/-- Uniform left-tail control, independent of height. -/
theorem tail_norm_le_left_tail {a b c : ℝ}
    (hi : Integrable (realDensity a b c)) {z : ℂ} (hz : z ∈ closedUpper) :
    ‖tail a b c z‖ ≤ ∫ t in Iic z.re, realDensity a b c t := by
  rw [tail_eq_neg_horizontal_Iic hi hz, norm_neg]
  exact norm_integral_le_of_norm_le hi.integrableOn
    (ae_restrict_of_ae (differential_horizontal_bound_ae a b c hz))


private def horizontalNormIntegral (a b c y : ℝ) : ℝ :=
  ∫ t : ℝ, ‖differential a b c ((t:ℂ)+(y:ℂ)*Complex.I)‖

private theorem horizontalNormIntegral_tendsto_atTop {a b c : ℝ}
    (hi : Integrable (realDensity a b c)) :
    Tendsto (horizontalNormIntegral a b c) atTop (𝓝 0) := by
  change Tendsto (fun y : ℝ => ∫ t : ℝ, ‖differential a b c ((t:ℂ)+(y:ℂ)*Complex.I)‖) atTop (𝓝 0)
  have hm (y : ℝ) : AEStronglyMeasurable
      (fun t : ℝ => ‖differential a b c ((t:ℂ)+(y:ℂ)*Complex.I)‖) volume :=
    (((differential_measurable a b c).comp
      (Complex.measurable_ofReal.add measurable_const)).norm).aestronglyMeasurable
  have hb : ∀ᶠ y : ℝ in atTop, ∀ᵐ t : ℝ,
      ‖‖differential a b c ((t:ℂ)+(y:ℂ)*Complex.I)‖‖ ≤ realDensity a b c t := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with y hy
    simpa only [norm_norm] using differential_horizontal_bound_ae a b c hy
  have hl : ∀ᵐ t : ℝ, Tendsto
      (fun y : ℝ => ‖differential a b c ((t:ℂ)+(y:ℂ)*Complex.I)‖) atTop (𝓝 (0:ℝ)) :=
    Eventually.of_forall (fun t => by
      simpa only [norm_zero] using (differential_vertical_tendsto_atTop a b c t).norm)
  simpa only [integral_zero] using
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (realDensity a b c) (Eventually.of_forall hm) hb hi hl

private theorem tail_norm_le_horizontalNormIntegral {a b c : ℝ}
    (hi : Integrable (realDensity a b c)) {z : ℂ} (hz : z ∈ closedUpper) :
    ‖tail a b c z‖ ≤ horizontalNormIntegral a b c z.im := by
  exact norm_integral_le_of_norm_le (horizontal_integrable hi hz).norm
    (Eventually.of_forall (fun t => norm_indicator_le_norm_self _ _))

/-- The actual cubic primitive tends uniformly to zero at the single
point at infinity of the closed upper half-plane. -/
theorem tail_uniform_decay {a b c : ℝ} (hi : Integrable (realDensity a b c))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R > 0, ∀ z ∈ closedUpper, R ≤ ‖z‖ → ‖tail a b c z‖ < ε := by
  have hr : Tendsto (fun x : ℝ => ∫ t in Ioi x, realDensity a b c t) atTop (𝓝 0) :=
    tendsto_integral_Ioi_zero tendsto_id
  have hl : Tendsto (fun x : ℝ => ∫ t in Iic x, realDensity a b c t) atBot (𝓝 0) :=
    tendsto_integral_Iic_zero tendsto_id
  obtain ⟨r,hr⟩ := eventually_atTop.1 (hr.eventually (Iio_mem_nhds hε))
  obtain ⟨l,hl⟩ := eventually_atBot.1 (hl.eventually (Iio_mem_nhds hε))
  obtain ⟨y,hy⟩ := eventually_atTop.1
    ((horizontalNormIntegral_tendsto_atTop hi).eventually (Iio_mem_nhds hε))
  let R : ℝ := max 1 (max r (max (-l) y))
  have hR1 : 1 ≤ R := le_max_left _ _
  have hRr : r ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hRl : -l ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hRy : y ≤ R := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨2*R+1, by linarith, ?_⟩
  intro z hz hn
  by_cases hzr : R ≤ z.re
  · exact (tail_norm_le_right_tail hi hz).trans_lt (hr z.re (hRr.trans hzr))
  by_cases hzl : z.re ≤ -R
  · exact (tail_norm_le_left_tail hi hz).trans_lt (hl z.re (by linarith))
  · have hrea : |z.re| ≤ R := abs_le.mpr ⟨by linarith, by linarith⟩
    have hn' := Complex.norm_le_abs_re_add_abs_im z
    rw [abs_of_nonneg (a := z.im) hz] at hn'
    have hyz : y ≤ z.im := by linarith
    exact (tail_norm_le_horizontalNormIntegral hi hz).trans_lt (hy z.im hyz)

/-- Filter formulation of uniform decay, ready for compactification and
properness arguments in the rectangle construction. -/
theorem tail_tendsto_zero_of_norm_atTop {ι : Type*} {l : Filter ι}
    {a b c : ℝ} (hi : Integrable (realDensity a b c)) {f : ι → ℂ}
    (hupper : ∀ᶠ i in l, f i ∈ closedUpper)
    (hnorm : Tendsto (fun i => ‖f i‖) l atTop) :
    Tendsto (fun i => tail a b c (f i)) l (𝓝 0) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨R,hR,hbound⟩ := tail_uniform_decay hi hε
  filter_upwards [hupper, hnorm.eventually (eventually_ge_atTop R)] with i hi' hn
  simpa only [dist_zero_right] using hbound (f i) hi' hn

end
end SlitCubicCalibration
