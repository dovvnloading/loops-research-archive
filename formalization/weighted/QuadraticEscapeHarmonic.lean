import QuadraticEscape
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Harmonicity of the actual quadratic escape potential

A normally convergent analytic logarithmic correction on the far exterior
has real part equal to the already constructed escape potential minus
`log ‖z‖`. Finite iteration transports this representation to every
escaping analytic parameter/point family. In particular the dynamical and
parameter escape potentials are harmonic throughout their positive loci.
-/

namespace QuadraticEscapeHarmonic

open Set Filter Topology InnerProductSpace QuadraticEscape

noncomputable section

/-- The analytic correction to the logarithm at one actual orbit step. -/
def logCorrectionTerm (c z : ℂ) (n : ℕ) : ℂ :=
  (weight (n+1) : ℂ) * Complex.log (1 + c / (orbit c n z)^2)

/-- The convergent correction used on the far exterior. -/
def logCorrection (c z : ℂ) : ℂ := ∑' n : ℕ, logCorrectionTerm c z n

private theorem exterior_step_bound (C : ℝ) (c z : ℂ)
    (hC : 0 ≤ C) (hc : ‖c‖ ≤ C) (hz : 2*(1+C) ≤ ‖z‖) :
    ‖z‖ ≤ ‖z^2+c‖ := by
  have hback : ‖z‖^2 ≤ ‖z^2+c‖ + C := by
    calc
      ‖z‖^2 = ‖(z^2+c)-c‖ := by rw [add_sub_cancel_right, norm_pow]
      _ ≤ ‖z^2+c‖ + ‖c‖ := norm_sub_le _ _
      _ ≤ ‖z^2+c‖ + C := add_le_add_left hc _
  have hr : 2 ≤ ‖z‖ := by linarith
  have hp : 0 ≤ ‖z‖ * (‖z‖-2) :=
    mul_nonneg (norm_nonneg z) (by linarith)
  nlinarith

/-- One common exterior region is preserved by every actual iterate. -/
theorem exterior_orbit_bound (C : ℝ) (c z : ℂ)
    (hC : 0 ≤ C) (hc : ‖c‖ ≤ C) (hz : 2*(1+C) ≤ ‖z‖) (n : ℕ) :
    2*(1+C) ≤ ‖orbit c n z‖ := by
  induction n with
  | zero => exact hz
  | succ n ih => exact ih.trans (exterior_step_bound C c _ hC hc ih)

private theorem exterior_orbit_ne_zero (C : ℝ) (c z : ℂ)
    (hC : 0 ≤ C) (hc : ‖c‖ ≤ C) (hz : 2*(1+C) ≤ ‖z‖) (n : ℕ) :
    orbit c n z ≠ 0 := by
  have h := exterior_orbit_bound C c z hC hc hz n
  exact norm_pos_iff.mp (by linarith)

/-- Every logarithmic correction stays in the fixed small-ratio disk. -/
theorem exterior_ratio_bound (C : ℝ) (c z : ℂ)
    (hC : 0 ≤ C) (hc : ‖c‖ ≤ C) (hz : 2*(1+C) ≤ ‖z‖) (n : ℕ) :
    ‖c / (orbit c n z)^2‖ ≤ 1/2 := by
  have hr := exterior_orbit_bound C c z hC hc hz n
  have hp : 0 < ‖orbit c n z‖ := by linarith
  rw [norm_div, norm_pow, div_le_iff₀ (pow_pos hp 2)]
  have hprod : 0 ≤ ‖orbit c n z‖ * (‖orbit c n z‖-1) :=
    mul_nonneg hp.le (by linarith)
  nlinarith

/-- A geometric majorant controls the complex series uniformly over all
parameters and initial points in one fixed exterior region. -/
theorem exterior_log_term_bound (C : ℝ) (c z : ℂ)
    (hC : 0 ≤ C) (hc : ‖c‖ ≤ C) (hz : 2*(1+C) ≤ ‖z‖) (n : ℕ) :
    ‖logCorrectionTerm c z n‖ ≤ weight (n+1) := by
  have hratio := exterior_ratio_bound C c z hC hc hz n
  have hlog := Complex.norm_log_one_add_half_le_self hratio
  have hlogone : ‖Complex.log (1 + c / (orbit c n z)^2)‖ ≤ 1 := by
    nlinarith
  rw [logCorrectionTerm, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (weight_pos (n+1))]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hlogone (weight_pos (n+1)).le

private theorem shifted_weight_summable : Summable (fun n : ℕ => weight (n+1)) := by
  have h : Summable (fun n : ℕ => (1/2 : ℝ)^n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  simpa only [weight, pow_succ] using h.mul_right (1/2 : ℝ)

theorem exterior_log_correction_summable (C : ℝ) (c z : ℂ)
    (hC : 0 ≤ C) (hc : ‖c‖ ≤ C) (hz : 2*(1+C) ≤ ‖z‖) :
    Summable (logCorrectionTerm c z) :=
  shifted_weight_summable.of_norm_bounded
    (exterior_log_term_bound C c z hC hc hz)

private theorem log_norm_quadratic_step (c w : ℂ) (hw : w ≠ 0)
    (hsmall : ‖c / w^2‖ ≤ 1/2) :
    Real.log ‖w^2+c‖ =
      2*Real.log ‖w‖ + (Complex.log (1+c/w^2)).re := by
  have hfactor : w^2+c = w^2*(1+c/w^2) := by field_simp [hw] <;> ring
  have hone : 1+c/w^2 ≠ 0 :=
    Complex.slitPlane_ne_zero
      (Complex.mem_slitPlane_of_norm_lt_one (by linarith))
  rw [hfactor, norm_mul, norm_pow,
    Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.mpr hw))
      (norm_ne_zero_iff.mpr hone), Real.log_pow, Complex.log_re]
  norm_num

/-- The finite correction sum is exactly the existing orbit approximant. -/
theorem exterior_approx_telescope (C : ℝ) (c z : ℂ)
    (hC : 0 ≤ C) (hc : ‖c‖ ≤ C) (hz : 2*(1+C) ≤ ‖z‖) (n : ℕ) :
    approx c z n = Real.log ‖z‖ +
      (∑ k ∈ Finset.range n, logCorrectionTerm c z k).re := by
  have hnorm (j : ℕ) : 1 ≤ ‖orbit c j z‖ := by
    have h := exterior_orbit_bound C c z hC hc hz j
    linarith
  have hsize (j : ℕ) : logSize (orbit c j z) = Real.log ‖orbit c j z‖ := by
    simp only [logSize, size, max_eq_right (hnorm j)]
  induction n with
  | zero =>
    simpa only [Finset.range_zero, Finset.sum_empty, Complex.zero_re, add_zero,
      approx, weight, pow_zero, one_mul] using hsize 0
  | succ n ih =>
    have hstep := log_norm_quadratic_step c (orbit c n z)
      (exterior_orbit_ne_zero C c z hC hc hz n)
      (exterior_ratio_bound C c z hC hc hz n)
    have hrec : approx c z (n+1) = approx c z n +
        (logCorrectionTerm c z n).re := by
      simp only [approx, hsize, logCorrectionTerm,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      rw [orbit, hstep]
      simp only [weight_succ]
      ring
    rw [hrec, ih, Finset.sum_range_succ, Complex.add_re]
    ring

/-- The analytic correction represents the actual limiting potential. -/
theorem exterior_escape_log_correction (C : ℝ) (c z : ℂ)
    (hC : 0 ≤ C) (hc : ‖c‖ ≤ C) (hz : 2*(1+C) ≤ ‖z‖) :
    escape c z = Real.log ‖z‖ + (logCorrection c z).re := by
  have hs := (exterior_log_correction_summable C c z hC hc hz).hasSum.tendsto_sum_nat
  have hr := Complex.continuous_re.continuousAt.tendsto.comp hs
  have hlim : Tendsto
      (fun n : ℕ => Real.log ‖z‖ +
        (∑ k ∈ Finset.range n, logCorrectionTerm c z k).re)
      atTop (𝓝 (Real.log ‖z‖ + (logCorrection c z).re)) :=
    tendsto_const_nhds.add hr
  have heq : approx c z = fun n : ℕ =>
      Real.log ‖z‖ + (∑ k ∈ Finset.range n, logCorrectionTerm c z k).re :=
    funext (exterior_approx_telescope C c z hC hc hz)
  rw [← heq] at hlim
  exact tendsto_nhds_unique (escape_tendsto c z) hlim

/-- The actual iterate is analytic for analytic parameter and point data. -/
theorem orbit_pair_analyticAt (a b : ℂ → ℂ) (x : ℂ)
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x) (n : ℕ) :
    AnalyticAt ℂ (fun w => orbit (a w) n (b w)) x := by
  induction n with
  | zero => exact hb
  | succ n ih => exact (ih.pow 2).add ha

/-- Normal convergence proves analyticity of the complex correction,
including holomorphic variation of the parameter. -/
theorem log_correction_analyticOnNhd (a b : ℂ → ℂ) (U : Set ℂ)
    (hU : IsOpen U) (ha : AnalyticOnNhd ℂ a U) (hb : AnalyticOnNhd ℂ b U)
    (C : ℝ) (hC : 0 ≤ C)
    (hparam : ∀ w ∈ U, ‖a w‖ ≤ C)
    (hpoint : ∀ w ∈ U, 2*(1+C) ≤ ‖b w‖) :
    AnalyticOnNhd ℂ (fun w => logCorrection (a w) (b w)) U := by
  have hterm (n : ℕ) :
      DifferentiableOn ℂ (fun w => logCorrectionTerm (a w) (b w) n) U := by
    intro w hw
    have horb := orbit_pair_analyticAt a b w (ha w hw) (hb w hw) n
    have hne := exterior_orbit_ne_zero C (a w) (b w) hC
      (hparam w hw) (hpoint w hw) n
    have hratio := exterior_ratio_bound C (a w) (b w) hC
      (hparam w hw) (hpoint w hw) n
    have hlog : AnalyticAt ℂ
        (fun v => Complex.log (1+a v/(orbit (a v) n (b v))^2)) w :=
      (analyticAt_const.add ((ha w hw).div (horb.pow 2) (pow_ne_zero _ hne))).clog
        (Complex.mem_slitPlane_of_norm_lt_one (by linarith))
    exact (analyticAt_const.mul hlog).differentiableWithinAt
  have hdiff := Complex.differentiableOn_tsum_of_summable_norm
    shifted_weight_summable hterm hU
    (fun n w hw => exterior_log_term_bound C (a w) (b w) hC
      (hparam w hw) (hpoint w hw) n)
  exact hdiff.analyticOnNhd hU

/-- On a common exterior region the real logarithm and the analytic
correction prove harmonicity, without postulating a Green coordinate. -/
theorem exterior_pair_harmonicAt (a b : ℂ → ℂ) (U : Set ℂ)
    (hU : IsOpen U) (ha : AnalyticOnNhd ℂ a U) (hb : AnalyticOnNhd ℂ b U)
    (C : ℝ) (hC : 0 ≤ C)
    (hparam : ∀ w ∈ U, ‖a w‖ ≤ C)
    (hpoint : ∀ w ∈ U, 2*(1+C) ≤ ‖b w‖) (x : ℂ) (hx : x ∈ U) :
    HarmonicAt (fun w => escape (a w) (b w)) x := by
  have hsum := log_correction_analyticOnNhd a b U hU ha hb C hC hparam hpoint
  have hbne : b x ≠ 0 := by
    apply norm_pos_iff.mp
    have h := hpoint x hx
    linarith
  have hrep : (fun w => escape (a w) (b w)) =ᶠ[𝓝 x]
      (fun w => Real.log ‖b w‖ + (logCorrection (a w) (b w)).re) := by
    filter_upwards [hU.mem_nhds hx] with w hw
    exact exterior_escape_log_correction C (a w) (b w) hC (hparam w hw) (hpoint w hw)
  apply (harmonicAt_congr_nhds hrep).mpr
  exact ((hb x hx).harmonicAt_log_norm hbne).add ((hsum x hx).harmonicAt_re)

/-- Every escaping analytic parameter/point family has a harmonic
escape potential locally. The finite escape time is derived from
positive escape, and is not an extra hypothesis. -/
theorem escape_pair_harmonicAt (a b : ℂ → ℂ) (x : ℂ)
    (ha : AnalyticAt ℂ a x) (hb : AnalyticAt ℂ b x)
    (hescape : 0 < escape (a x) (b x)) :
    HarmonicAt (fun w => escape (a w) (b w)) x := by
  let C : ℝ := ‖a x‖+1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hcross : ∃ N : ℕ, 2*(1+C) < ‖orbit (a x) N (b x)‖ := by
    by_contra h
    push Not at h
    have he := (escape_zero_iff_bounded (a x) (b x)).mpr ⟨2*(1+C), h⟩
    linarith
  obtain ⟨N, hN⟩ := hcross
  let B : ℂ → ℂ := fun w => orbit (a w) N (b w)
  have hB : AnalyticAt ℂ B x := orbit_pair_analyticAt a b x ha hb N
  have hap : ∀ᶠ w in 𝓝 x, ‖a w‖ < C :=
    ha.continuousAt.norm.eventually (gt_mem_nhds (by dsimp [C]; linarith))
  have hbp : ∀ᶠ w in 𝓝 x, 2*(1+C) < ‖B w‖ :=
    hB.continuousAt.norm.eventually (lt_mem_nhds hN)
  have hloc : ∀ᶠ w in 𝓝 x,
      AnalyticAt ℂ a w ∧ AnalyticAt ℂ B w ∧ ‖a w‖ < C ∧ 2*(1+C) < ‖B w‖ := by
    filter_upwards [ha.eventually_analyticAt, hB.eventually_analyticAt, hap, hbp]
      with w hwa hwb hwp hwq
    exact ⟨hwa, hwb, hwp, hwq⟩
  obtain ⟨U, hprop, hU, hx⟩ := eventually_nhds_iff.mp hloc
  have hfar := exterior_pair_harmonicAt a B U hU
    (fun w hw => (hprop w hw).1) (fun w hw => (hprop w hw).2.1)
    C hC (fun w hw => (hprop w hw).2.2.1.le)
    (fun w hw => (hprop w hw).2.2.2.le) x hx
  have heq : (fun w => escape (a w) (b w)) =ᶠ[𝓝 x]
      ((2 : ℝ)^N)⁻¹ • (fun w => escape (a w) (B w)) := by
    filter_upwards with w
    simp only [Pi.smul_apply, smul_eq_mul, B, escape_iterate]
    rw [← mul_assoc, inv_mul_cancel₀ (by positivity : (2 : ℝ)^N ≠ 0), one_mul]
  exact (harmonicAt_congr_nhds heq).mpr hfar.const_smul

/-- The dynamical escape potential is harmonic at every escaping point. -/
theorem escape_harmonicAt (c z : ℂ) (hz : 0 < escape c z) :
    HarmonicAt (escape c) z :=
  escape_pair_harmonicAt (fun _ => c) id z analyticAt_const analyticAt_id hz

/-- The actual critical-value parameter potential is harmonic outside
its bounded-critical-orbit locus. -/
theorem parameter_escape_harmonicAt (c : ℂ) (hc : 0 < parameterEscape c) :
    HarmonicAt parameterEscape c :=
  escape_pair_harmonicAt id id c analyticAt_id analyticAt_id hc

theorem escape_real_analyticAt (c z : ℂ) (hz : 0 < escape c z) :
    AnalyticAt ℝ (escape c) z :=
  (escape_harmonicAt c z hz).analyticAt

theorem parameter_escape_real_analyticAt (c : ℂ) (hc : 0 < parameterEscape c) :
    AnalyticAt ℝ parameterEscape c :=
  (parameter_escape_harmonicAt c hc).analyticAt

/-- Every closed disk contained in the actual escape locus has the
mean-value identity for the limiting orbit potential. -/
theorem escape_circle_average (c z : ℂ) (R : ℝ)
    (hpos : ∀ w ∈ Metric.closedBall z |R|, 0 < escape c w) :
    Real.circleAverage (escape c) z R = escape c z := by
  apply InnerProductSpace.HarmonicOnNhd.circleAverage_eq
  exact fun w hw => escape_harmonicAt c w (hpos w hw)

theorem parameter_escape_circle_average (c : ℂ) (R : ℝ)
    (hpos : ∀ d ∈ Metric.closedBall c |R|, 0 < parameterEscape d) :
    Real.circleAverage parameterEscape c R = parameterEscape c := by
  apply InnerProductSpace.HarmonicOnNhd.circleAverage_eq
  exact fun d hd => parameter_escape_harmonicAt d (hpos d hd)

end

end QuadraticEscapeHarmonic
