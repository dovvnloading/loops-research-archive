import QuadraticEscapeHarmonic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# A normalized analytic Böttcher function on the actual quadratic exterior

The logarithmic correction gives an analytic function satisfying the
quadratic semiconjugacy equation and the exact escape-potential identity.
A quantitative inverse-square error proves its normalization at infinity.
The reciprocal function extends analytically across zero with derivative
one, so it has an actual analytic local inverse there.
-/

namespace QuadraticBottcherExterior

open Set Filter Topology Bornology QuadraticEscape QuadraticEscapeHarmonic

noncomputable section

/-- The exterior function is constructed from the convergent complex
correction, not selected from a presumed conjugacy. -/
def bottcher (c z : ℂ) : ℂ := z * Complex.exp (logCorrection c z)

private theorem shifted_weight_hasSum : HasSum (fun n : ℕ => weight (n+1)) 1 := by
  have h := (hasSum_geometric_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) < 1)).mul_right (1/2 : ℝ)
  have htotal : (1-(1/2 : ℝ))⁻¹*(1/2 : ℝ) = 1 := by norm_num
  rw [htotal] at h
  simpa only [weight, pow_succ] using h

/-- The norms of actual exterior iterates never decrease. -/
theorem exterior_orbit_norm_lower (C : ℝ) (c z : ℂ)
    (hC : 0 ≤ C) (hc : ‖c‖ ≤ C) (hz : 2*(1+C) ≤ ‖z‖) (n : ℕ) :
    ‖z‖ ≤ ‖orbit c n z‖ := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    have hr := exterior_orbit_bound C c z hC hc hz n
    have hback : ‖orbit c n z‖^2 ≤ ‖orbit c (n+1) z‖ + C := by
      calc
        ‖orbit c n z‖^2 = ‖orbit c (n+1) z-c‖ := by
          rw [orbit, add_sub_cancel_right, norm_pow]
        _ ≤ ‖orbit c (n+1) z‖ + ‖c‖ := norm_sub_le _ _
        _ ≤ ‖orbit c (n+1) z‖ + C := add_le_add le_rfl hc
    have hp : 0 ≤ ‖orbit c n z‖ * (‖orbit c n z‖-2) :=
      mul_nonneg (norm_nonneg _) (by linarith)
    nlinarith

/-- The full analytic correction has an explicit inverse-square bound. -/
theorem log_correction_norm_bound (C : ℝ) (c z : ℂ)
    (hC : 0 ≤ C) (hc : ‖c‖ ≤ C) (hz : 2*(1+C) ≤ ‖z‖) :
    ‖logCorrection c z‖ ≤ (3/2 : ℝ) * (‖c‖ / ‖z‖^2) := by
  have hzpos : 0 < ‖z‖ := by linarith
  have hterm (n : ℕ) : ‖logCorrectionTerm c z n‖ ≤
      weight (n+1) * ((3/2 : ℝ) * (‖c‖ / ‖z‖^2)) := by
    have hn := exterior_orbit_norm_lower C c z hC hc hz n
    have hrat : ‖c / (orbit c n z)^2‖ ≤ ‖c‖ / ‖z‖^2 := by
      rw [norm_div, norm_pow]
      exact div_le_div_of_nonneg_left (norm_nonneg c) (pow_pos hzpos 2)
        (pow_le_pow_left₀ hzpos.le hn 2)
    have hlog := Complex.norm_log_one_add_half_le_self
      (exterior_ratio_bound C c z hC hc hz n)
    rw [logCorrectionTerm, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (weight_pos (n+1))]
    exact mul_le_mul_of_nonneg_left
      (hlog.trans (mul_le_mul_of_nonneg_left hrat (by norm_num)))
      (weight_pos (n+1)).le
  have hsum := tsum_of_norm_bounded
    (shifted_weight_hasSum.mul_right ((3/2 : ℝ) * (‖c‖ / ‖z‖^2))) hterm
  simpa only [one_mul, logCorrection] using hsum

private theorem log_correction_norm_le_one (C : ℝ) (c z : ℂ)
    (hC : 0 ≤ C) (hc : ‖c‖ ≤ C) (hz : 2*(1+C) ≤ ‖z‖) :
    ‖logCorrection c z‖ ≤ 1 :=
  tsum_of_norm_bounded shifted_weight_hasSum
    (exterior_log_term_bound C c z hC hc hz)

/-- Reindexing the actual convergent series gives its functional equation. -/
theorem log_correction_step (C : ℝ) (c z : ℂ)
    (hC : 0 ≤ C) (hc : ‖c‖ ≤ C) (hz : 2*(1+C) ≤ ‖z‖) :
    2*logCorrection c z =
      Complex.log (1+c/z^2) + logCorrection c (z^2+c) := by
  have hs := exterior_log_correction_summable C c z hC hc hz
  have htail : (fun n : ℕ => logCorrectionTerm c z (n+1)) =
      (fun n : ℕ => (1/2 : ℂ)*logCorrectionTerm c (z^2+c) n) := by
    funext n
    simp only [logCorrectionTerm, orbit_shift]
    rw [weight_succ]
    push_cast
    ring
  have hzero : logCorrectionTerm c z 0 =
      (1/2 : ℂ)*Complex.log (1+c/z^2) := by
    norm_num [logCorrectionTerm, weight, orbit]
  have hsplit : logCorrection c z = (1/2 : ℂ)*Complex.log (1+c/z^2) +
      (1/2 : ℂ)*logCorrection c (z^2+c) := by
    change (∑' n : ℕ, logCorrectionTerm c z n) = _
    rw [hs.tsum_eq_zero_add, hzero, htail, tsum_mul_left]
    rfl
  linear_combination 2 * hsplit

/-- The constructed exterior function conjugates one actual quadratic
step to squaring at the level of its analytic functional equation. -/
theorem bottcher_semiconjugacy (C : ℝ) (c z : ℂ)
    (hC : 0 ≤ C) (hc : ‖c‖ ≤ C) (hz : 2*(1+C) ≤ ‖z‖) :
    bottcher c (z^2+c) = (bottcher c z)^2 := by
  have hzpos : 0 < ‖z‖ := by linarith
  have hzne : z ≠ 0 := norm_pos_iff.mp hzpos
  have hratio := exterior_ratio_bound C c z hC hc hz 0
  have hq : 1+c/z^2 ≠ 0 :=
    Complex.slitPlane_ne_zero (Complex.mem_slitPlane_of_norm_lt_one (by
      change ‖c/z^2‖ ≤ 1/2 at hratio
      linarith))
  have hfactor : z^2+c = z^2*(1+c/z^2) := by field_simp [hzne] <;> ring
  have hstep := log_correction_step C c z hC hc hz
  calc
    bottcher c (z^2+c) = z^2*(1+c/z^2)*Complex.exp (logCorrection c (z^2+c)) := by
      rw [bottcher, hfactor]
    _ = z^2 * Complex.exp (Complex.log (1+c/z^2) + logCorrection c (z^2+c)) := by
      rw [Complex.exp_add, Complex.exp_log hq]
      ring
    _ = z^2 * Complex.exp (2*logCorrection c z) := by rw [← hstep]
    _ = (bottcher c z)^2 := by
      rw [show 2*logCorrection c z = logCorrection c z + logCorrection c z by ring,
        Complex.exp_add, bottcher]
      ring

theorem log_correction_analyticAt (c z : ℂ) (hz : 2*(1+‖c‖) < ‖z‖) :
    AnalyticAt ℂ (logCorrection c) z := by
  let U : Set ℂ := {w | 2*(1+‖c‖) < ‖w‖}
  have hU : IsOpen U := isOpen_lt continuous_const continuous_norm
  have h := log_correction_analyticOnNhd (fun _ => c) id U hU
    (fun _ _ => analyticAt_const) (fun _ _ => analyticAt_id)
    ‖c‖ (norm_nonneg c) (fun _ _ => le_rfl) (fun _ hw => hw.le)
  exact h z hz

/-- Analyticity is proved on the genuine far exterior in the plane. -/
theorem bottcher_analyticAt (c z : ℂ) (hz : 2*(1+‖c‖) < ‖z‖) :
    AnalyticAt ℂ (bottcher c) z :=
  analyticAt_id.mul (log_correction_analyticAt c z hz).cexp

theorem bottcher_ne_zero (C : ℝ) (c z : ℂ)
    (hC : 0 ≤ C) (hc : ‖c‖ ≤ C) (hz : 2*(1+C) ≤ ‖z‖) :
    bottcher c z ≠ 0 := by
  apply mul_ne_zero _ (Complex.exp_ne_zero _)
  exact norm_pos_iff.mp (by linarith)

/-- The actual orbit-limit potential is exactly the logarithmic modulus
of the constructed exterior function. -/
theorem bottcher_log_norm (C : ℝ) (c z : ℂ)
    (hC : 0 ≤ C) (hc : ‖c‖ ≤ C) (hz : 2*(1+C) ≤ ‖z‖) :
    Real.log ‖bottcher c z‖ = escape c z := by
  have hzne : z ≠ 0 := norm_pos_iff.mp (by linarith)
  rw [bottcher, norm_mul,
    Real.log_mul (norm_ne_zero_iff.mpr hzne)
      (norm_ne_zero_iff.mpr (Complex.exp_ne_zero _)),
    Complex.norm_exp, Real.log_exp]
  exact (exterior_escape_log_correction C c z hC hc hz).symm

/-- An explicit relative error supplies the normalization at infinity. -/
theorem bottcher_relative_error (C : ℝ) (c z : ℂ)
    (hC : 0 ≤ C) (hc : ‖c‖ ≤ C) (hz : 2*(1+C) ≤ ‖z‖) :
    ‖bottcher c z / z - 1‖ ≤ 3*(‖c‖ / ‖z‖^2) := by
  have hzne : z ≠ 0 := norm_pos_iff.mp (by linarith)
  have he : bottcher c z / z = Complex.exp (logCorrection c z) := by
    unfold bottcher
    field_simp [hzne] <;> ring
  rw [he]
  have hfirst := Complex.norm_exp_sub_one_le
    (log_correction_norm_le_one C c z hC hc hz)
  have hsecond := log_correction_norm_bound C c z hC hc hz
  nlinarith

/-- The complex correction tends to zero, with no restriction on the
direction of approach to infinity. -/
theorem log_correction_tendsto_zero (c : ℂ) :
    Tendsto (logCorrection c) (cobounded ℂ) (𝓝 0) := by
  have hlim : Tendsto (fun z : ℂ => (3/2 : ℝ)*(‖c‖ / ‖z‖^2))
      (cobounded ℂ) (𝓝 0) := by
    simpa [norm_inv, div_eq_mul_inv, mul_assoc] using
      (tendsto_const_nhds (x := (3/2 : ℝ)*‖c‖)).mul
        ((tendsto_inv₀_cobounded (α := ℂ)).norm.pow 2)
  apply squeeze_zero_norm' _ hlim
  filter_upwards [eventually_cobounded_le_norm (2*(1+‖c‖))] with z hz
  exact log_correction_norm_bound ‖c‖ c z (norm_nonneg c) le_rfl hz

/-- The exterior function has leading coefficient one at infinity. -/
theorem bottcher_normalization (c : ℂ) :
    Tendsto (fun z : ℂ => bottcher c z / z) (cobounded ℂ) (𝓝 1) := by
  have hlim : Tendsto (fun z : ℂ => Complex.exp (logCorrection c z))
      (cobounded ℂ) (𝓝 1) := by
    simpa only [Complex.exp_zero, Function.comp_def] using
      Complex.continuous_exp.continuousAt.tendsto.comp (log_correction_tendsto_zero c)
  apply hlim.congr'
  filter_upwards [eventually_cobounded_le_norm (2*(1+‖c‖))] with z hz
  have hzne : z ≠ 0 := norm_pos_iff.mp (by linarith [norm_nonneg c])
  unfold bottcher
  field_simp [hzne] <;> ring

/-- The reciprocal expression is defined at zero as well; its value
there is zero by the explicit prefactor. -/
def reciprocal (c w : ℂ) : ℂ :=
  w * Complex.exp (-logCorrection c w⁻¹)

@[simp] theorem reciprocal_zero (c : ℂ) : reciprocal c 0 = 0 := by
  simp only [reciprocal, zero_mul]

/-- This is exactly the exterior function in reciprocal coordinates. -/
theorem reciprocal_eq_inverse (c w : ℂ) :
    reciprocal c w = (bottcher c w⁻¹)⁻¹ := by
  simp only [reciprocal, bottcher, mul_inv_rev, inv_inv, Complex.exp_neg]
  ring

/-- Normalization at infinity gives derivative one at the added point. -/
theorem reciprocal_hasDerivAt_zero (c : ℂ) :
    HasDerivAt (reciprocal c) 1 0 := by
  have hs : Tendsto (fun w : ℂ => logCorrection c w⁻¹)
      (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
    (log_correction_tendsto_zero c).comp tendsto_inv₀_nhdsNE_zero
  have hlim : Tendsto (fun w : ℂ => Complex.exp (-logCorrection c w⁻¹))
      (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
    simpa only [neg_zero, Complex.exp_zero, Function.comp_def] using
      Complex.continuous_exp.continuousAt.tendsto.comp hs.neg
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hne : w ≠ 0 := hw
  simp only [zero_add, reciprocal_zero, sub_zero, smul_eq_mul, reciprocal, zero_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- The reciprocal function is analytic across the added point at
infinity; this is derived from the constructed exterior function. -/
theorem reciprocal_analyticAt_zero (c : ℂ) :
    AnalyticAt ℂ (reciprocal c) 0 := by
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · have hlarge : ∀ᶠ w : ℂ in 𝓝[≠] (0 : ℂ), 2*(1+‖c‖) < ‖w⁻¹‖ :=
      tendsto_norm_inv_nhdsNE_zero_atTop.eventually_gt_atTop _
    filter_upwards [hlarge, self_mem_nhdsWithin] with w hw hne
    have hi : AnalyticAt ℂ (fun v : ℂ => v⁻¹) w := analyticAt_id.inv hne
    have hS := (log_correction_analyticAt c w⁻¹ hw).comp hi
    exact (analyticAt_id.mul hS.neg.cexp).differentiableAt
  · exact (reciprocal_hasDerivAt_zero c).continuousAt

/-- In reciprocal coordinates the actual quadratic germ is the rational
map `w²/(1+c*w²)`, and the constructed coordinate sends it to squaring. -/
theorem reciprocal_semiconjugacy (c : ℂ) :
    ∀ᶠ w in 𝓝 (0 : ℂ),
      reciprocal c (w^2/(1+c*w^2)) = (reciprocal c w)^2 := by
  have hpunct : ∀ᶠ w : ℂ in 𝓝[≠] (0 : ℂ),
      reciprocal c (w^2/(1+c*w^2)) = (reciprocal c w)^2 := by
    have hlarge : ∀ᶠ w : ℂ in 𝓝[≠] (0 : ℂ), 2*(1+‖c‖) ≤ ‖w⁻¹‖ :=
      tendsto_norm_inv_nhdsNE_zero_atTop.eventually_ge_atTop _
    filter_upwards [hlarge, self_mem_nhdsWithin] with w hw hne
    have hwne : w ≠ 0 := hne
    have hquot : (w⁻¹)^2+c = (1+c*w^2)/w^2 := by
      field_simp [hwne] <;> ring
    have hrat : w^2/(1+c*w^2) = ((w⁻¹)^2+c)⁻¹ := by
      rw [hquot, inv_div]
    rw [hrat, reciprocal_eq_inverse, inv_inv,
      bottcher_semiconjugacy ‖c‖ c w⁻¹ (norm_nonneg c) le_rfl hw,
      reciprocal_eq_inverse]
    simp only [inv_pow]
  have hnear : ∀ᶠ w in 𝓝 (0 : ℂ), w ≠ 0 →
      reciprocal c (w^2/(1+c*w^2)) = (reciprocal c w)^2 :=
    eventually_nhdsWithin_iff.mp hpunct
  filter_upwards [hnear] with w hw
  by_cases hzero : w = 0
  · subst w
    simp only [zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, add_zero,
      zero_div, reciprocal_zero]
  · exact hw hzero

/-- An analytic inverse is actually constructed at infinity. Combined
with `reciprocal_semiconjugacy`, this is a local analytic Böttcher chart,
with both coordinate and inverse normalized to derivative one. -/
theorem reciprocal_local_coordinate (c : ℂ) :
    ∃ ψ : ℂ → ℂ,
      ψ 0 = 0 ∧ AnalyticAt ℂ ψ 0 ∧ HasDerivAt ψ 1 0 ∧
      (∀ᶠ w in 𝓝 (0 : ℂ), ψ (reciprocal c w) = w) ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), reciprocal c (ψ t) = t) := by
  have hf := reciprocal_analyticAt_zero c
  have hd := reciprocal_hasDerivAt_zero c
  have hderiv : deriv (reciprocal c) 0 ≠ 0 := by rw [hd.deriv]; norm_num
  let ψ := hf.hasStrictDerivAt.localInverse
    (reciprocal c) (deriv (reciprocal c) 0) 0 hderiv
  have hleft : ∀ᶠ w in 𝓝 (0 : ℂ), ψ (reciprocal c w) = w :=
    HasStrictDerivAt.eventually_left_inverse ..
  have hright : ∀ᶠ t in 𝓝 (reciprocal c 0), reciprocal c (ψ t) = t :=
    HasStrictDerivAt.eventually_right_inverse ..
  have hinv : HasDerivAt ψ (deriv (reciprocal c) 0)⁻¹ (reciprocal c 0) :=
    (hf.hasStrictDerivAt.to_localInverse hderiv).hasDerivAt
  refine ⟨ψ, ?_, ?_, ?_, hleft, ?_⟩
  · simpa only [reciprocal_zero] using hleft.self_of_nhds
  · simpa only [reciprocal_zero] using hf.analyticAt_localInverse hderiv
  · simpa only [reciprocal_zero, hd.deriv, inv_one] using hinv
  · simpa only [reciprocal_zero] using hright

/-- The constructed function is an actual analytic coordinate on a
sufficiently far exterior. Injectivity follows from its proved analytic
inverse at infinity. -/
theorem bottcher_exterior_coordinate (c : ℂ) :
    ∃ R : ℝ, 0 < R ∧ 2*(1+‖c‖) ≤ R ∧
      AnalyticOnNhd ℂ (bottcher c) {z | R < ‖z‖} ∧
      Set.InjOn (bottcher c) {z | R < ‖z‖} := by
  obtain ⟨ψ, _, _, _, hleft, _⟩ := reciprocal_local_coordinate c
  have hfar : ∀ᶠ z in cobounded ℂ, ψ (reciprocal c z⁻¹) = z⁻¹ :=
    (tendsto_inv₀_cobounded (α := ℂ)).eventually hleft
  rw [Filter.hasBasis_cobounded_norm.eventually_iff] at hfar
  obtain ⟨r, _, hr⟩ := hfar
  let R := max (2*(1+‖c‖)) r
  have hR : 2*(1+‖c‖) ≤ R := le_max_left _ _
  have hrR : r ≤ R := le_max_right _ _
  refine ⟨R, by linarith [norm_nonneg c], hR, ?_, ?_⟩
  · intro z hz
    exact bottcher_analyticAt c z (hR.trans_lt hz)
  · intro z hz w hw hsame
    have hzinv := hr (hrR.trans hz.le)
    have hwinv := hr (hrR.trans hw.le)
    have hinv : z⁻¹ = w⁻¹ := by
      calc
        z⁻¹ = ψ (reciprocal c z⁻¹) := hzinv.symm
        _ = ψ (reciprocal c w⁻¹) := by
          rw [reciprocal_eq_inverse, reciprocal_eq_inverse, inv_inv, inv_inv, hsame]
        _ = w⁻¹ := hwinv
    simpa only [inv_inv] using congrArg (fun u : ℂ => u⁻¹) hinv

end

end QuadraticBottcherExterior
