import ThreeLevelSelection
import TwoLevelPhysicalGate

/-!
# Complete terminal geometry of the three-level quadratic family

The perturbation is applied after both moving normalizations have been
accounted for. Complete intermediate phases exclude additional sign
collisions, so the terminal restriction is selected from the full pullback.
-/

namespace ThreeLevelTerminal

open Set Function Metric
open LimitingCrestQuadraticReturn LimitingCrest NearTwoShooting
open TwoLevelOuterChart TwoLevelConjugacy ThreeLevelSelection

noncomputable section

theorem chart_reference_output {q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) {a b l u t : ℝ}
    (h : SharpChart r a b) (g : OuterChart q a b l u) (ht : t ∈ Icc l u)
    {z : ℂ} (hz : ‖z‖ ≤ 23/20) :
    ‖normalizedReturn t (r*q) z‖ ≤ 4 := by
  have hk := h.coefficient_range (g.monic_range ht)
  have hk0 : 0 ≤ kappa r (monicParameter q t) := by linarith [hk.1]
  have he := ThreeLevelReference.chart_normalized_error_tight hr hqr h g ht z hz
  have hz2 := pow_le_pow_left₀ (norm_nonneg z) hz 2
  have hlead : ‖(kappa r (monicParameter q t) : ℂ)*z^2‖ ≤
      (9/5 : ℝ)*(23/20)^2 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk0]
    exact mul_le_mul (by linarith [hk.2]) hz2 (sq_nonneg _) (by norm_num)
  have ht1 := norm_sub_le (1 : ℂ) ((kappa r (monicParameter q t) : ℂ)*z^2)
  simp only [norm_one] at ht1
  change ‖complexMap (kappa r (monicParameter q t)) z‖ ≤ _ at ht1
  have ht2 := norm_le_norm_sub_add (normalizedReturn t (r*q) z)
    (complexMap (kappa r (monicParameter q t)) z)
  linarith

theorem chart_moving_model {p q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) (hp : 20*(r*q)+100 ≤ p)
    {a b l u L U c : ℝ} (h : SharpChart r a b)
    (g : OuterChart q a b l u) (j : OuterChart p l u L U) (hc : c ∈ Icc L U)
    {z : ℂ} (hz : ‖z‖ ≤ 23/20) (n : ℕ) (hn : n ≤ r*q) :
    ‖((quadraticMap (monicParameter p c))^[n])
      ((secondScale c p (r*q) : ℂ)*z)‖ ≤ 21/10 := by
  have hd := ThreeLevelReference.terminal_scale_negative hr hqr h g (j.monic_range hc)
  obtain ⟨hw,hi⟩ := ThreeLevelPerturbation.moving_scale_input
    (criticalValue (monicParameter p c) (r*q)) (secondScale c p (r*q)) hd.ne
    (chart_scale_relative hr hqr hp h g j hc) hz
  rw [← hi]
  exact ThreeLevelReference.physical_orbit_disk hr hqr h g (j.monic_range hc) hw n hn

theorem chart_normalized_error {p q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) (hp : 20*(r*q)+100 ≤ p)
    {a b l u L U c : ℝ} (h : SharpChart r a b)
    (g : OuterChart q a b l u) (j : OuterChart p l u L U) (hc : c ∈ Icc L U)
    (z : ℂ) (hz : ‖z‖ ≤ 23/20) :
    ‖normalizedReturn c ((r*q)*p) z-
      complexMap (kappa r (monicParameter q (monicParameter p c))) z‖ ≤ 1/500000 := by
  have hd := ThreeLevelReference.terminal_scale_negative hr hqr h g (j.monic_range hc)
  have hdlo := ThreeLevelReference.terminal_scale_lower hr hqr h g (j.monic_range hc)
  have hrelative : error p*(5 : ℝ)^(r*q) ≤
      |criticalValue (monicParameter p c) (r*q)|/2 := by
    have hb := error_budget hr hqr hp (show r*q ≤ 12*(r*q) by omega)
    nlinarith only [hb, hdlo, (ThreeLevelSelection.product_scale_pos q r).le]
  obtain ⟨hDne,he⟩ := ThreeLevelPerturbation.normalized_iterate_stability
    (outerMap c p) (monicParameter p c) (r*q) (error p)
    (criticalValue (monicParameter p c) (r*q)) (secondScale c p (r*q))
    (23/20) 4 (error_nonneg p) hd.ne
    (small_error_budget hr hqr hp (by omega)) hrelative
    (chart_scale_error hr hqr hp h g j hc)
    (fun w hw => j.outerMap_error (by omega) hc w hw) hz
    (chart_moving_model hr hqr hp h g j hc hz)
    (fun n hn => ThreeLevelReference.physical_orbit_disk hr hqr h g (j.monic_range hc)
      (hz.trans (by norm_num)) n hn)
    (chart_reference_output hr hqr h g (j.monic_range hc) hz)
  rw [second_normalization_eq c p (r*q)
    (coefficient_negative (j.coefficient_lower c hc)).ne hDne z] at he
  change ‖normalizedReturn c ((r*q)*p) z-
    normalizedReturn (monicParameter p c) (r*q) z‖ ≤ _ at he
  have hbound : 2*(1+(23/20 : ℝ)+4)*error p*(5 : ℝ)^(2*(r*q))/
      |criticalValue (monicParameter p c) (r*q)| ≤ 1/1000000 := by
    apply (div_le_iff₀ (abs_pos.mpr hd.ne)).mpr
    have hb := error_budget hr hqr hp (show 2*(r*q) ≤ 12*(r*q) by omega)
    nlinarith only [hb, hdlo, (ThreeLevelSelection.product_scale_pos q r).le]
  have href := ThreeLevelReference.chart_normalized_error_tight hr hqr h g
    (j.monic_range hc) z hz
  have htri : ‖normalizedReturn c ((r*q)*p) z-
      complexMap (kappa r (monicParameter q (monicParameter p c))) z‖ ≤
      ‖normalizedReturn c ((r*q)*p) z-normalizedReturn (monicParameter p c) (r*q) z‖+
      ‖normalizedReturn (monicParameter p c) (r*q) z-
        complexMap (kappa r (monicParameter q (monicParameter p c))) z‖ := by
    simpa only [dist_eq_norm] using dist_triangle
      (normalizedReturn c ((r*q)*p) z) (normalizedReturn (monicParameter p c) (r*q) z)
      (complexMap (kappa r (monicParameter q (monicParameter p c))) z)
  linarith

theorem chart_collision {p q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) (hp : 20*(r*q)+100 ≤ p)
    {a b l u L U c : ℝ} (h : SharpChart r a b)
    (g : OuterChart q a b l u) (j : OuterChart p l u L U) (hc : c ∈ Icc L U)
    {z w : ℂ} (hz : ‖z‖ ≤ 23/20) (hw : ‖w‖ ≤ 23/20) :
    normalizedReturn c ((r*q)*p) z = normalizedReturn c ((r*q)*p) w ↔
      z = w ∨ z = -w := by
  have hd := ThreeLevelReference.terminal_scale_negative hr hqr h g (j.monic_range hc)
  have hD := chart_scale_negative hr hqr hp h g j hc
  have hrel := chart_scale_relative hr hqr hp h g j hc
  obtain ⟨hz',hzi⟩ := ThreeLevelPerturbation.moving_scale_input
    (criticalValue (monicParameter p c) (r*q)) (secondScale c p (r*q)) hd.ne hrel hz
  obtain ⟨hw',hwi⟩ := ThreeLevelPerturbation.moving_scale_input
    (criticalValue (monicParameter p c) (r*q)) (secondScale c p (r*q)) hd.ne hrel hw
  have hbudget : error p*(5 : ℝ)^(r*q) ≤ scale q := by
    have hb := error_budget hr hqr hp (show r*q ≤ 12*(r*q) by omega)
    have hs := mul_le_mul_of_nonneg_left
      (show scale r ≤ 1 by exact pow_le_one₀ (by norm_num) (by norm_num)) (scale_pos q).le
    nlinarith only [hb, hs, (scale_pos q).le]
  have hraw := ThreeLevelReference.perturbed_complete_collision (outerMap c p)
    hr hqr h g (j.monic_range hc) (error p) (error_nonneg p) hbudget
    (fun v hv => j.outerMap_error (by omega) hc v hv)
    (fun hv hx => TwoLevelOuterChart.outerMap_collision_iff (by omega)
      (j.critical_orbit c hc) (j.coefficient_lower c hc) hv hx) hz' hw'
  rw [hzi,hwi] at hraw
  have hDC : (secondScale c p (r*q) : ℂ) ≠ 0 := by exact_mod_cast hD.ne
  have hdC : (criticalValue (monicParameter p c) (r*q) : ℂ) ≠ 0 := by exact_mod_cast hd.ne
  have hratio : (secondScale c p (r*q) : ℂ)/
      (criticalValue (monicParameter p c) (r*q) : ℂ) ≠ 0 := div_ne_zero hDC hdC
  rw [← second_normalization_eq c p (r*q)
      (coefficient_negative (j.coefficient_lower c hc)).ne hD.ne z,
    ← second_normalization_eq c p (r*q)
      (coefficient_negative (j.coefficient_lower c hc)).ne hD.ne w,
    div_left_inj' hDC, hraw]
  constructor
  · rintro (he | he)
    · exact Or.inl (mul_left_cancel₀ hratio he)
    · exact Or.inr (mul_left_cancel₀ hratio (by simpa only [mul_neg] using he))
  · rintro (he | he)
    · exact Or.inl (congrArg (fun v : ℂ =>
        (secondScale c p (r*q) : ℂ)/(criticalValue (monicParameter p c) (r*q) : ℂ)*v) he)
    · exact Or.inr (by rw [he,mul_neg])

theorem chart_phase_disk {p q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) (hp : 20*(r*q)+100 ≤ p)
    {a b l u L U c : ℝ} (h : SharpChart r a b)
    (g : OuterChart q a b l u) (j : OuterChart p l u L U) (hc : c ∈ Icc L U)
    {z : ℂ} (hz : ‖z‖ ≤ 23/20) (n : ℕ) (hn : n ≤ r*q) :
    ‖((outerMap c p)^[n]) ((secondScale c p (r*q) : ℂ)*z)‖ ≤ 12/5 :=
  (TwoLevelPerturbation.iterate_stability (outerMap c p) (monicParameter p c)
    ((secondScale c p (r*q) : ℂ)*z) (r*q) (error p) (error_nonneg p)
    (small_error_budget hr hqr hp (by omega))
    (fun v hv => j.outerMap_error (by omega) hc v hv)
    (chart_moving_model hr hqr hp h g j hc hz) n hn).2

/-- The complete terminal source and closed gate are conclusions about
the original polynomial, with no prescribed domain or degree premise. -/
theorem chart_central_gate {p q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) (hp : 20*(r*q)+100 ≤ p)
    {a b l u L U c : ℝ} (h : SharpChart r a b)
    (g : OuterChart q a b l u) (j : OuterChart p l u L U) (hc : c ∈ Icc L U) :
    TwoLevelGateDomain.CentralGate c ((r*q)*p) := by
  apply TwoLevelGateDomain.central_gate_of_estimates c ((r*q)*p)
    (Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega))
    (physical_scale_positive hr hqr hp h g j hc).ne'
    (h.coefficient_range (g.monic_range (j.monic_range hc)))
    (chart_normalized_error hr hqr hp h g j hc)
  exact fun hz hw => chart_collision hr hqr hp h g j hc hz hw

end
end ThreeLevelTerminal
