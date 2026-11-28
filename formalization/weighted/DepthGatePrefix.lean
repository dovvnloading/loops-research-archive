import DepthGateChart

/-!
# Prefixing a quantitative physical terminal chart

A sufficiently long literal outer return preserves all terminal estimates.
The argument controls every ordinary phase, including the phases between
coarse returns, and retains the signed moving critical scale.
-/

namespace DepthGate
namespace TerminalChart

open Set Function Metric
open LimitingCrestQuadraticReturn LimitingCrest NearTwoShooting
open TwoLevelOuterChart TwoLevelConjugacy

noncomputable section

theorem budget_le_margin (C : TerminalChart) : C.budget ≤ C.margin/10000 := by
  have hb : C.buffer ≤ 1 := by linarith [C.buffer_le]
  have hs : C.slack ≤ 1 := by linarith [C.slack_le]
  have hbs := mul_le_mul hb hs C.slack_pos.le (by norm_num : (0 : ℝ) ≤ 1)
  have hm := mul_le_mul_of_nonneg_left hbs C.margin_pos.le
  unfold budget
  nlinarith only [hm]

theorem budget_le_margin_buffer (C : TerminalChart) :
    C.budget ≤ C.margin*C.buffer/10000 := by
  have hs : C.slack ≤ 1 := by linarith [C.slack_le]
  have hm := mul_le_mul_of_nonneg_left hs (mul_pos C.margin_pos C.buffer_pos).le
  unfold budget
  nlinarith only [hm]

theorem budget_le_margin_slack (C : TerminalChart) :
    C.budget ≤ C.margin*C.slack/10000 := by
  have hb : C.buffer ≤ 1 := by linarith [C.buffer_le]
  have hm := mul_le_mul_of_nonneg_left hb (mul_pos C.margin_pos C.slack_pos).le
  unfold budget
  nlinarith only [hm]

theorem budget_le_tenth (C : TerminalChart) : C.budget ≤ 1/10 := by
  linarith [C.budget_le_margin, C.margin_le]

theorem prefix_error_bound (C : TerminalChart) {p n : ℕ}
    (hp : C.AdmissiblePrefix p) (hn : n ≤ 6*C.period) :
    128*scale p*(5 : ℝ)^n ≤ C.budget := by
  have hpow := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 5) hn
  exact (mul_le_mul_of_nonneg_left hpow
    (mul_nonneg (by norm_num) (scale_pos p).le)).trans hp.2

theorem prefix_margin_le (C : TerminalChart) {p : ℕ} (hp : C.AdmissiblePrefix p) :
    C.prefixMargin p ≤ 1/100 := by
  have hs : scale p ≤ 1 := by linarith [scale_small hp.1]
  have hm := mul_le_mul_of_nonneg_left hs C.margin_pos.le
  unfold prefixMargin
  nlinarith only [hm, C.margin_le]

theorem prefix_margin_weighted (C : TerminalChart) {p : ℕ}
    (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U) :
    |returnCoefficient p c| * C.prefixMargin p ≤ C.margin/400 := by
  have hab := (ThreeLevelReference.coefficient_scale_bounds hp.1 j hc).2
  have hm := mul_le_mul_of_nonneg_left hab C.margin_pos.le
  unfold prefixMargin
  nlinarith only [hm]

theorem prefix_coefficient_large (C : TerminalChart) {p : ℕ}
    (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U) :
    (100 : ℝ) ≤ |returnCoefficient p c| := by
  have hab := (ThreeLevelReference.coefficient_scale_bounds hp.1 j hc).1
  by_contra! hh
  have hm := mul_le_mul_of_nonneg_right hh.le (scale_pos p).le
  nlinarith only [hab, hm, scale_small hp.1]

/-- A common error bound for every finite reference disk used by a tower. -/
theorem prefix_iterate_error (C : TerminalChart) {p : ℕ}
    (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U)
    {N : ℕ} (hN : N ≤ C.period) {v : ℂ}
    (hv : ∀ k : ℕ, k ≤ N → ‖((quadraticMap (monicParameter p c))^[k]) v‖ ≤ 21/10)
    (n : ℕ) (hn : n ≤ N) :
    ‖((outerMap c p)^[n]) v-((quadraticMap (monicParameter p c))^[n]) v‖ ≤ C.budget := by
  have hb : 128*scale p*(5 : ℝ)^N ≤ 1/10 :=
    (C.prefix_error_bound hp (by omega : N ≤ 6*C.period)).trans C.budget_le_tenth
  have he := (TwoLevelPerturbation.iterate_stability (outerMap c p)
    (monicParameter p c) v N (128*scale p)
    (mul_nonneg (by norm_num) (scale_pos p).le) hb
    (fun w hw => j.outerMap_error hp.1 hc w hw) hv n hn).1
  have hsmall := C.prefix_error_bound hp (by omega : n ≤ 6*C.period)
  nlinarith only [he, hsmall]

theorem prefix_iterate_norm (C : TerminalChart) {p : ℕ}
    (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U)
    {N : ℕ} (hN : N ≤ C.period) {v : ℂ}
    (hv : ∀ k : ℕ, k ≤ N → ‖((quadraticMap (monicParameter p c))^[k]) v‖ ≤ 21/10)
    (n : ℕ) (hn : n ≤ N) : ‖((outerMap c p)^[n]) v‖ ≤ 11/5 := by
  have he := C.prefix_iterate_error hp j hc hN hv n hn
  have ht := norm_le_norm_sub_add (((outerMap c p)^[n]) v)
    (((quadraticMap (monicParameter p c))^[n]) v)
  linarith [hv n hn, C.budget_le_tenth]

/-- The sharper coarse bound leaves room inside the existing sixteen-scale nucleus. -/
theorem prefix_coarse_bound (C : TerminalChart) {p : ℕ}
    (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U)
    {N : ℕ} (hN : N ≤ C.period) {v : ℂ}
    (hv : ∀ k : ℕ, k ≤ N → ‖((quadraticMap (monicParameter p c))^[k]) v‖ ≤ 21/10)
    (n : ℕ) (hn : n ≤ N) :
    ‖((quadraticMap c)^[n*p]) (v/(returnCoefficient p c : ℂ))‖ ≤ (44/3)*scale p := by
  have hA := coefficient_negative (j.coefficient_lower c hc)
  have hAa : 0 < |returnCoefficient p c| := abs_pos.mpr hA.ne
  have he := C.prefix_iterate_norm hp j hc hN hv n hn
  rw [outerMap_iterate_scale c p hA.ne, norm_mul, Complex.norm_real, Real.norm_eq_abs] at he
  have hab := (ThreeLevelReference.coefficient_scale_bounds hp.1 j hc).1
  calc
    ‖((quadraticMap c)^[n*p]) (v/(returnCoefficient p c : ℂ))‖ ≤
        (11/5)/|returnCoefficient p c| := (le_div_iff₀ hAa).mpr (by nlinarith only [he])
    _ ≤ (44/3)*scale p := (div_le_iff₀ hAa).mpr (by nlinarith only [hab])

theorem prefix_coarse_small (C : TerminalChart) {p : ℕ}
    (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U)
    {N : ℕ} (hN : N ≤ C.period) {v : ℂ}
    (hv : ∀ k : ℕ, k ≤ N → ‖((quadraticMap (monicParameter p c))^[k]) v‖ ≤ 21/10)
    (n : ℕ) (hn : n ≤ N) :
    ‖((quadraticMap c)^[n*p]) (v/(returnCoefficient p c : ℂ))‖ ≤ 15*scale p := by
  have hb := C.prefix_coarse_bound hp j hc hN hv n hn
  linarith [scale_pos p]

theorem prefix_lifted_orbit (C : TerminalChart) {p : ℕ}
    (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U)
    {N : ℕ} (hN : N ≤ C.period) {v : ℂ}
    (hv : ∀ k : ℕ, k ≤ N → ‖((quadraticMap (monicParameter p c))^[k]) v‖ ≤ 21/10)
    (n : ℕ) (hn : n ≤ N*p) :
    ‖((quadraticMap c)^[n]) (v/(returnCoefficient p c : ℂ))‖ ≤ 21/10 := by
  have hp0 : 0 < p := by have := hp.1; omega
  have hi : n%p < p := Nat.mod_lt n hp0
  have he := Nat.mod_add_div n p
  have hk : n/p ≤ N := by
    by_contra! hh
    have hm := Nat.mul_le_mul_right p (show N+1 ≤ n/p by omega)
    nlinarith only [hn, he, hm, hp0, Nat.zero_le (n%p)]
  have hnform : n = n%p+(n/p)*p := by nlinarith only [he]
  rw [hnform, iterate_add_apply]
  exact ThreeLevelReference.small_disk_orbit hp.1
    (ThreeLevelReference.chart_parameter_band hp.1 j hc)
    (C.prefix_coarse_small hp j hc hN hv (n/p) hk) (n%p) hi.le

theorem prefix_residual_lower (C : TerminalChart) {p : ℕ}
    (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U)
    {v : ℂ} (hv : ‖v‖ ≤ 15*scale p) (i : ℕ) (hi : 1 ≤ i) (hip : i < p) :
    (6/5 : ℝ) ≤ ‖((quadraticMap c)^[i]) v‖ := by
  have hd := ThreeLevelReference.small_disk_displacement hp.1
    (ThreeLevelReference.chart_parameter_band hp.1 j hc) hv i (by omega) hip.le
  have hx := ThreeLevelReference.outer_phase_abs hp.1 j hc hi hip
  have ht := norm_le_norm_sub_add (criticalValue c i : ℂ) (((quadraticMap c)^[i]) v)
  rw [norm_sub_rev, Complex.norm_real, Real.norm_eq_abs] at ht
  linarith [scale_small hp.1]

theorem prefix_residual_pair (C : TerminalChart) {p : ℕ}
    (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U)
    {v w : ℂ} (hv : ‖v‖ ≤ 15*scale p) (hw : ‖w‖ ≤ 15*scale p)
    (i : ℕ) (hi : 1 ≤ i) (hip : i < p) :
    (12/5 : ℝ) ≤ ‖((quadraticMap c)^[i]) v+((quadraticMap c)^[i]) w‖ := by
  have hvd := ThreeLevelReference.small_disk_displacement hp.1
    (ThreeLevelReference.chart_parameter_band hp.1 j hc) hv i (by omega) hip.le
  have hwd := ThreeLevelReference.small_disk_displacement hp.1
    (ThreeLevelReference.chart_parameter_band hp.1 j hc) hw i (by omega) hip.le
  have hx := ThreeLevelReference.outer_phase_abs hp.1 j hc hi hip
  have ht := norm_le_norm_sub_add ((criticalValue c i : ℂ)+(criticalValue c i : ℂ))
    (((quadraticMap c)^[i]) v+((quadraticMap c)^[i]) w)
  have hid : (criticalValue c i : ℂ)+(criticalValue c i : ℂ)-
      (((quadraticMap c)^[i]) v+((quadraticMap c)^[i]) w) =
      ((criticalValue c i : ℂ)-((quadraticMap c)^[i]) v)+
      ((criticalValue c i : ℂ)-((quadraticMap c)^[i]) w) := by ring
  rw [hid] at ht
  have hsub := norm_add_le ((criticalValue c i : ℂ)-((quadraticMap c)^[i]) v)
    ((criticalValue c i : ℂ)-((quadraticMap c)^[i]) w)
  rw [norm_sub_rev (criticalValue c i : ℂ) (((quadraticMap c)^[i]) v),
    norm_sub_rev (criticalValue c i : ℂ) (((quadraticMap c)^[i]) w)] at hsub
  have hnorm : ‖(criticalValue c i : ℂ)+(criticalValue c i : ℂ)‖ =
      2*|criticalValue c i| := by
    rw [← two_mul, norm_mul]
    norm_num [Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm] at ht
  linarith [scale_small hp.1]


/-- Pair separation survives every original time, not only coarse checkpoints. -/
theorem prefix_lifted_pair (C : TerminalChart) {p : ℕ}
    (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U)
    {N : ℕ} (hN : N ≤ C.period) {v w : ℂ}
    (hv : ∀ k : ℕ, k ≤ N → ‖((quadraticMap (monicParameter p c))^[k]) v‖ ≤ 21/10)
    (hw : ∀ k : ℕ, k ≤ N → ‖((quadraticMap (monicParameter p c))^[k]) w‖ ≤ 21/10)
    (hpair : ∀ k : ℕ, 1 ≤ k → k < N → C.margin ≤
      ‖((quadraticMap (monicParameter p c))^[k]) v+
        ((quadraticMap (monicParameter p c))^[k]) w‖)
    (n : ℕ) (hn : 1 ≤ n) (hnN : n < N*p) :
    C.prefixMargin p ≤ ‖((quadraticMap c)^[n]) (v/(returnCoefficient p c : ℂ))+
      ((quadraticMap c)^[n]) (w/(returnCoefficient p c : ℂ))‖ := by
  have hp0 : 0 < p := by have := hp.1; omega
  have hi : n%p < p := Nat.mod_lt n hp0
  have he := Nat.mod_add_div n p
  have hk : n/p < N := by
    by_contra! hh
    have hm := Nat.mul_le_mul_right p hh
    nlinarith only [hnN, he, hm, Nat.zero_le (n%p)]
  have hnform : n = n%p+(n/p)*p := by nlinarith only [he]
  by_cases hi0 : n%p = 0
  · have hk1 : 1 ≤ n/p := by
      by_contra! hh
      have hk0 : n/p = 0 := by omega
      rw [hi0, hk0] at hnform
      omega
    have hncoarse : n = (n/p)*p := by simpa only [hi0, zero_add] using hnform
    have hvE := C.prefix_iterate_error hp j hc hN hv (n/p) hk.le
    have hwE := C.prefix_iterate_error hp j hc hN hw (n/p) hk.le
    have htri := norm_le_norm_sub_add
      (((quadraticMap (monicParameter p c))^[n/p]) v+
        ((quadraticMap (monicParameter p c))^[n/p]) w)
      (((outerMap c p)^[n/p]) v+((outerMap c p)^[n/p]) w)
    have hdiff : ‖(((quadraticMap (monicParameter p c))^[n/p]) v+
        ((quadraticMap (monicParameter p c))^[n/p]) w)-
        (((outerMap c p)^[n/p]) v+((outerMap c p)^[n/p]) w)‖ ≤ 2*C.budget := by
      calc
        _ = ‖(((quadraticMap (monicParameter p c))^[n/p]) v-
            ((outerMap c p)^[n/p]) v)+
            (((quadraticMap (monicParameter p c))^[n/p]) w-
            ((outerMap c p)^[n/p]) w)‖ := by congr 1; ring
        _ ≤ ‖((quadraticMap (monicParameter p c))^[n/p]) v-
              ((outerMap c p)^[n/p]) v‖ + 
            ‖((quadraticMap (monicParameter p c))^[n/p]) w-
              ((outerMap c p)^[n/p]) w‖ := norm_add_le _ _
        _ ≤ 2*C.budget := by
          rw [norm_sub_rev (((quadraticMap (monicParameter p c))^[n/p]) v)
              (((outerMap c p)^[n/p]) v),
            norm_sub_rev (((quadraticMap (monicParameter p c))^[n/p]) w)
              (((outerMap c p)^[n/p]) w)]
          linarith
    have hcoarse : C.margin-2*C.budget ≤
        ‖((outerMap c p)^[n/p]) v+((outerMap c p)^[n/p]) w‖ := by
      linarith [hpair (n/p) hk1 hk]
    have hA := coefficient_negative (j.coefficient_lower c hc)
    have hAa : 0 < |returnCoefficient p c| := abs_pos.mpr hA.ne
    rw [outerMap_iterate_scale c p hA.ne (n/p) v,
      outerMap_iterate_scale c p hA.ne (n/p) w,
      ← mul_add, norm_mul, Complex.norm_real, Real.norm_eq_abs] at hcoarse
    rw [hncoarse]
    apply (mul_le_mul_left hAa).mp
    have hm := C.prefix_margin_weighted hp j hc
    nlinarith only [hcoarse, hm, C.budget_le_margin, C.margin_pos.le]
  · have hi1 : 1 ≤ n%p := by omega
    have hres := C.prefix_residual_pair hp j hc
      (C.prefix_coarse_small hp j hc hN hv (n/p) hk.le)
      (C.prefix_coarse_small hp j hc hN hw (n/p) hk.le) (n%p) hi1 hi
    rw [hnform]
    simp only [iterate_add_apply]
    linarith [C.prefix_margin_le hp]

theorem reference_scale_ne (C : TerminalChart) {t : ℝ} (ht : t ∈ Icc C.left C.right) :
    criticalValue t C.period ≠ 0 := by
  apply abs_pos.mp
  exact C.margin_pos.trans_le (C.scale_bounds t ht).1

theorem prefix_scale_error (C : TerminalChart) {p : ℕ}
    (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U) :
    |secondScale c p C.period-criticalValue (monicParameter p c) C.period| ≤
      (5 : ℝ)^C.period*(128*scale p) := by
  have ht := C.parameter_band (j.monic_range hc)
  have hband : monicParameter p c ∈ Icc (-2 : ℝ) 0 := ⟨ht.1, by linarith [ht.2]⟩
  have hb : 128*scale p*(5 : ℝ)^C.period ≤ 1/10 :=
    (C.prefix_error_bound hp (by omega : C.period ≤ 6*C.period)).trans C.budget_le_tenth
  have he := TwoLevelPerturbation.critical_return_scale_error (outerMap c p)
    (monicParameter p c) hband C.period (128*scale p)
    (mul_nonneg (by norm_num) (scale_pos p).le) hb
    (fun w hw => j.outerMap_error hp.1 hc w hw)
  rw [← secondScale_eq_re c p C.period (coefficient_negative (j.coefficient_lower c hc)).ne] at he
  exact he

theorem prefix_scale_budget (C : TerminalChart) {p : ℕ}
    (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U) :
    |secondScale c p C.period-criticalValue (monicParameter p c) C.period| ≤ C.budget := by
  have he := C.prefix_scale_error hp j hc
  have hb := C.prefix_error_bound hp (by omega : C.period ≤ 6*C.period)
  nlinarith only [he, hb]

/-- The shrinking positive buffer absorbs the signed change of input scale. -/
theorem prefix_moving_input (C : TerminalChart) {p : ℕ}
    (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U)
    {z : ℂ} (hz : ‖z‖ ≤ 23/20+C.buffer/2) :
    ‖((secondScale c p C.period : ℂ)/(criticalValue (monicParameter p c) C.period : ℂ))*z‖ ≤
      C.radius ∧
    (criticalValue (monicParameter p c) C.period : ℂ)*
      (((secondScale c p C.period : ℂ)/(criticalValue (monicParameter p c) C.period : ℂ))*z) =
        (secondScale c p C.period : ℂ)*z := by
  have ht := j.monic_range hc
  have hd := C.reference_scale_ne ht
  have hdabs : 0 < |criticalValue (monicParameter p c) C.period| := abs_pos.mpr hd
  have hdC : (criticalValue (monicParameter p c) C.period : ℂ) ≠ 0 := by exact_mod_cast hd
  have he := C.prefix_scale_budget hp j hc
  have hupper : |secondScale c p C.period| ≤
      |secondScale c p C.period-criticalValue (monicParameter p c) C.period| + 
        |criticalValue (monicParameter p c) C.period| := by
    calc
      _ = |(secondScale c p C.period-criticalValue (monicParameter p c) C.period)+
          criticalValue (monicParameter p c) C.period| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have hmb := mul_le_mul_of_nonneg_right (C.scale_bounds _ ht).1 C.buffer_pos.le
  have hratio : |secondScale c p C.period| /
      |criticalValue (monicParameter p c) C.period| ≤ 1+C.buffer/4 := by
    apply (div_le_iff₀ hdabs).mpr
    nlinarith only [hupper, he, C.budget_le_margin_buffer, hmb,
      (mul_pos C.margin_pos C.buffer_pos).le]
  constructor
  · simp only [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ (1+C.buffer/4)*(23/20+C.buffer/2) :=
        mul_le_mul hratio hz (norm_nonneg z) (by linarith [C.buffer_pos])
      _ ≤ C.radius := by
        unfold radius
        have hb := mul_le_mul_of_nonneg_left C.buffer_le C.buffer_pos.le
        nlinarith only [hb, C.buffer_pos.le]
  · field_simp [hdC]
    <;> ring

theorem prefix_moving_model (C : TerminalChart) {p : ℕ}
    (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U)
    {z : ℂ} (hz : ‖z‖ ≤ 23/20+C.buffer/2) (n : ℕ) (hn : n ≤ C.period) :
    ‖((quadraticMap (monicParameter p c))^[n]) ((secondScale c p C.period : ℂ)*z)‖ ≤ 21/10 := by
  obtain ⟨hw, hi⟩ := C.prefix_moving_input hp j hc hz
  rw [← hi]
  exact C.orbit_bound _ (j.monic_range hc) hw n hn

theorem prefix_input_identity (C : TerminalChart) {p : ℕ} {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U) (z : ℂ) :
    ((secondScale c p C.period : ℂ)*z)/(returnCoefficient p c : ℂ) =
      (criticalValue c (C.period*p) : ℂ)*z := by
  have hA : (returnCoefficient p c : ℂ) ≠ 0 := by
    exact_mod_cast (coefficient_negative (j.coefficient_lower c hc)).ne
  unfold secondScale
  push_cast
  field_simp [hA]
  <;> ring

theorem prefix_scale_bounds (C : TerminalChart) {p : ℕ}
    (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U) :
    C.prefixMargin p ≤ |criticalValue c (C.period*p)| ∧
      |criticalValue c (C.period*p)| ≤ 1/100 := by
  have ht := j.monic_range hc
  have hd := C.reference_scale_ne ht
  have hb : C.budget ≤ |criticalValue (monicParameter p c) C.period| / 2 := by
    linarith [C.budget_le_margin, (C.scale_bounds _ ht).1, C.margin_pos]
  obtain ⟨hlo, hup, _⟩ := ThreeLevelPerturbation.moving_scale_control
    (criticalValue (monicParameter p c) C.period) (secondScale c p C.period) C.budget hd hb
    (C.prefix_scale_budget hp j hc)
  have hid : |secondScale c p C.period| =
      |returnCoefficient p c| * |criticalValue c (C.period*p)| := by
    unfold secondScale
    rw [abs_mul]
  rw [hid] at hlo hup
  have hA := coefficient_negative (j.coefficient_lower c hc)
  have hAa : 0 < |returnCoefficient p c| := abs_pos.mpr hA.ne
  constructor
  · apply (mul_le_mul_left hAa).mp
    have hm := C.prefix_margin_weighted hp j hc
    linarith [(C.scale_bounds _ ht).1, C.margin_pos]
  · apply (mul_le_mul_left hAa).mp
    nlinarith only [hup, (C.scale_bounds _ ht).2, C.prefix_coefficient_large hp j hc]

theorem prefix_terminal_orbit (C : TerminalChart) {p : ℕ}
    (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U)
    {z : ℂ} (hz : ‖z‖ ≤ 23/20+C.buffer/2) (n : ℕ) (hn : n ≤ C.period*p) :
    ‖((quadraticMap c)^[n]) ((criticalValue c (C.period*p) : ℂ)*z)‖ ≤ 21/10 := by
  have he := C.prefix_lifted_orbit hp j hc le_rfl (C.prefix_moving_model hp j hc hz) n hn
  rw [C.prefix_input_identity j hc] at he
  exact he

theorem prefix_terminal_pair (C : TerminalChart) {p : ℕ}
    (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U)
    {z w : ℂ} (hz : ‖z‖ ≤ 23/20+C.buffer/2) (hw : ‖w‖ ≤ 23/20+C.buffer/2)
    (n : ℕ) (hn : 1 ≤ n) (hnN : n < C.period*p) :
    C.prefixMargin p ≤ ‖((quadraticMap c)^[n]) ((criticalValue c (C.period*p) : ℂ)*z)+
      ((quadraticMap c)^[n]) ((criticalValue c (C.period*p) : ℂ)*w)‖ := by
  obtain ⟨hz', hzi⟩ := C.prefix_moving_input hp j hc hz
  obtain ⟨hw', hwi⟩ := C.prefix_moving_input hp j hc hw
  have hpair : ∀ k : ℕ, 1 ≤ k → k < C.period → C.margin ≤
      ‖((quadraticMap (monicParameter p c))^[k]) ((secondScale c p C.period : ℂ)*z)+
        ((quadraticMap (monicParameter p c))^[k]) ((secondScale c p C.period : ℂ)*w)‖ := by
    intro k hk hkN
    rw [← hzi, ← hwi]
    exact C.pair_bound _ (j.monic_range hc) hz' hw' k hk hkN
  have he := C.prefix_lifted_pair hp j hc le_rfl
    (C.prefix_moving_model hp j hc hz) (C.prefix_moving_model hp j hc hw) hpair n hn hnN
  rw [C.prefix_input_identity j hc z, C.prefix_input_identity j hc w] at he
  exact he


/-- A target and a positive reference margin give literal first-return
exclusion after lifting. The half-margin permits a moving terminal target. -/
theorem prefix_lifted_first (C : TerminalChart) {p : ℕ}
    (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U)
    {N : ℕ} (hN : N ≤ C.period) {v : ℂ}
    (hv : ∀ k : ℕ, k ≤ N → ‖((quadraticMap (monicParameter p c))^[k]) v‖ ≤ 21/10)
    {R : ℝ} (hR : 0 ≤ R) (hRle : R ≤ 1/10)
    (hfirst : ∀ k : ℕ, 1 ≤ k → k < N →
      R+C.margin/2 ≤ ‖((quadraticMap (monicParameter p c))^[k]) v‖)
    (n : ℕ) (hn : 1 ≤ n) (hnN : n < N*p) :
    R/|returnCoefficient p c| + C.prefixMargin p ≤
      ‖((quadraticMap c)^[n]) (v/(returnCoefficient p c : ℂ))‖ := by
  have hA := coefficient_negative (j.coefficient_lower c hc)
  have hAa : 0 < |returnCoefficient p c| := abs_pos.mpr hA.ne
  have hp0 : 0 < p := by have := hp.1; omega
  have hi : n%p < p := Nat.mod_lt n hp0
  have he := Nat.mod_add_div n p
  have hk : n/p < N := by
    by_contra! hh
    have hm := Nat.mul_le_mul_right p hh
    nlinarith only [hnN, he, hm, Nat.zero_le (n%p)]
  have hnform : n = n%p+(n/p)*p := by nlinarith only [he]
  by_cases hi0 : n%p = 0
  · have hk1 : 1 ≤ n/p := by
      by_contra! hh
      have hk0 : n/p = 0 := by omega
      rw [hi0, hk0] at hnform
      omega
    have hncoarse : n = (n/p)*p := by simpa only [hi0, zero_add] using hnform
    have hvE := C.prefix_iterate_error hp j hc hN hv (n/p) hk.le
    have htri := norm_le_norm_sub_add
      (((quadraticMap (monicParameter p c))^[n/p]) v) (((outerMap c p)^[n/p]) v)
    rw [norm_sub_rev] at htri
    have hcoarse : R+C.margin/2-C.budget ≤ ‖((outerMap c p)^[n/p]) v‖ := by
      linarith [hfirst (n/p) hk1 hk]
    rw [outerMap_iterate_scale c p hA.ne, norm_mul, Complex.norm_real,
      Real.norm_eq_abs] at hcoarse
    rw [hncoarse]
    calc
      R/|returnCoefficient p c| + C.prefixMargin p =
          (R+|returnCoefficient p c| * C.prefixMargin p)/|returnCoefficient p c| := by
            field_simp [hAa.ne']; ring
      _ ≤ ‖((quadraticMap c)^[(n/p)*p]) (v/(returnCoefficient p c : ℂ))‖ := by
        apply (div_le_iff₀ hAa).mpr
        have hm := C.prefix_margin_weighted hp j hc
        nlinarith only [hcoarse, hm, C.budget_le_margin, C.margin_pos.le]
  · have hi1 : 1 ≤ n%p := by omega
    have hres := C.prefix_residual_lower hp j hc
      (C.prefix_coarse_small hp j hc hN hv (n/p) hk.le) (n%p) hi1 hi
    have hdiv : R/|returnCoefficient p c| ≤ 1/10 := by
      apply (div_le_iff₀ hAa).mpr
      linarith [C.prefix_coefficient_large hp j hc]
    rw [hnform, iterate_add_apply]
    linarith [C.prefix_margin_le hp]

theorem prefix_terminal_first (C : TerminalChart) {p : ℕ}
    (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U)
    {z : ℂ} (hz : ‖z‖ ≤ 23/20+C.buffer/2)
    (n : ℕ) (hn : 1 ≤ n) (hnN : n < C.period*p) :
    |criticalValue c (C.period*p)| * (23/20)+C.prefixMargin p ≤
      ‖((quadraticMap c)^[n]) ((criticalValue c (C.period*p) : ℂ)*z)‖ := by
  obtain ⟨hw, hi⟩ := C.prefix_moving_input hp j hc hz
  have he := C.prefix_scale_budget hp j hc
  have hDupper : |secondScale c p C.period| ≤
      |criticalValue (monicParameter p c) C.period| + C.budget := by
    have ht : |secondScale c p C.period| ≤
        |secondScale c p C.period-criticalValue (monicParameter p c) C.period| + 
          |criticalValue (monicParameter p c) C.period| := by
      calc
        _ = |(secondScale c p C.period-criticalValue (monicParameter p c) C.period)+
            criticalValue (monicParameter p c) C.period| := by congr 1; ring
        _ ≤ _ := abs_add_le _ _
    linarith
  have hR : |secondScale c p C.period| * (23/20) ≤ (1/10 : ℝ) := by
    have hd := (C.scale_bounds _ (j.monic_range hc)).2
    linarith [C.budget_le_margin, C.margin_le]
  have hfirst : ∀ k : ℕ, 1 ≤ k → k < C.period →
      |secondScale c p C.period| * (23/20)+C.margin/2 ≤
        ‖((quadraticMap (monicParameter p c))^[k]) ((secondScale c p C.period : ℂ)*z)‖ := by
    intro k hk hkN
    have href := C.first_bound _ (j.monic_range hc) hw k hk hkN
    rw [hi] at href
    nlinarith only [href, hDupper, C.budget_le_margin, C.margin_pos.le]
  have hraw := C.prefix_lifted_first hp j hc le_rfl
    (C.prefix_moving_model hp j hc hz)
    (R := |secondScale c p C.period| * (23/20))
    (mul_nonneg (abs_nonneg _) (by norm_num)) hR hfirst n hn hnN
  have hAa : |returnCoefficient p c| ≠ 0 :=
    (abs_pos.mpr (coefficient_negative (j.coefficient_lower c hc)).ne).ne'
  have hid : |secondScale c p C.period| * (23/20)/|returnCoefficient p c| =
      |criticalValue c (C.period*p)| * (23/20) := by
    unfold secondScale
    rw [abs_mul]
    field_simp [hAa]
    <;> ring
  rw [hid, C.prefix_input_identity j hc z] at hraw
  exact hraw

theorem reference_output (C : TerminalChart) {t : ℝ} (ht : t ∈ Icc C.left C.right)
    {z : ℂ} (hz : ‖z‖ ≤ 23/20) : ‖normalizedReturn t C.period z‖ ≤ 4 := by
  have hk := C.coefficient_band t ht
  have hk0 : 0 ≤ C.coefficient t := by linarith [hk.1]
  have he := C.normalized_error t ht z hz
  have hz2 := pow_le_pow_left₀ (norm_nonneg z) hz 2
  have hlead : ‖(C.coefficient t : ℂ)*z^2‖ ≤ (9/5 : ℝ)*(23/20)^2 := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk0]
    exact mul_le_mul (by linarith [hk.2]) hz2 (sq_nonneg _) (by norm_num)
  have ht1 := norm_sub_le (1 : ℂ) ((C.coefficient t : ℂ)*z^2)
  simp only [norm_one] at ht1
  change ‖complexMap (C.coefficient t) z‖ ≤ _ at ht1
  have ht2 := norm_le_norm_sub_add (normalizedReturn t C.period z)
    (complexMap (C.coefficient t) z)
  linarith [C.slack_pos]

theorem prefix_normalized_error (C : TerminalChart) {p : ℕ}
    (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U)
    (z : ℂ) (hz : ‖z‖ ≤ 23/20) :
    ‖normalizedReturn c (C.period*p) z-complexMap (C.coefficient (monicParameter p c)) z‖ ≤
      1/500000-C.slack/2 := by
  have ht := j.monic_range hc
  have hd := C.reference_scale_ne ht
  have hdabs : 0 < |criticalValue (monicParameter p c) C.period| := abs_pos.mpr hd
  have hbudget := C.prefix_error_bound hp (by omega : C.period ≤ 6*C.period)
  have hrelative : 128*scale p*(5 : ℝ)^C.period ≤
      |criticalValue (monicParameter p c) C.period| / 2 := by
    linarith [C.budget_le_margin, (C.scale_bounds _ ht).1, C.margin_pos]
  have hz' : ‖z‖ ≤ 23/20+C.buffer/2 := by linarith [C.buffer_pos]
  obtain ⟨hDne, he⟩ := ThreeLevelPerturbation.normalized_iterate_stability
    (outerMap c p) (monicParameter p c) C.period (128*scale p)
    (criticalValue (monicParameter p c) C.period) (secondScale c p C.period)
    (23/20) 4 (mul_nonneg (by norm_num) (scale_pos p).le) hd
    (hbudget.trans C.budget_le_tenth) hrelative
    (C.prefix_scale_error hp j hc) (fun w hw => j.outerMap_error hp.1 hc w hw) hz
    (C.prefix_moving_model hp j hc hz')
    (C.orbit_bound _ ht (show ‖z‖ ≤ 23/20+C.buffer by linarith [C.buffer_pos]))
    (C.reference_output ht hz)
  rw [second_normalization_eq c p C.period
    (coefficient_negative (j.coefficient_lower c hc)).ne hDne z] at he
  change ‖normalizedReturn c (C.period*p) z-normalizedReturn (monicParameter p c) C.period z‖ ≤
    2*(1+(23/20 : ℝ)+4)*(128*scale p)*(5 : ℝ)^(2*C.period)/
      |criticalValue (monicParameter p c) C.period| at he
  have hbound : 2*(1+(23/20 : ℝ)+4)*(128*scale p)*(5 : ℝ)^(2*C.period)/
      |criticalValue (monicParameter p c) C.period| ≤ C.slack/2 := by
    apply (div_le_iff₀ hdabs).mpr
    have hb := C.prefix_error_bound hp (by omega : 2*C.period ≤ 6*C.period)
    have hm := mul_le_mul_of_nonneg_right (C.scale_bounds _ ht).1 C.slack_pos.le
    nlinarith only [hb, C.budget_le_margin_slack, hm,
      (mul_pos C.margin_pos C.slack_pos).le]
  have href := C.normalized_error _ ht z hz
  have htri : ‖normalizedReturn c (C.period*p) z-complexMap (C.coefficient (monicParameter p c)) z‖ ≤
      ‖normalizedReturn c (C.period*p) z-normalizedReturn (monicParameter p c) C.period z‖ + 
      ‖normalizedReturn (monicParameter p c) C.period z-complexMap (C.coefficient (monicParameter p c)) z‖ := by
    simpa only [dist_eq_norm] using dist_triangle
      (normalizedReturn c (C.period*p) z) (normalizedReturn (monicParameter p c) C.period z)
      (complexMap (C.coefficient (monicParameter p c)) z)
  linarith

theorem prefix_relation_error (C : TerminalChart) {p : ℕ}
    (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U) :
    |returnCoefficient p c*(criticalValue c (6*(C.period*p))+criticalValue c (3*(C.period*p)))-
      (criticalValue (monicParameter p c) (6*C.period)+
        criticalValue (monicParameter p c) (3*C.period))| ≤ 2*C.budget := by
  have ht := C.parameter_band (j.monic_range hc)
  have hband : monicParameter p c ∈ Icc (-2 : ℝ) 0 := ⟨ht.1, by linarith [ht.2]⟩
  have hb := C.prefix_error_bound hp (show 6*C.period ≤ 6*C.period from le_rfl)
  have he := TwoLevelPerturbation.signed_relation_stability (outerMap c p)
    (monicParameter p c) hband C.period (128*scale p)
    (mul_nonneg (by norm_num) (scale_pos p).le) (hb.trans C.budget_le_tenth)
    (fun w hw => j.outerMap_error hp.1 hc w hw)
  rw [signed_relation_scale c p C.period (coefficient_negative (j.coefficient_lower c hc)).ne] at he
  exact he.trans (by nlinarith only [hb])

theorem prefix_oriented_relation_error (C : TerminalChart) {p : ℕ}
    (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U) :
    | |returnCoefficient p c| * ((-C.orientation)*
        (criticalValue c (6*(C.period*p))+criticalValue c (3*(C.period*p))))-
      C.orientation*(criticalValue (monicParameter p c) (6*C.period)+
        criticalValue (monicParameter p c) (3*C.period))| ≤ 2*C.budget := by
  have ho : |C.orientation| = 1 := by
    rcases C.orientation_unit with ho | ho <;> rw [ho] <;> norm_num
  have he := C.prefix_relation_error hp j hc
  have hA := coefficient_negative (j.coefficient_lower c hc)
  calc
    _ = |C.orientation*(returnCoefficient p c*
        (criticalValue c (6*(C.period*p))+criticalValue c (3*(C.period*p)))-
        (criticalValue (monicParameter p c) (6*C.period)+
          criticalValue (monicParameter p c) (3*C.period)))| := by
      rw [abs_of_neg hA]
      congr 1
      ring
    _ ≤ 2*C.budget := by rw [abs_mul, ho, one_mul]; exact he

theorem prefix_relation_left (C : TerminalChart) {p : ℕ}
    (hp : C.AdmissiblePrefix p) {L U : ℝ}
    (j : OuterChart p C.left C.right L U) :
    (-C.orientation)*(criticalValue L (6*(C.period*p))+criticalValue L (3*(C.period*p))) ≤
      -C.prefixMargin p := by
  have hc : L ∈ Icc L U := left_mem_Icc.mpr j.ordered.le
  have he := C.prefix_oriented_relation_error hp j hc
  rw [j.left_monicParameter] at he
  have hAa : 0 < |returnCoefficient p L| :=
    abs_pos.mpr (coefficient_negative (j.coefficient_lower L hc)).ne
  apply (mul_le_mul_left hAa).mp
  have hm := C.prefix_margin_weighted hp j hc
  nlinarith only [(abs_le.mp he).2, C.relation_left, hm,
    C.budget_le_margin, C.margin_pos.le]

theorem prefix_relation_right (C : TerminalChart) {p : ℕ}
    (hp : C.AdmissiblePrefix p) {L U : ℝ}
    (j : OuterChart p C.left C.right L U) :
    C.prefixMargin p ≤
      (-C.orientation)*(criticalValue U (6*(C.period*p))+criticalValue U (3*(C.period*p))) := by
  have hc : U ∈ Icc L U := right_mem_Icc.mpr j.ordered.le
  have he := C.prefix_oriented_relation_error hp j hc
  rw [j.right_monicParameter] at he
  have hAa : 0 < |returnCoefficient p U| :=
    abs_pos.mpr (coefficient_negative (j.coefficient_lower U hc)).ne
  apply (mul_le_mul_left hAa).mp
  have hm := C.prefix_margin_weighted hp j hc
  nlinarith only [(abs_le.mp he).1, C.relation_right, hm,
    C.budget_le_margin, C.margin_pos.le]

/-- A closed construction on actual quadratic parameter intervals. Every
new estimate is proved from the old chart and the finite outer budget. -/
def prefix (C : TerminalChart) (p : ℕ) (hp : C.AdmissiblePrefix p)
    {L U : ℝ} (j : OuterChart p C.left C.right L U) : TerminalChart where
  period := C.period*p
  left := L
  right := U
  margin := C.prefixMargin p
  buffer := C.buffer/2
  slack := C.slack/2
  orientation := -C.orientation
  coefficient := fun c => C.coefficient (monicParameter p c)
  period_ge := (by norm_num : 17 ≤ 17*17).trans (Nat.mul_le_mul C.period_ge hp.1)
  ordered := j.ordered
  parameter_band := fun c hc => NearTwoShooting.parameter_band hp.1 (j.parameter_range c hc)
  margin_pos := C.prefixMargin_pos p
  margin_le := C.prefix_margin_le hp
  buffer_pos := by linarith [C.buffer_pos]
  buffer_le := by linarith [C.buffer_le]
  slack_pos := by linarith [C.slack_pos]
  slack_le := by linarith [C.slack_le]
  orientation_unit := by rcases C.orientation_unit with ho | ho <;> simp [ho]
  coefficient_band := fun c hc => C.coefficient_band _ (j.monic_range hc)
  scale_bounds := fun c hc => C.prefix_scale_bounds hp j hc
  orbit_bound := fun c hc _ hz n hn => C.prefix_terminal_orbit hp j hc hz n hn
  pair_bound := fun c hc _ _ hz hw n hn hnN => C.prefix_terminal_pair hp j hc hz hw n hn hnN
  first_bound := fun c hc _ hz n hn hnN => C.prefix_terminal_first hp j hc hz n hn hnN
  normalized_error := fun c hc z hz => C.prefix_normalized_error hp j hc z hz
  relation_left := C.prefix_relation_left hp j
  relation_right := C.prefix_relation_right hp j

end
end TerminalChart
end DepthGate


