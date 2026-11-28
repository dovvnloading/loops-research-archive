import NearTwoShooting
import CriticalReturnRelationStability

/-!
# Reference corridors for a second physical return

These estimates retain a complete parameter interval, rather than selecting
one root of its signed critical relation. They provide the quantitative
reference data used in the perturbation of that interval by a first return.
-/

namespace TwoLevelReference

open Set Function
open NearTwoShooting LimitingCrestQuadraticReturn
open CriticalReturnRelationStability LimitingCrest LimitingCrestPerturbation
open LoopsLimitingCrestParameter

noncomputable section

/-- Every real critical orbit with parameter in `[-2,0]` stays in `[-2,2]`,
including times beyond the first return chart. -/
theorem critical_orbit_bound (c : ℝ) (hc : c ∈ Icc (-2 : ℝ) 0) (n : ℕ) :
    |criticalValue c n| ≤ 2 := by
  have hinterval : ∀ j : ℕ, criticalValue c j ∈ Icc c (-c) := by
    intro j
    induction j with
    | zero =>
      change c ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ -c
      constructor <;> linarith [hc.2]
    | succ j ih =>
      have hsquare : (criticalValue c j)^2 ≤ (-c)^2 :=
        sq_le_sq' (show -(-c) ≤ criticalValue c j by linarith [ih.1]) ih.2
      have hproduct : c*(c+2) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hc.2 (by linarith [hc.1])
      rw [criticalValue_step]
      constructor
      · nlinarith only [sq_nonneg (criticalValue c j)]
      · nlinarith only [hsquare, hproduct]
  have hn := hinterval n
  rw [abs_le]
  constructor <;> linarith [hc.1, hn.1, hn.2]

/-- The complete quadratic coefficient is controlled by the actual
critical orbit through the same horizon. -/
theorem coefficient_bound (c : ℝ) (n : ℕ)
    (hcrit : ∀ j : ℕ, j ≤ n+1 → |criticalValue c j| ≤ 2) :
    |quadraticCoefficient c n| ≤ (4 : ℝ)^n := by
  induction n with
  | zero => norm_num [quadraticCoefficient]
  | succ n ih =>
    have ha := ih (fun j hj => hcrit j (by omega))
    have hd := hcrit (n+1) (by omega)
    calc
      |quadraticCoefficient c (n+1)| =
          (2 * |criticalValue c (n+1)|) * |quadraticCoefficient c n| := by
            norm_num [quadraticCoefficient, abs_mul]
      _ ≤ 4*(4 : ℝ)^n :=
        mul_le_mul (by linarith) ha (abs_nonneg _) (by norm_num)
      _ = (4 : ℝ)^(n+1) := by rw [pow_succ]; ring

theorem quadratic_iterate_ofReal (c t : ℝ) (n : ℕ) :
    ((quadraticMap c)^[n]) (t : ℂ) =
      (((fun x : ℝ => x^2+c)^[n]) t : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply', ih]
    simp only [quadraticMap, Complex.ofReal_add, Complex.ofReal_pow]

theorem critical_complex_orbit_bound (c : ℝ) (hc : c ∈ Icc (-2 : ℝ) 0)
    (n : ℕ) : ‖((quadraticMap c)^[n]) 0‖ ≤ 2 := by
  rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) by simp, quadratic_iterate_ofReal]
  simpa only [criticalValue, Complex.norm_real, Real.norm_eq_abs] using
    critical_orbit_bound c hc n

theorem power_mul_scale (p : ℕ) : (4 : ℝ)^p*scale p = 1 := by
  simp [scale, one_div_pow]

/-- The positive critical return is bounded below on the entire sharp
chart, not only at a selected critical-relation root. -/
theorem chart_return_lower {q : ℕ} (hq : 17 ≤ q) {a b c : ℝ}
    (h : SharpChart q a b) (hc : c ∈ Icc a b) :
    7*scale q ≤ criticalValue c q := by
  have hd := (h.return_range c hc).1
  have hk := (h.coefficient_range hc).1
  have hs := scale_pos q
  have hA := coefficient_bound c (q-1) (by
    intro j hj
    exact SharpChart.critical_orbit_bound hq h hc j (by omega))
  have hA' : -quadraticCoefficient c (q-1) ≤ (4 : ℝ)^(q-1) :=
    (neg_le_abs _).trans hA
  have hmul := mul_le_mul_of_nonneg_right hA' hd.le
  have hmul' := mul_le_mul_of_nonneg_right hmul hs.le
  have hscale : (4 : ℝ)^(q-1)*scale q = 1/4 := by
    have hp := power_mul_scale q
    have hq1 : q = (q-1)+1 := by omega
    rw [hq1, pow_succ] at hp
    have hscale' : scale ((q-1)+1) = scale q := by congr 1; omega
    rw [hscale'] at hp
    linarith
  have hreorder : (4 : ℝ)^(q-1)*criticalValue c q*scale q =
      criticalValue c q/4 := by
    calc
      _ = ((4 : ℝ)^(q-1)*scale q)*criticalValue c q := by ring
      _ = _ := by rw [hscale]; ring
  rw [hreorder] at hmul'
  have hklower := mul_le_mul_of_nonneg_right hk hs.le
  dsimp [kappa] at hklower
  nlinarith only [hmul', hklower, hs]

theorem chart_return_bounds {q : ℕ} (hq : 17 ≤ q) {a b c : ℝ}
    (h : SharpChart q a b) (hc : c ∈ Icc a b) :
    7*scale q ≤ criticalValue c q ∧ criticalValue c q ≤ 12*scale q :=
  ⟨chart_return_lower hq h hc, (h.return_range c hc).2⟩

theorem chart_parameter_band {q : ℕ} (hq : 17 ≤ q) {a b c : ℝ}
    (h : SharpChart q a b) (hc : c ∈ Icc a b) : c ∈ Icc (-2 : ℝ) 0 := by
  have hb := parameter_band hq (h.parameter_range c hc)
  exact ⟨hb.1, by linarith [hb.2]⟩

theorem chart_global_orbit_bound {q : ℕ} (hq : 17 ≤ q) {a b c : ℝ}
    (h : SharpChart q a b) (hc : c ∈ Icc a b) (n : ℕ) :
    |criticalValue c n| ≤ 2 :=
  critical_orbit_bound c (chart_parameter_band hq h hc) n

/-- Every intermediate positive phase of the reference return has a
uniform separation from the critical point. -/
theorem chart_intermediate_lower {q : ℕ} (hq : 17 ≤ q) {a b c : ℝ}
    (h : SharpChart q a b) (hc : c ∈ Icc a b)
    {j : ℕ} (hj : 2 ≤ j) (hjq : j < q) :
    (7/5 : ℝ) ≤ criticalValue c j := by
  have hband := parameter_band hq (h.parameter_range c hc)
  have hd : criticalValue c q ∈ Icc (0 : ℝ) 2 :=
    terminal_band hq ⟨(h.return_range c hc).1.le, (h.return_range c hc).2⟩
  have he := shooting_critical_itinerary hband hd (h.itinerary c hc)
    (j-2) (by omega)
  rw [Nat.sub_add_cancel hj] at he
  rw [he, show (q-2)-(j-2) = (q-j-1)+1 by omega]
  exact NearTwoInverse.back_lower hband hd _

/-- All noncentral phases, including the negative first image, stay a
fixed distance from zero throughout the reference interval. -/
theorem chart_phase_abs {q : ℕ} (hq : 17 ≤ q) {a b c : ℝ}
    (h : SharpChart q a b) (hc : c ∈ Icc a b)
    {j : ℕ} (hj : 1 ≤ j) (hjq : j < q) :
    (7/5 : ℝ) ≤ |criticalValue c j| := by
  by_cases hj1 : j = 1
  · subst j
    have hband := parameter_band hq (h.parameter_range c hc)
    have he : criticalValue c 1 = c := by simp [criticalValue]
    rw [he, abs_of_nonpos (by linarith [hband.2])]
    linarith [hband.2]
  · exact (chart_intermediate_lower hq h hc (by omega) hjq).trans (le_abs_self _)

private theorem chart_signed_relation_error {q : ℕ} (hq : 17 ≤ q) {a b c : ℝ}
    (h : SharpChart q a b) (hc : c ∈ Icc a b) :
    |(((normalizedReturn c q)^[6]) 0).re+
      (((normalizedReturn c q)^[3]) 0).re-relation (kappa q c)| ≤
        94488*scale q := by
  have he := actual_signed_relation_error c q hq
    (fun j _ => chart_global_orbit_bound hq h hc j)
    (h.return_range c hc).1
    (by simpa only [scale, one_div_pow, mul_one_div] using (h.return_range c hc).2)
    (h.coefficient_range hc)
  simpa only [scale, one_div_pow, mul_one_div, kappa] using he

/-- A strict signed margin in original reference coordinates at the
high-coefficient wall. It survives perturbations below the stated scale. -/
theorem chart_left_relation_margin {q : ℕ} (hq : 17 ≤ q) {a b : ℝ}
    (h : SharpChart q a b) :
    scale q/10000 < criticalValue a (6*q)+criticalValue a (3*q) := by
  have ha : a ∈ Icc a b := left_mem_Icc.mpr h.ordered.le
  have he := chart_signed_relation_error hq h ha
  rw [h.left_coefficient] at he
  have hsmall := scale_small hq
  have hs := scale_pos q
  have hnorm : (1/20000 : ℝ) < (((normalizedReturn a q)^[6]) 0).re+
      (((normalizedReturn a q)^[3]) 0).re := by
    have hlo := (abs_le.mp he).1
    linarith [narrow_model_endpoint_margins.2]
  have hd := chart_return_lower hq h ha
  have hprod := mul_lt_mul_of_pos_left hnorm (h.return_range a ha).1
  rw [actual_signed_relation_scale a q (h.return_range a ha).1.ne']
  nlinarith only [hprod, hd, hs]

/-- The opposite wall has the opposite strict margin, in the same
physical reference coordinates. -/
theorem chart_right_relation_margin {q : ℕ} (hq : 17 ≤ q) {a b : ℝ}
    (h : SharpChart q a b) :
    criticalValue b (6*q)+criticalValue b (3*q) < -scale q/10000 := by
  have hb : b ∈ Icc a b := right_mem_Icc.mpr h.ordered.le
  have he := chart_signed_relation_error hq h hb
  rw [h.right_coefficient] at he
  have hsmall := scale_small hq
  have hs := scale_pos q
  have hnorm : (((normalizedReturn b q)^[6]) 0).re+
      (((normalizedReturn b q)^[3]) 0).re < -(1/20000 : ℝ) := by
    have hup := (abs_le.mp he).2
    linarith [narrow_model_endpoint_margins.1]
  have hd := chart_return_lower hq h hb
  have hprod := mul_lt_mul_of_pos_left hnorm (h.return_range b hb).1
  rw [actual_signed_relation_scale b q (h.return_range b hb).1.ne']
  nlinarith only [hprod, hd, hs]

private theorem model_iterate_real (k : ℝ) (n : ℕ) :
    ((complexMap k)^[n]) 0 = (criticalOrbit k n : ℂ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply', ih]
    simp only [criticalOrbit, Q, complexMap]
    push_cast
    rfl

/-- Every parameter in the reference corridor has its entire normalized
third critical return strictly to the left of `-1/10`. -/
theorem chart_normalized_third {q : ℕ} (hq : 17 ≤ q) {a b c : ℝ}
    (h : SharpChart q a b) (hc : c ∈ Icc a b) :
    (((normalizedReturn c q)^[3]) 0).re < -(1/10 : ℝ) := by
  let k := kappa q c
  let ε : ℝ := 24*scale q
  have hk : k ∈ parameterInterval := h.coefficient_range hc
  have hk0 : 0 ≤ k := by dsimp [parameterInterval] at hk; linarith [hk.1]
  have hk2 : k ≤ 2 := by dsimp [parameterInterval] at hk; linarith [hk.2]
  have hε0 : 0 ≤ ε := by
    dsimp [ε]
    exact mul_nonneg (by norm_num) (scale_pos q).le
  have hεmax : ε ≤ 1/100000 := by
    dsimp [ε]
    linarith [scale_small hq]
  have hclose : ∀ z : ℂ, ‖z‖ ≤ 23/20 →
      ‖normalizedReturn c q z-complexMap k z‖ ≤ ε := by
    have hh := normalized_return_error c q (by omega)
      (fun j _ => chart_global_orbit_bound hq h hc j)
      (h.return_range c hc).1
      (by simpa only [scale, one_div_pow, mul_one_div] using (h.return_range c hc).2)
    simpa only [k, ε, kappa, scale, one_div_pow, mul_one_div] using hh
  have hiter := iterate_perturbation_up_to_six (normalizedReturn c q) (complexMap k)
    0 ε hε0 hεmax hclose (quadratic_disk_lipschitz k hk0 hk2)
    (fun n _ => quadratic_critical_orbit_unit k hk0 hk2 n)
  have h3 := (hiter 3 (by omega)).1
  have hr := (Complex.abs_re_le_norm
    (((normalizedReturn c q)^[3]) 0-((complexMap k)^[3]) 0)).trans h3
  rw [model_iterate_real] at hr
  simp only [Complex.sub_re, Complex.ofReal_re] at hr
  rw [show errorCoefficient 3 = 31 by norm_num [errorCoefficient]] at hr
  have hmodel : criticalOrbit k 3 < -(118/1000) := (parameter_orbit_bounds hk).2.1
  have hupper := (abs_le.mp hr).2
  linarith only [hupper, hεmax, hmodel]

end
end TwoLevelReference
