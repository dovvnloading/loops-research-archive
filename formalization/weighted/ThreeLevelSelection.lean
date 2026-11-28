import ThreeLevelReference
import ThreeLevelPerturbation

/-!
# A third critical relation selected in the original quadratic family

The two nested reference charts are transported through the actual
outer return.  The full six-return error is smaller than the endpoint
shooting margins, so the intermediate-value argument selects an actual
quadratic parameter.  The signed critical scales alternate: the
reference terminal scale and its outer-return image are negative,
whereas the terminal scale in the original dynamical plane is positive.
-/

namespace ThreeLevelSelection

open Set Function
open LimitingCrestQuadraticReturn LimitingCrest NearTwoShooting
open TwoLevelOuterChart TwoLevelConjugacy

noncomputable section

def error (p : ℕ) : ℝ := 128*scale p

theorem error_nonneg (p : ℕ) : 0 ≤ error p := by
  unfold error
  exact mul_nonneg (by norm_num) (scale_pos p).le

theorem product_scale_pos (q r : ℕ) : 0 < scale q*scale r :=
  mul_pos (scale_pos q) (scale_pos r)

theorem error_budget {p q r n : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) (hp : 20*(r*q)+100 ≤ p)
    (hn : n ≤ 12*(r*q)) :
    error p*(5 : ℝ)^n ≤ scale q*scale r/1000000000000 := by
  have hpow : (5 : ℝ)^n ≤ (5 : ℝ)^(12*(r*q)) :=
    pow_le_pow_right₀ (by norm_num) hn
  exact (mul_le_mul_of_nonneg_left hpow (error_nonneg p)).trans
    (ThreeLevelPerturbation.separated_three_period_product_error p q r
      (by omega) (by omega) hp)

theorem small_error_budget {p q r n : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) (hp : 20*(r*q)+100 ≤ p)
    (hn : n ≤ 12*(r*q)) : error p*(5 : ℝ)^n ≤ 1/10 := by
  have he := error_budget hr hqr hp hn
  have hq1 : scale q ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hr1 : scale r ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hs : scale q*scale r ≤ 1 := by
    simpa only [one_mul] using mul_le_mul hq1 hr1 (scale_pos r).le (by norm_num)
  linarith only [he, hs]

theorem chart_critical_error {p q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) (hp : 20*(r*q)+100 ≤ p)
    {a b l u L U c : ℝ} (h : SharpChart r a b)
    (g : OuterChart q a b l u) (j : OuterChart p l u L U)
    (hc : c ∈ Icc L U) (n : ℕ) (hn : n ≤ 6*(r*q)) :
    ‖((outerMap c p)^[n]) 0-(criticalValue (monicParameter p c) n : ℂ)‖ ≤
      (5 : ℝ)^n*error p := by
  have hp17 : 17 ≤ p := by omega
  have hq17 : 17 ≤ q := by omega
  apply TwoLevelPerturbation.critical_iterate_stability (outerMap c p)
    (monicParameter p c)
    (ThreeLevelReference.chart_parameter_band hq17 g (j.monic_range hc))
    (6*(r*q)) (error p) (error_nonneg p)
    (small_error_budget hr hqr hp (by omega)) _ n hn
  intro z hz
  exact j.outerMap_error hp17 hc z hz

theorem chart_scale_error {p q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) (hp : 20*(r*q)+100 ≤ p)
    {a b l u L U c : ℝ} (h : SharpChart r a b)
    (g : OuterChart q a b l u) (j : OuterChart p l u L U)
    (hc : c ∈ Icc L U) :
    |secondScale c p (r*q)-criticalValue (monicParameter p c) (r*q)| ≤
      (5 : ℝ)^(r*q)*error p := by
  have hA := coefficient_negative (j.coefficient_lower c hc)
  have he := chart_critical_error hr hqr hp h g j hc (r*q) (by omega)
  rw [outerMap_iterate_zero c p (r*q) hA.ne] at he
  simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, secondScale]
    using he

theorem chart_scale_absolute_error {p q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) (hp : 20*(r*q)+100 ≤ p)
    {a b l u L U c : ℝ} (h : SharpChart r a b)
    (g : OuterChart q a b l u) (j : OuterChart p l u L U)
    (hc : c ∈ Icc L U) :
    |secondScale c p (r*q)-criticalValue (monicParameter p c) (r*q)| ≤
      scale q*scale r/1000000000000 := by
  have he := chart_scale_error hr hqr hp h g j hc
  have hb := error_budget hr hqr hp (show r*q ≤ 12*(r*q) by omega)
  nlinarith only [he, hb]

theorem chart_scale_relative {p q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) (hp : 20*(r*q)+100 ≤ p)
    {a b l u L U c : ℝ} (h : SharpChart r a b)
    (g : OuterChart q a b l u) (j : OuterChart p l u L U)
    (hc : c ∈ Icc L U) :
    |secondScale c p (r*q)-criticalValue (monicParameter p c) (r*q)| ≤
      |criticalValue (monicParameter p c) (r*q)|/100 := by
  have he := chart_scale_absolute_error hr hqr hp h g j hc
  have hd := ThreeLevelReference.terminal_scale_lower hr hqr h g (j.monic_range hc)
  have hs := mul_pos (scale_pos q) (scale_pos r)
  nlinarith only [he, hd, hs]

theorem chart_scale_negative {p q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) (hp : 20*(r*q)+100 ≤ p)
    {a b l u L U c : ℝ} (h : SharpChart r a b)
    (g : OuterChart q a b l u) (j : OuterChart p l u L U)
    (hc : c ∈ Icc L U) : secondScale c p (r*q) < 0 := by
  have hd := ThreeLevelReference.terminal_scale_negative hr hqr h g (j.monic_range hc)
  have he := chart_scale_relative hr hqr hp h g j hc
  have hhalf : |secondScale c p (r*q)-criticalValue (monicParameter p c) (r*q)| ≤
      |criticalValue (monicParameter p c) (r*q)|/2 :=
    he.trans (by linarith [abs_nonneg (criticalValue (monicParameter p c) (r*q))])
  exact (ThreeLevelPerturbation.moving_scale_negative
    (criticalValue (monicParameter p c) (r*q)) (secondScale c p (r*q)) hd hhalf).1

theorem physical_scale_positive {p q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) (hp : 20*(r*q)+100 ≤ p)
    {a b l u L U c : ℝ} (h : SharpChart r a b)
    (g : OuterChart q a b l u) (j : OuterChart p l u L U)
    (hc : c ∈ Icc L U) : 0 < criticalValue c ((r*q)*p) := by
  have hD := chart_scale_negative hr hqr hp h g j hc
  have hA := coefficient_negative (j.coefficient_lower c hc)
  unfold secondScale at hD
  by_contra hn
  have hm := mul_nonneg_of_nonpos_of_nonpos hA.le (le_of_not_gt hn)
  linarith only [hD, hm]

def shootingRelation (p q r : ℕ) (c : ℝ) : ℝ :=
  TwoLevelSelection.shootingRelation p (r*q) c

theorem continuous_shootingRelation (p q r : ℕ) :
    Continuous (shootingRelation p q r) :=
  TwoLevelSelection.continuous_shootingRelation p (r*q)

theorem chart_relation_error {p q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) (hp : 20*(r*q)+100 ≤ p)
    {a b l u L U c : ℝ} (h : SharpChart r a b)
    (g : OuterChart q a b l u) (j : OuterChart p l u L U)
    (hc : c ∈ Icc L U) :
    |shootingRelation p q r c-
      (criticalValue (monicParameter p c) (6*(r*q))+
        criticalValue (monicParameter p c) (3*(r*q)))| ≤
      2*(scale q*scale r)/1000000000000 := by
  have hp17 : 17 ≤ p := by omega
  have hq17 : 17 ≤ q := by omega
  have hA := coefficient_negative (j.coefficient_lower c hc)
  have he := TwoLevelPerturbation.signed_relation_stability
    (outerMap c p) (monicParameter p c)
    (ThreeLevelReference.chart_parameter_band hq17 g (j.monic_range hc))
    (r*q) (error p) (error_nonneg p)
    (small_error_budget hr hqr hp (by omega))
    (fun z hz => j.outerMap_error hp17 hc z hz)
  rw [signed_relation_scale c p (r*q) hA.ne] at he
  change |shootingRelation p q r c-
    (criticalValue (monicParameter p c) (6*(r*q))+
      criticalValue (monicParameter p c) (3*(r*q)))| ≤
        2*error p*(5 : ℝ)^(6*(r*q)) at he
  have hb := error_budget hr hqr hp (show 6*(r*q) ≤ 12*(r*q) by omega)
  nlinarith only [he, hb]

/-- Every product-separated period triple supplies an actual original
quadratic parameter with the complete signed third-return relation and
nonzero positive terminal scale.  Both nested chart witnesses are
retained for the subsequent physical domain construction. -/
theorem exists_three_level_parameter (p q r : ℕ) (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) (hp : 20*(r*q)+100 ≤ p) :
    ∃ a b l u L U c : ℝ,
      SharpChart r a b ∧ OuterChart q a b l u ∧ OuterChart p l u L U ∧
        c ∈ Icc L U ∧
        criticalValue c (6*((r*q)*p))+criticalValue c (3*((r*q)*p)) = 0 ∧
        0 < criticalValue c ((r*q)*p) := by
  have hp17 : 17 ≤ p := by omega
  have hq17 : 17 ≤ q := by omega
  obtain ⟨a,b,h⟩ := exists_sharp_chart r hr
  have ha : a ∈ Icc a b := left_mem_Icc.mpr h.ordered.le
  have hb : b ∈ Icc a b := right_mem_Icc.mpr h.ordered.le
  have haband := NearTwoShooting.parameter_band hr (h.parameter_range a ha)
  have hbband := NearTwoShooting.parameter_band hr (h.parameter_range b hb)
  obtain ⟨l,u,g⟩ := exists_outer_chart q hq17 a b haband.1 h.ordered hbband.2
  have hl : l ∈ Icc l u := left_mem_Icc.mpr g.ordered.le
  have hu : u ∈ Icc l u := right_mem_Icc.mpr g.ordered.le
  have hlband := NearTwoShooting.parameter_band hq17 (g.parameter_range l hl)
  have huband := NearTwoShooting.parameter_band hq17 (g.parameter_range u hu)
  obtain ⟨L,U,j⟩ := exists_outer_chart p hp17 l u hlband.1 g.ordered huband.2
  have hL : L ∈ Icc L U := left_mem_Icc.mpr j.ordered.le
  have hU : U ∈ Icc L U := right_mem_Icc.mpr j.ordered.le
  have heL := chart_relation_error hr hqr hp h g j hL
  have heU := chart_relation_error hr hqr hp h g j hU
  rw [j.left_monicParameter] at heL
  rw [j.right_monicParameter] at heU
  have hleft : shootingRelation p q r L < 0 := by
    have he := (abs_le.mp heL).2
    have hm := ThreeLevelReference.left_relation_margin hr hqr h g
    have hs := mul_pos (scale_pos q) (scale_pos r)
    linarith only [he, hm, hs]
  have hright : 0 < shootingRelation p q r U := by
    have he := (abs_le.mp heU).1
    have hm := ThreeLevelReference.right_relation_margin hr hqr h g
    have hs := mul_pos (scale_pos q) (scale_pos r)
    linarith only [he, hm, hs]
  obtain ⟨c,hc,hzero⟩ := intermediate_value_Icc j.ordered.le
    (continuous_shootingRelation p q r).continuousOn
    (show (0 : ℝ) ∈ Icc (shootingRelation p q r L) (shootingRelation p q r U)
      from ⟨hleft.le,hright.le⟩)
  have hA := coefficient_negative (j.coefficient_lower c hc)
  unfold shootingRelation TwoLevelSelection.shootingRelation at hzero
  have hrel : criticalValue c (6*((r*q)*p))+criticalValue c (3*((r*q)*p)) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hA.ne
  exact ⟨a,b,l,u,L,U,c,h,g,j,hc,hrel,physical_scale_positive hr hqr hp h g j hc⟩

end
end ThreeLevelSelection
