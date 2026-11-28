import TwoLevelConjugacy
import TwoLevelPerturbation
import TwoLevelReference
import TwoLevelCollisions

/-!
# An infinite two-level family selected from literal quadratic parameters

Both return periods vary.  The separation p >= 10*q+30 pays for all
six q-return compositions of the first, nonquadratic return.  Selection
uses the signed relation of the actual original polynomial, not a
relation imposed on an independently chosen quadratic approximation.
-/

namespace TwoLevelSelection

open Set Function
open LimitingCrestQuadraticReturn LimitingCrest NearTwoShooting
open TwoLevelOuterChart TwoLevelConjugacy

noncomputable section

def error (p : ℕ) : ℝ := 128*scale p

theorem error_nonneg (p : ℕ) : 0 ≤ error p := by
  unfold error
  positivity

theorem error_budget {p q n : ℕ} (hpq : 10*q+30 ≤ p) (hn : n ≤ 6*q) :
    error p*(5 : ℝ)^n ≤ scale q/100000000 := by
  have hpow : (5 : ℝ)^n ≤ (5 : ℝ)^(6*q) :=
    pow_le_pow_right₀ (by norm_num) hn
  exact (mul_le_mul_of_nonneg_left hpow (error_nonneg p)).trans
    (TwoLevelPerturbation.separated_period_error p q hpq)

theorem small_error_budget {p q n : ℕ} (hq : 17 ≤ q)
    (hpq : 10*q+30 ≤ p) (hn : n ≤ 6*q) : error p*(5 : ℝ)^n ≤ 1/10 := by
  have he := error_budget hpq hn
  have hs := scale_small hq
  linarith

theorem chart_critical_error {p q : ℕ} (hq : 17 ≤ q)
    (hpq : 10*q+30 ≤ p) {a b l r c : ℝ}
    (h : SharpChart q a b) (g : OuterChart p a b l r) (hc : c ∈ Icc l r)
    (n : ℕ) (hn : n ≤ 6*q) :
    ‖((outerMap c p)^[n]) 0-(criticalValue (monicParameter p c) n : ℂ)‖ ≤
      (5 : ℝ)^n*error p := by
  have hp : 17 ≤ p := by omega
  have hτ := g.monic_range hc
  apply TwoLevelPerturbation.critical_iterate_stability (outerMap c p)
    (monicParameter p c) (TwoLevelReference.chart_parameter_band hq h hτ)
    (6*q) (error p) (error_nonneg p) (small_error_budget hq hpq le_rfl) _ n hn
  intro z hz
  exact g.outerMap_error hp hc z hz

theorem chart_scale_bounds {p q : ℕ} (hq : 17 ≤ q)
    (hpq : 10*q+30 ≤ p) {a b l r c : ℝ}
    (h : SharpChart q a b) (g : OuterChart p a b l r) (hc : c ∈ Icc l r) :
    6*scale q < secondScale c p q ∧ secondScale c p q < (121/10)*scale q := by
  have hA := coefficient_negative (g.coefficient_lower c hc)
  have he := chart_critical_error hq hpq h g hc q (by omega)
  rw [outerMap_iterate_zero c p q hA.ne] at he
  have he' : |secondScale c p q-criticalValue (monicParameter p c) q| ≤
      (5 : ℝ)^q*error p := by
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, secondScale] using he
  have hb := error_budget hpq (show q ≤ 6*q by omega)
  obtain ⟨hdlo, hdhi⟩ := TwoLevelReference.chart_return_bounds hq h (g.monic_range hc)
  have hs := scale_pos q
  have hd := abs_le.mp he'
  constructor <;> nlinarith only [hd.1, hd.2, hb, hdlo, hdhi, hs]

theorem chart_scaled_input {p q : ℕ} (hq : 17 ≤ q)
    (hpq : 10*q+30 ≤ p) {a b l r c : ℝ}
    (h : SharpChart q a b) (g : OuterChart p a b l r) (hc : c ∈ Icc l r)
    {z : ℂ} (hz : ‖z‖ ≤ 23/20) :
    ‖(secondScale c p q : ℂ)*z‖ ≤ 14*scale q := by
  obtain ⟨hlo,hhi⟩ := chart_scale_bounds hq hpq h g hc
  have hD : 0 < secondScale c p q := by linarith [scale_pos q]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD]
  have hm := mul_le_mul_of_nonneg_left hz hD.le
  nlinarith only [hm, hhi, scale_pos q]

theorem chart_phase_disk {p q : ℕ} (hq : 17 ≤ q)
    (hpq : 10*q+30 ≤ p) {a b l r c : ℝ}
    (h : SharpChart q a b) (g : OuterChart p a b l r) (hc : c ∈ Icc l r)
    {z : ℂ} (hz : ‖z‖ ≤ 23/20) (j : ℕ) (hj : j ≤ q) :
    ‖((outerMap c p)^[j]) ((secondScale c p q : ℂ)*z)‖ ≤ 12/5 := by
  have hp : 17 ≤ p := by omega
  have hband := TwoLevelReference.chart_parameter_band hq h (g.monic_range hc)
  exact (TwoLevelPerturbation.iterate_stability (outerMap c p) (monicParameter p c)
    ((secondScale c p q : ℂ)*z) q (error p) (error_nonneg p)
    (small_error_budget hq hpq (by omega))
    (fun w hw => g.outerMap_error hp hc w hw)
    (fun n hn => TwoLevelPerturbation.reference_disk_orbit
      (monicParameter p c) hband q hq (chart_scaled_input hq hpq h g hc hz) n hn)
    j hj).2

theorem chart_collision {p q : ℕ} (hq : 17 ≤ q)
    (hpq : 10*q+30 ≤ p) {a b l r c : ℝ}
    (h : SharpChart q a b) (g : OuterChart p a b l r) (hc : c ∈ Icc l r)
    {z w : ℂ} (hz : ‖z‖ ≤ 23/20) (hw : ‖w‖ ≤ 23/20) :
    normalizedReturn c (q*p) z = normalizedReturn c (q*p) w ↔
      z = w ∨ z = -w := by
  have hp : 17 ≤ p := by omega
  have hA := coefficient_negative (g.coefficient_lower c hc)
  have hD : 0 < secondScale c p q := by
    linarith [(chart_scale_bounds hq hpq h g hc).1, scale_pos q]
  have hDC : (secondScale c p q : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hraw := TwoLevelCollisions.iterate_signed_collision (outerMap c p) hq h
    (g.monic_range hc) (error p) (error_nonneg p)
    (small_error_budget hq hpq (by omega))
    (fun v hv => g.outerMap_error hp hc v hv)
    (fun hu hv => outerMap_collision_iff hp (g.critical_orbit c hc)
      (g.coefficient_lower c hc) hu hv)
    (chart_scaled_input hq hpq h g hc hz) (chart_scaled_input hq hpq h g hc hw)
  rw [← second_normalization_eq c p q hA.ne hD.ne' z,
    ← second_normalization_eq c p q hA.ne hD.ne' w,
    div_left_inj' hDC, hraw]
  constructor
  · rintro (he | he)
    · exact Or.inl (mul_left_cancel₀ hDC he)
    · exact Or.inr (mul_left_cancel₀ hDC (by simpa only [mul_neg] using he))
  · rintro (he | he)
    · exact Or.inl (congrArg (fun v : ℂ => (secondScale c p q : ℂ)*v) he)
    · exact Or.inr (by rw [he, mul_neg])

theorem chart_normalized_error {p q : ℕ} (hq : 17 ≤ q)
    (hpq : 10*q+30 ≤ p) {a b l r c : ℝ}
    (h : SharpChart q a b) (g : OuterChart p a b l r) (hc : c ∈ Icc l r)
    (z : ℂ) (hz : ‖z‖ ≤ 23/20) :
    ‖normalizedReturn c (q*p) z-
      complexMap (kappa q (monicParameter p c)) z‖ ≤ 1/500000 := by
  have hp : 17 ≤ p := by omega
  have hA := coefficient_negative (g.coefficient_lower c hc)
  have hτ := g.monic_range hc
  have hτband := TwoLevelReference.chart_parameter_band hq h hτ
  obtain ⟨hdlo, hdhi⟩ := TwoLevelReference.chart_return_bounds hq h hτ
  have hscale := chart_scale_bounds hq hpq h g hc
  have hDpos : 0 < secondScale c p q := by linarith [scale_pos q]
  have he := chart_critical_error hq hpq h g hc q (by omega)
  rw [outerMap_iterate_zero c p q hA.ne] at he
  have he' : |secondScale c p q-criticalValue (monicParameter p c) q| ≤
      (5 : ℝ)^q*error p := by
    simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, secondScale] using he
  have hbudget : error p*(5 : ℝ)^(2*q) ≤
      criticalValue (monicParameter p c) q/100000000 := by
    have hb := error_budget hpq (show 2*q ≤ 6*q by omega)
    linarith [scale_pos q]
  have hstab := TwoLevelPerturbation.normalized_return_stability
    (outerMap c p) (monicParameter p c) hτband q hq (error p) (error_nonneg p)
    (fun w hw => g.outerMap_error hp hc w hw) hdlo hdhi
    (secondScale c p q) he' hbudget hz
  rw [second_normalization_eq c p q hA.ne hDpos.ne'] at hstab
  have href := normalized_return_error (monicParameter p c) q (by omega)
    (fun j _ => TwoLevelReference.chart_global_orbit_bound hq h hτ j)
    (h.return_range _ hτ).1
    (by simpa only [scale, one_div_pow, mul_one_div] using hdhi) z hz
  change ‖normalizedReturn (monicParameter p c) q z-
    complexMap (kappa q (monicParameter p c)) z‖ ≤ 24/(4 : ℝ)^q at href
  have href' : ‖normalizedReturn (monicParameter p c) q z-
    complexMap (kappa q (monicParameter p c)) z‖ ≤ 24*scale q := by
    simpa only [scale, one_div_pow, mul_one_div] using href
  have ht : ‖normalizedReturn c (q*p) z-complexMap (kappa q (monicParameter p c)) z‖ ≤
      ‖normalizedReturn c (q*p) z-normalizedReturn (monicParameter p c) q z‖+
      ‖normalizedReturn (monicParameter p c) q z-complexMap (kappa q (monicParameter p c)) z‖ := by
    simpa only [dist_eq_norm] using dist_triangle
      (normalizedReturn c (q*p) z) (normalizedReturn (monicParameter p c) q z)
      (complexMap (kappa q (monicParameter p c)) z)
  linarith [scale_small hq]

def shootingRelation (p q : ℕ) (c : ℝ) : ℝ :=
  returnCoefficient p c *
    (criticalValue c (6*(q*p))+criticalValue c (3*(q*p)))

theorem continuous_shootingRelation (p q : ℕ) : Continuous (shootingRelation p q) :=
  (continuous_quadraticCoefficient (p-1)).mul
    ((continuous_criticalValue (6*(q*p))).add (continuous_criticalValue (3*(q*p))))

theorem chart_relation_error {p q : ℕ} (hq : 17 ≤ q)
    (hpq : 10*q+30 ≤ p) {a b l r c : ℝ}
    (h : SharpChart q a b) (g : OuterChart p a b l r) (hc : c ∈ Icc l r) :
    |shootingRelation p q c-
      (criticalValue (monicParameter p c) (6*q)+
        criticalValue (monicParameter p c) (3*q))| ≤ 2*scale q/100000000 := by
  have hA := coefficient_negative (g.coefficient_lower c hc)
  have h6 := (Complex.abs_re_le_norm
    (((outerMap c p)^[6*q]) 0-(criticalValue (monicParameter p c) (6*q) : ℂ))).trans
      (chart_critical_error hq hpq h g hc (6*q) le_rfl)
  have h3 := (Complex.abs_re_le_norm
    (((outerMap c p)^[3*q]) 0-(criticalValue (monicParameter p c) (3*q) : ℂ))).trans
      (chart_critical_error hq hpq h g hc (3*q) (by omega))
  simp only [Complex.sub_re, Complex.ofReal_re] at h6 h3
  have hb6 := error_budget hpq (show 6*q ≤ 6*q from le_rfl)
  have hb3 := error_budget hpq (show 3*q ≤ 6*q by omega)
  have hid : shootingRelation p q c-
      (criticalValue (monicParameter p c) (6*q)+criticalValue (monicParameter p c) (3*q)) =
      ((((outerMap c p)^[6*q]) 0).re-criticalValue (monicParameter p c) (6*q))+
      ((((outerMap c p)^[3*q]) 0).re-criticalValue (monicParameter p c) (3*q)) := by
    unfold shootingRelation
    rw [← signed_relation_scale c p q hA.ne]
    ring
  rw [hid]
  have ht := abs_add_le
    ((((outerMap c p)^[6*q]) 0).re-criticalValue (monicParameter p c) (6*q))
    ((((outerMap c p)^[3*q]) 0).re-criticalValue (monicParameter p c) (3*q))
  nlinarith only [ht, h6, h3, hb6, hb3]

structure Selected (p q : ℕ) (c : ℝ) : Prop where
  parameter_band : c ∈ Icc (-2 : ℝ) (-2+20*scale p)
  first_scale : 0 < criticalValue c p ∧ criticalValue c p ≤ 14*scale p
  first_coefficient : (3/20 : ℝ) < -returnCoefficient p c*scale p
  first_itinerary : shooting (p-2) (criticalValue c p) c = 0
  first_critical_orbit : ∀ j ≤ p, |criticalValue c j| ≤ 2
  second_scale : 6*scale q < secondScale c p q ∧ secondScale c p q < (121/10)*scale q
  physical_scale_negative : criticalValue c (q*p) < 0
  signed_relation : criticalValue c (6*(q*p))+criticalValue c (3*(q*p)) = 0
  inner_coefficient : kappa q (monicParameter p c) ∈
    Icc (17903/10000 : ℝ) (17904/10000)
  complete_disk_error : ∀ z : ℂ, ‖z‖ ≤ 23/20 →
    ‖normalizedReturn c (q*p) z-complexMap (kappa q (monicParameter p c)) z‖ ≤ 1/500000
  complete_collision : ∀ {z w : ℂ}, ‖z‖ ≤ 23/20 → ‖w‖ ≤ 23/20 →
    (normalizedReturn c (q*p) z = normalizedReturn c (q*p) w ↔ z = w ∨ z = -w)
  complete_phase_disk : ∀ {z : ℂ}, ‖z‖ ≤ 23/20 → ∀ j ≤ q,
    ‖((outerMap c p)^[j]) ((secondScale c p q : ℂ)*z)‖ ≤ 12/5

theorem exists_selected (p q : ℕ) (hq : 17 ≤ q) (hpq : 10*q+30 ≤ p) :
    ∃ c : ℝ, Selected p q c := by
  have hp : 17 ≤ p := by omega
  obtain ⟨a,b,h⟩ := exists_sharp_chart q hq
  have ha : a ∈ Icc a b := left_mem_Icc.mpr h.ordered.le
  have hb : b ∈ Icc a b := right_mem_Icc.mpr h.ordered.le
  have haband := NearTwoShooting.parameter_band hq (h.parameter_range a ha)
  have hbband := NearTwoShooting.parameter_band hq (h.parameter_range b hb)
  obtain ⟨l,r,g⟩ := exists_outer_chart p hp a b haband.1 h.ordered hbband.2
  have hl : l ∈ Icc l r := left_mem_Icc.mpr g.ordered.le
  have hr : r ∈ Icc l r := right_mem_Icc.mpr g.ordered.le
  have hel := chart_relation_error hq hpq h g hl
  have her := chart_relation_error hq hpq h g hr
  rw [g.left_monicParameter] at hel
  rw [g.right_monicParameter] at her
  have hleft : 0 < shootingRelation p q l := by
    have hh := (abs_le.mp hel).1
    have hm := TwoLevelReference.chart_left_relation_margin hq h
    linarith [scale_pos q]
  have hright : shootingRelation p q r < 0 := by
    have hh := (abs_le.mp her).2
    have hm := TwoLevelReference.chart_right_relation_margin hq h
    linarith [scale_pos q]
  obtain ⟨c,hc,hzero⟩ := intermediate_value_Icc' g.ordered.le
    (continuous_shootingRelation p q).continuousOn
    (show (0 : ℝ) ∈ Icc (shootingRelation p q r) (shootingRelation p q l)
      from ⟨hright.le,hleft.le⟩)
  have hA := coefficient_negative (g.coefficient_lower c hc)
  have hsc := chart_scale_bounds hq hpq h g hc
  have hDpos : 0 < secondScale c p q := by linarith [scale_pos q]
  have hdneg := (secondScale_positive_iff c p q hA).mp hDpos
  have hrel : criticalValue c (6*(q*p))+criticalValue c (3*(q*p)) = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hA.ne
  exact ⟨c, g.parameter_range c hc, g.return_range c hc, g.coefficient_lower c hc,
    g.itinerary c hc, g.critical_orbit c hc, hsc, hdneg, hrel,
    h.coefficient_range (g.monic_range hc), chart_normalized_error hq hpq h g hc,
    chart_collision hq hpq h g hc, chart_phase_disk hq hpq h g hc⟩

end
end TwoLevelSelection
