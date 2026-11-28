import TwoLevelSelection

/-!
# Complete reference itineraries for a third physical return

The reference is an entire two-level parameter chart.  Its terminal scale
is negative in the original plane.  Every intermediate complex phase is
controlled, including the phases between successive coarse returns.  The
separation estimate applies to pairs of arbitrary points in a whole disk.
-/

namespace ThreeLevelReference

open Set Function
open LimitingCrestQuadraticReturn LimitingCrest NearTwoShooting
open TwoLevelOuterChart TwoLevelConjugacy

noncomputable section

theorem chart_parameter_band {q : ℕ} (hq : 17 ≤ q)
    {a b l u t : ℝ} (g : OuterChart q a b l u) (ht : t ∈ Icc l u) :
    t ∈ Icc (-2 : ℝ) 0 := by
  have hb := NearTwoShooting.parameter_band hq (g.parameter_range t ht)
  exact ⟨hb.1, by linarith [hb.2]⟩

theorem chart_critical_bound {q : ℕ} (hq : 17 ≤ q)
    {a b l u t : ℝ} (g : OuterChart q a b l u) (ht : t ∈ Icc l u)
    (n : ℕ) : |criticalValue t n| ≤ 2 :=
  TwoLevelPerturbation.critical_orbit_bound t (chart_parameter_band hq g ht) n

theorem coefficient_scale_bounds {q : ℕ} (hq : 17 ≤ q)
    {a b l u t : ℝ} (g : OuterChart q a b l u) (ht : t ∈ Icc l u) :
    (3/20 : ℝ) < |returnCoefficient q t| * scale q ∧
      |returnCoefficient q t| * scale q ≤ 1/4 := by
  have hA := coefficient_negative (g.coefficient_lower t ht)
  have hb := TwoLevelPerturbation.coefficient_bound t (q-1)
    (fun j _ => chart_critical_bound hq g ht j)
  have hm := mul_le_mul_of_nonneg_right hb (scale_pos q).le
  have hp : (4 : ℝ)^(q-1)*scale q = 1/4 := by
    have hs := TwoLevelReference.power_mul_scale q
    have he : q = (q-1)+1 := by omega
    rw [he, pow_succ] at hs
    have hscale : scale ((q-1)+1) = scale q := by congr 1; omega
    rw [hscale] at hs
    linarith
  refine ⟨?_, ?_⟩
  · rw [abs_of_neg hA]
    exact g.coefficient_lower t ht
  · change |returnCoefficient q t| * scale q ≤ _ at hm
    linarith only [hm, hp]

theorem terminal_scale_negative {q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) {a b l u t : ℝ}
    (h : SharpChart r a b) (g : OuterChart q a b l u) (ht : t ∈ Icc l u) :
    criticalValue t (r*q) < 0 := by
  have hA := coefficient_negative (g.coefficient_lower t ht)
  have hs := TwoLevelSelection.chart_scale_bounds hr hqr h g ht
  apply (secondScale_positive_iff t q r hA).mp
  linarith [scale_pos r]

theorem terminal_scale_lower {q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) {a b l u t : ℝ}
    (h : SharpChart r a b) (g : OuterChart q a b l u) (ht : t ∈ Icc l u) :
    24*scale q*scale r < |criticalValue t (r*q)| := by
  have hq : 17 ≤ q := by omega
  have hd := terminal_scale_negative hr hqr h g ht
  have hA := coefficient_negative (g.coefficient_lower t ht)
  have hab := (coefficient_scale_bounds hq g ht).2
  have hs := (TwoLevelSelection.chart_scale_bounds hr hqr h g ht).1
  have hid : |returnCoefficient q t| * |criticalValue t (r*q)| =
      secondScale t q r := by
    rw [abs_of_neg hA, abs_of_neg hd]
    unfold secondScale
    ring
  have hlo := mul_lt_mul_of_pos_right hs (scale_pos q)
  have hup := mul_le_mul_of_nonneg_right hab (abs_nonneg (criticalValue t (r*q)))
  rw [← hid] at hlo
  nlinarith only [hlo, hup]

theorem terminal_scale_upper {q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) {a b l u t : ℝ}
    (h : SharpChart r a b) (g : OuterChart q a b l u) (ht : t ∈ Icc l u) :
    |criticalValue t (r*q)| < 81*scale q*scale r := by
  have hq : 17 ≤ q := by omega
  have hd := terminal_scale_negative hr hqr h g ht
  have hA := coefficient_negative (g.coefficient_lower t ht)
  have hab := (coefficient_scale_bounds hq g ht).1
  have hs := (TwoLevelSelection.chart_scale_bounds hr hqr h g ht).2
  have hid : |returnCoefficient q t| * |criticalValue t (r*q)| =
      secondScale t q r := by
    rw [abs_of_neg hA, abs_of_neg hd]
    unfold secondScale
    ring
  have hlo := mul_lt_mul_of_pos_right hab (abs_pos.mpr hd.ne)
  have hup := mul_lt_mul_of_pos_right hs (scale_pos q)
  rw [← hid] at hup
  have hprod := mul_pos (scale_pos q) (scale_pos r)
  nlinarith only [hlo, hup, hprod]

theorem left_relation_margin {q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) {a b l u : ℝ}
    (h : SharpChart r a b) (g : OuterChart q a b l u) :
    criticalValue l (6*(r*q))+criticalValue l (3*(r*q)) <
      -(scale q*scale r/10000) := by
  have hq : 17 ≤ q := by omega
  have hl : l ∈ Icc l u := left_mem_Icc.mpr g.ordered.le
  have he := TwoLevelSelection.chart_relation_error hr hqr h g hl
  rw [g.left_monicParameter] at he
  have href := TwoLevelReference.chart_left_relation_margin hr h
  have hs := scale_pos r
  have hweighted : scale r/20000 < TwoLevelSelection.shootingRelation q r l := by
    linarith [(abs_le.mp he).1]
  have hA := coefficient_negative (g.coefficient_lower l hl)
  let P := criticalValue l (6*(r*q))+criticalValue l (3*(r*q))
  have hP : P < 0 := by
    have hp : 0 < returnCoefficient q l * P := by
      change 0 < TwoLevelSelection.shootingRelation q r l
      linarith
    rcases mul_pos_iff.mp hp with hp | hp
    · linarith [hp.1]
    · exact hp.2
  have hab := (coefficient_scale_bounds hq g hl).2
  rw [abs_of_neg hA] at hab
  have hmul := mul_le_mul_of_nonneg_right hab (neg_nonneg.mpr hP.le)
  have hwall := mul_lt_mul_of_pos_right hweighted (scale_pos q)
  change scale r/20000*scale q < (returnCoefficient q l*P)*scale q at hwall
  change P < -(scale q*scale r/10000)
  have hprod := mul_pos (scale_pos q) (scale_pos r)
  nlinarith only [hmul, hwall, hprod]

theorem right_relation_margin {q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) {a b l u : ℝ}
    (h : SharpChart r a b) (g : OuterChart q a b l u) :
    scale q*scale r/10000 <
      criticalValue u (6*(r*q))+criticalValue u (3*(r*q)) := by
  have hq : 17 ≤ q := by omega
  have hu : u ∈ Icc l u := right_mem_Icc.mpr g.ordered.le
  have he := TwoLevelSelection.chart_relation_error hr hqr h g hu
  rw [g.right_monicParameter] at he
  have href := TwoLevelReference.chart_right_relation_margin hr h
  have hs := scale_pos r
  have hweighted : TwoLevelSelection.shootingRelation q r u < -scale r/20000 := by
    linarith [(abs_le.mp he).2]
  have hA := coefficient_negative (g.coefficient_lower u hu)
  let P := criticalValue u (6*(r*q))+criticalValue u (3*(r*q))
  have hP : 0 < P := by
    have hp : returnCoefficient q u * P < 0 := by
      change TwoLevelSelection.shootingRelation q r u < 0
      linarith
    rcases mul_neg_iff.mp hp with hp | hp
    · exact hp.2
    · linarith [hp.1]
  have hab := (coefficient_scale_bounds hq g hu).2
  rw [abs_of_neg hA] at hab
  have hmul := mul_le_mul_of_nonneg_right hab hP.le
  have hwall := mul_lt_mul_of_pos_right hweighted (scale_pos q)
  change (returnCoefficient q u*P)*scale q < (-scale r/20000)*scale q at hwall
  change scale q*scale r/10000 < P
  have hprod := mul_pos (scale_pos q) (scale_pos r)
  nlinarith only [hmul, hwall, hprod]

theorem phase_identity {q r : ℕ} {a b l u t : ℝ}
    (g : OuterChart q a b l u) (ht : t ∈ Icc l u) (j : ℕ) (z : ℂ) :
    (returnCoefficient q t : ℂ)*
      ((quadraticMap t)^[j*q]) ((criticalValue t (r*q) : ℂ)*z) =
        ((outerMap t q)^[j]) ((secondScale t q r : ℂ)*z) := by
  have hA := (coefficient_negative (g.coefficient_lower t ht)).ne
  have hAC : (returnCoefficient q t : ℂ) ≠ 0 := by exact_mod_cast hA
  have hin : (secondScale t q r : ℂ)*z/(returnCoefficient q t : ℂ) =
      (criticalValue t (r*q) : ℂ)*z := by
    unfold secondScale
    push_cast
    field_simp [hAC]
  rw [outerMap_iterate_scale t q hA, hin]

theorem small_disk_displacement {s : ℕ} (hs : 17 ≤ s) {t : ℝ}
    (ht : t ∈ Icc (-2 : ℝ) 0) {z : ℂ} (hz : ‖z‖ ≤ 15*scale s)
    (n : ℕ) (hn0 : 0 < n) (hn : n ≤ s) :
    ‖((quadraticMap t)^[n]) z-(criticalValue t n : ℂ)‖ ≤ 75*scale s := by
  cases n with
  | zero => omega
  | succ n =>
    have hp : (4 : ℝ)^(n+1) ≤ (4 : ℝ)^s :=
      pow_le_pow_right₀ (by norm_num) hn
    have he : (4 : ℝ)^s*(15*scale s)^2 = 225*scale s := by
      calc
        _ = 225*scale s*(scale s*(4 : ℝ)^s) := by ring
        _ = _ := by rw [TwoLevelPerturbation.scale_mul_power]; ring
    have hm := mul_le_mul_of_nonneg_right hp (sq_nonneg (15*scale s))
    rw [he] at hm
    have hsmall : (4 : ℝ)^(n+1)*(15*scale s)^2 ≤ 1 := by
      linarith [scale_small hs]
    have hd := TwoLevelPerturbation.orbit_displacement t n (15*scale s) z
      (by positivity) (fun j _ => TwoLevelPerturbation.critical_orbit_bound t ht j)
      hsmall hz
    linarith

theorem small_disk_orbit {s : ℕ} (hs : 17 ≤ s) {t : ℝ}
    (ht : t ∈ Icc (-2 : ℝ) 0) {z : ℂ} (hz : ‖z‖ ≤ 15*scale s)
    (n : ℕ) (hn : n ≤ s) :
    ‖((quadraticMap t)^[n]) z‖ ≤ 21/10 := by
  by_cases hn0 : n = 0
  · subst n
    simpa using hz.trans (show 15*scale s ≤ (21/10 : ℝ) by linarith [scale_small hs])
  have hd := small_disk_displacement hs ht hz n (by omega) hn
  have hb : ‖(criticalValue t n : ℂ)‖ ≤ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact TwoLevelPerturbation.critical_orbit_bound t ht n
  have htri := norm_le_norm_sub_add (((quadraticMap t)^[n]) z) (criticalValue t n : ℂ)
  linarith [scale_small hs]

theorem chart_input_bound {q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) {a b l u t : ℝ}
    (h : SharpChart r a b) (g : OuterChart q a b l u) (ht : t ∈ Icc l u)
    {z : ℂ} (hz : ‖z‖ ≤ 6/5) :
    ‖(secondScale t q r : ℂ)*z‖ ≤ 15*scale r := by
  have hb := TwoLevelSelection.chart_scale_bounds hr hqr h g ht
  have hD : 0 < secondScale t q r := by linarith [hb.1, scale_pos r]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD]
  have hm := mul_le_mul_of_nonneg_left hz hD.le
  nlinarith only [hm, hb.2, scale_pos r]

theorem coarse_phase_displacement {q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) {a b l u t : ℝ}
    (h : SharpChart r a b) (g : OuterChart q a b l u) (ht : t ∈ Icc l u)
    {z : ℂ} (hz : ‖z‖ ≤ 6/5) (j : ℕ) (hj : 1 ≤ j) (hjr : j ≤ r) :
    ‖((outerMap t q)^[j]) ((secondScale t q r : ℂ)*z)-
      (criticalValue (monicParameter q t) j : ℂ)‖ ≤ 1/5 := by
  have hq : 17 ≤ q := by omega
  have hband := TwoLevelReference.chart_parameter_band hr h (g.monic_range ht)
  have hz' := chart_input_bound hr hqr h g ht hz
  have hp := (TwoLevelPerturbation.iterate_stability (outerMap t q)
    (monicParameter q t) ((secondScale t q r : ℂ)*z) r
    (TwoLevelSelection.error q) (TwoLevelSelection.error_nonneg q)
    (TwoLevelSelection.small_error_budget hr hqr (by omega))
    (fun w hw => g.outerMap_error hq ht w hw)
    (fun n hn => small_disk_orbit hr hband hz' n hn) j hjr).1
  have hd := small_disk_displacement hr hband hz' j hj hjr
  have he := TwoLevelSelection.error_budget hqr (show j ≤ 6*r by omega)
  have htri := norm_le_norm_sub_add
    (((outerMap t q)^[j]) ((secondScale t q r : ℂ)*z)-
      (criticalValue (monicParameter q t) j : ℂ))
    (((quadraticMap (monicParameter q t))^[j]) ((secondScale t q r : ℂ)*z)-
      (criticalValue (monicParameter q t) j : ℂ))
  simp only [sub_sub_sub_cancel_right] at htri
  nlinarith only [hp, hd, he, htri, scale_small hr]

theorem coarse_phase_disk {q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) {a b l u t : ℝ}
    (h : SharpChart r a b) (g : OuterChart q a b l u) (ht : t ∈ Icc l u)
    {z : ℂ} (hz : ‖z‖ ≤ 6/5) (j : ℕ) (hjr : j ≤ r) :
    ‖((outerMap t q)^[j]) ((secondScale t q r : ℂ)*z)‖ ≤ 201/100 := by
  have hq : 17 ≤ q := by omega
  have hband := TwoLevelReference.chart_parameter_band hr h (g.monic_range ht)
  have hz' := chart_input_bound hr hqr h g ht hz
  by_cases hj0 : j = 0
  · subst j
    simpa using hz'.trans (show 15*scale r ≤ (201/100 : ℝ) by linarith [scale_small hr])
  have hp := (TwoLevelPerturbation.iterate_stability (outerMap t q)
    (monicParameter q t) ((secondScale t q r : ℂ)*z) r
    (TwoLevelSelection.error q) (TwoLevelSelection.error_nonneg q)
    (TwoLevelSelection.small_error_budget hr hqr (by omega))
    (fun w hw => g.outerMap_error hq ht w hw)
    (fun n hn => small_disk_orbit hr hband hz' n hn) j hjr).1
  have hd := small_disk_displacement hr hband hz' j (by omega) hjr
  have he := TwoLevelSelection.error_budget hqr (show j ≤ 6*r by omega)
  have hb : ‖(criticalValue (monicParameter q t) j : ℂ)‖ ≤ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact TwoLevelReference.chart_global_orbit_bound hr h (g.monic_range ht) j
  have ht1 := norm_le_norm_sub_add
    (((outerMap t q)^[j]) ((secondScale t q r : ℂ)*z))
    (((quadraticMap (monicParameter q t))^[j]) ((secondScale t q r : ℂ)*z))
  have ht2 := norm_le_norm_sub_add
    (((quadraticMap (monicParameter q t))^[j]) ((secondScale t q r : ℂ)*z))
    (criticalValue (monicParameter q t) j : ℂ)
  nlinarith only [hp, hd, he, hb, ht1, ht2, scale_small hr]

theorem physical_block_input {q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) {a b l u t : ℝ}
    (h : SharpChart r a b) (g : OuterChart q a b l u) (ht : t ∈ Icc l u)
    {z : ℂ} (hz : ‖z‖ ≤ 6/5) (j : ℕ) (hjr : j ≤ r) :
    ‖((quadraticMap t)^[j*q]) ((criticalValue t (r*q) : ℂ)*z)‖ ≤ 14*scale q := by
  have hq : 17 ≤ q := by omega
  have hb := coarse_phase_disk hr hqr h g ht hz j hjr
  rw [← phase_identity g ht j z, norm_mul, Complex.norm_real, Real.norm_eq_abs] at hb
  have hA := (coefficient_scale_bounds hq g ht).1
  have hmul := mul_le_mul_of_nonneg_right hb (scale_pos q).le
  have hlo := mul_le_mul_of_nonneg_right hA.le
    (norm_nonneg (((quadraticMap t)^[j*q]) ((criticalValue t (r*q) : ℂ)*z)))
  nlinarith only [hmul, hlo, (scale_pos q).le]

theorem physical_block_orbit {q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) {a b l u t : ℝ}
    (h : SharpChart r a b) (g : OuterChart q a b l u) (ht : t ∈ Icc l u)
    {z : ℂ} (hz : ‖z‖ ≤ 6/5) (j i : ℕ) (hjr : j ≤ r) (hiq : i ≤ q) :
    ‖((quadraticMap t)^[i+j*q]) ((criticalValue t (r*q) : ℂ)*z)‖ ≤ 21/10 := by
  rw [iterate_add_apply]
  exact TwoLevelPerturbation.reference_disk_orbit t (chart_parameter_band (by omega) g ht)
    q (by omega) (physical_block_input hr hqr h g ht hz j hjr) i hiq

theorem physical_orbit_disk {q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) {a b l u t : ℝ}
    (h : SharpChart r a b) (g : OuterChart q a b l u) (ht : t ∈ Icc l u)
    {z : ℂ} (hz : ‖z‖ ≤ 6/5) (n : ℕ) (hn : n ≤ r*q) :
    ‖((quadraticMap t)^[n]) ((criticalValue t (r*q) : ℂ)*z)‖ ≤ 21/10 := by
  have hq : 0 < q := by omega
  have he := Nat.mod_add_div n q
  have hi : n%q < q := Nat.mod_lt n hq
  have hj : n/q ≤ r := by
    by_contra! hh
    have hm := Nat.mul_le_mul_right q (show r+1 ≤ n/q by omega)
    nlinarith
  have hnform : n = n%q+(n/q)*q := by nlinarith only [he]
  rw [hnform]
  exact physical_block_orbit hr hqr h g ht hz (n/q) (n%q) hj hi.le

end
end ThreeLevelReference
