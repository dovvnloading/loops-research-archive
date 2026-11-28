import ActualCrestQuartic

/-!
# The size of the actual quartic crest coefficient

The exact coefficient recurrence has a positive contribution from each
quadratic squaring.  The early critical orbit stays close enough to two
to bound the coefficient by the square of its quadratic coefficient.
The last two positive orbit points then give a uniform, two-sided bound
in the actual critical-return scale.
-/

namespace ActualCrestQuarticScale

open Set Function
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn
open ActualCrestRemainderOrder ActualCrestRemainderScale ActualCrestQuartic

noncomputable section

set_option maxHeartbeats 1000000

/- The next two elementary deficit estimates are the supporting proofs
from ActualCrestRemainderOrder, with the earlier cutoff needed here. -/
private theorem scale_power_bound {p n k : ℕ} (h : n+k ≤ p) :
    scale p*(4 : ℝ)^n ≤ (1/4 : ℝ)^k := by
  have hm : scale p ≤ scale (n+k) :=
    pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/4)
      (by norm_num : (1/4 : ℝ) ≤ 1) h
  have hi : scale n*(4 : ℝ)^n = 1 := by
    unfold scale
    rw [one_div_pow]
    exact one_div_mul_cancel (pow_ne_zero n (by norm_num))
  calc
    scale p*(4 : ℝ)^n ≤ scale (n+k)*(4 : ℝ)^n :=
      mul_le_mul_of_nonneg_right hm (by positivity)
    _ = (1/4 : ℝ)^k := by
      rw [show scale (n+k) = scale n*(1/4 : ℝ)^k by
        unfold scale; rw [pow_add]]
      calc
        scale n*(1/4 : ℝ)^k*4^n = (scale n*4^n)*(1/4 : ℝ)^k := by ring
        _ = (1/4 : ℝ)^k := by rw [hi,one_mul]

private theorem critical_deficit (c : ℝ) (hc : -2 ≤ c) (n : ℕ) :
    2-criticalValue c (n+2) ≤ 3*(c+2)*(4 : ℝ)^n := by
  induction n with
  | zero =>
    rw [criticalValue_two]
    norm_num only [pow_zero,mul_one]
    nlinarith only [sq_nonneg (c+2)]
  | succ n ih =>
    rw [show n+1+2 = (n+2)+1 by omega,criticalValue_step,pow_succ (4 : ℝ) n]
    nlinarith only [ih,sq_nonneg (2-criticalValue c (n+2)),hc]

private theorem early_critical_lower {p : ℕ} {c : ℝ}
    (hc : ActualTip p c) {j : ℕ} (hj2 : 2 ≤ j) (hjp : j ≤ p-3) :
    (497/256 : ℝ) ≤ criticalValue c j := by
  have hd := critical_deficit c hc.1.1 (j-2)
  rw [Nat.sub_add_cancel hj2] at hd
  have hpow := scale_power_bound (p := p) (n := j-2) (k := 5) (by omega)
  norm_num only [show (1/4 : ℝ)^5 = 1/1024 by norm_num] at hpow
  have he : c+2 ≤ 20*scale p := by linarith [hc.1.2]
  have hm := mul_le_mul_of_nonneg_right he
    (show 0 ≤ 3*(4 : ℝ)^(j-2) by positivity)
  nlinarith only [hd,hm,hpow]

private theorem quartic_nonneg {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {n : ℕ} (hn : n ≤ p-1) :
    0 ≤ quarticCoefficient c n := by
  have hall : ∀ m : ℕ, m ≤ p-1 → 0 ≤ quarticCoefficient c m := by
    intro m
    induction m with
    | zero => intro hm; simp only [quarticCoefficient,le_refl]
    | succ m ih =>
      intro hm
      cases m with
      | zero => norm_num [quarticCoefficient,quadraticCoefficient]
      | succ m =>
        have hb := ih (by omega)
        have hx := critical_prefix_lower hp hc
          (show 2 ≤ m+1+1 by omega) (show m+1+1 ≤ p-1 by omega)
        rw [quarticCoefficient]
        have hmul : 0 ≤ 2*criticalValue c (m+1+1)*quarticCoefficient c (m+1) :=
          mul_nonneg (by linarith) hb
        exact add_nonneg hmul (sq_nonneg _)
  exact hall n hn

private theorem upper_step {x a b r s : ℝ} (hx : 0 ≤ x)
    (hb : b ≤ r*a^2) (hs : 2*x*r+1 ≤ s*(2*x)^2) :
    2*x*b+a^2 ≤ s*(2*x*a)^2 := by
  have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2*x by positivity)
  have hc := mul_le_mul_of_nonneg_right hs (sq_nonneg a)
  nlinarith only [hm,hc]

private theorem early_quartic_upper {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {n : ℕ} (hn1 : 1 ≤ n) (hnp : n ≤ p-3) :
    quarticCoefficient c n ≤ (9/100 : ℝ)*(quadraticCoefficient c n)^2 := by
  have hall : ∀ m : ℕ, 1 ≤ m → m ≤ p-3 →
      quarticCoefficient c m ≤ (9/100 : ℝ)*(quadraticCoefficient c m)^2 := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      intro hmp
      have hb := parameter_band hp hc.1
      have he : criticalValue c 1 = c := by simp [criticalValue]
      norm_num only [quarticCoefficient,quadraticCoefficient,he,pow_zero,mul_zero,
        add_zero,zero_add,one_pow,mul_one]
      have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 49/25)
        (show (49/25 : ℝ) ≤ -c by linarith [hb.2]) 2
      nlinarith only [hs]
    | succ m hm ih =>
      intro hmp
      have hb := ih (by omega)
      have hx := early_critical_lower hc (show 2 ≤ m+1 by omega) hmp
      rw [quarticCoefficient,quadraticCoefficient]
      apply upper_step (by linarith) hb
      nlinarith only [hx,sq_nonneg (criticalValue c (m+1)-497/256)]
  exact hall n hn1 hnp

private theorem last_critical_bounds {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    criticalValue c (p-1) ∈ Icc (7/5 : ℝ) (10/7) ∧
      criticalValue c (p-2) ∈ Icc (9/5 : ℝ) 2 := by
  have hband := parameter_band hp hc.1
  have hq := scale_small hp
  have hx1 := critical_prefix_lower hp hc (show 2 ≤ p-1 by omega) le_rfl
  have hx2 := critical_prefix_lower hp hc (show 2 ≤ p-2 by omega) (by omega)
  have hstep1 := criticalValue_step c (p-1)
  have hstep2 := criticalValue_step c (p-2)
  rw [show p-1+1 = p by omega] at hstep1
  rw [show p-2+1 = p-1 by omega] at hstep2
  have hl1 : (7/5 : ℝ) ≤ criticalValue c (p-1) := by
    apply (sq_le_sq₀ (by norm_num) (by linarith : 0 ≤ criticalValue c (p-1))).mp
    nlinarith only [hstep1,hc.2.1,hband.2]
  have hu1 : criticalValue c (p-1) ≤ (10/7 : ℝ) := by
    apply (sq_le_sq₀ (by linarith : 0 ≤ criticalValue c (p-1)) (by norm_num)).mp
    nlinarith only [hstep1,hc.2.2.1,hband.1,hq]
  have hl2 : (9/5 : ℝ) ≤ criticalValue c (p-2) := by
    apply (sq_le_sq₀ (by norm_num) (by linarith : 0 ≤ criticalValue c (p-2))).mp
    nlinarith only [hstep2,hl1,hband.2]
  have hu2 : criticalValue c (p-2) ≤ 2 :=
    (abs_le.mp (hc.2.2.2.2.2.2 (p-2) (by omega))).2
  exact ⟨⟨hl1,hu1⟩,⟨hl2,hu2⟩⟩

/-- The exact quartic coefficient is trapped between fixed multiples of
the square of the exact quadratic coefficient. -/
theorem actual_quartic_coefficient_bounds {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    (7/50 : ℝ)*(quadraticCoefficient c (p-1))^2 ≤ quarticCoefficient c (p-1) ∧
      quarticCoefficient c (p-1) ≤ (17/100 : ℝ)*(quadraticCoefficient c (p-1))^2 := by
  obtain ⟨hx1,hx2⟩ := last_critical_bounds hp hc
  have hq1 : quadraticCoefficient c (p-1) =
      2*criticalValue c (p-1)*quadraticCoefficient c (p-2) := by
    conv_lhs => rw [show p-1 = (p-2)+1 by omega,quadraticCoefficient]
    rw [show p-2+1 = p-1 by omega]
  have hq2 : quadraticCoefficient c (p-2) =
      2*criticalValue c (p-2)*quadraticCoefficient c (p-3) := by
    conv_lhs => rw [show p-2 = (p-3)+1 by omega,quadraticCoefficient]
    rw [show p-3+1 = p-2 by omega]
  have hb1 : quarticCoefficient c (p-1) =
      2*criticalValue c (p-1)*quarticCoefficient c (p-2)+
        (quadraticCoefficient c (p-2))^2 := by
    conv_lhs => rw [show p-1 = (p-2)+1 by omega,quarticCoefficient]
    rw [show p-2+1 = p-1 by omega]
  have hb2 : quarticCoefficient c (p-2) =
      2*criticalValue c (p-2)*quarticCoefficient c (p-3)+
        (quadraticCoefficient c (p-3))^2 := by
    conv_lhs => rw [show p-2 = (p-3)+1 by omega,quarticCoefficient]
    rw [show p-3+1 = p-2 by omega]
  have hlowprev : (quadraticCoefficient c (p-2))^2/16 ≤
      quarticCoefficient c (p-2) := by
    have hnonneg := quartic_nonneg hp hc (show p-3 ≤ p-1 by omega)
    have hprod : 0 ≤ 2*criticalValue c (p-2)*quarticCoefficient c (p-3) :=
      mul_nonneg (by linarith [hx2.1]) hnonneg
    have hs := pow_le_pow_left₀ (by linarith [hx2.1] : 0 ≤ criticalValue c (p-2))
      hx2.2 2
    have hm := mul_le_mul_of_nonneg_right hs (sq_nonneg (quadraticCoefficient c (p-3)))
    rw [hq2,hb2]
    nlinarith only [hprod,hm]
  have hlow : (7/50 : ℝ)*(quadraticCoefficient c (p-1))^2 ≤
      quarticCoefficient c (p-1) := by
    have hs := pow_le_pow_left₀ (by linarith [hx1.1] : 0 ≤ criticalValue c (p-1))
      hx1.2 2
    have hcoeff : (7/50 : ℝ)*(2*criticalValue c (p-1))^2 ≤
        2*criticalValue c (p-1)/16+1 := by
      nlinarith only [hs,hx1.1]
    have hm := mul_le_mul_of_nonneg_left hlowprev
      (show 0 ≤ 2*criticalValue c (p-1) by linarith [hx1.1])
    have hn := mul_le_mul_of_nonneg_right hcoeff
      (sq_nonneg (quadraticCoefficient c (p-2)))
    rw [hq1,hb1]
    nlinarith only [hm,hn]
  have hearly := early_quartic_upper hp hc (show 1 ≤ p-3 by omega) le_rfl
  have hprev : quarticCoefficient c (p-2) ≤
      (11/100 : ℝ)*(quadraticCoefficient c (p-2))^2 := by
    rw [hq2,hb2]
    apply upper_step (by linarith [hx2.1]) hearly
    nlinarith only [hx2.1,sq_nonneg (criticalValue c (p-2)-9/5)]
  have hupper : quarticCoefficient c (p-1) ≤
      (17/100 : ℝ)*(quadraticCoefficient c (p-1))^2 := by
    rw [hq1,hb1]
    apply upper_step (by linarith [hx1.1]) hprev
    nlinarith only [hx1.1,sq_nonneg (criticalValue c (p-1)-7/5)]
  exact ⟨hlow,hupper⟩

/-- The quartic term of every actual tip has a nonzero, uniform
coefficient at the first dynamical scale. -/
theorem normalized_quartic_scale_bounds {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    3*scale p < normalizedQuartic c p ∧ normalizedQuartic c p < 7*scale p := by
  obtain ⟨hlo,hhi⟩ := actual_quartic_coefficient_bounds hp hc
  have hd := hc.2.1
  have hq := scale_pos p
  have hklo : (179/100 : ℝ) ≤ kappa p c := by
    have h := hc.2.2.2.1.1
    change (17903/10000 : ℝ) ≤ kappa p c at h
    linarith
  have hkhi : kappa p c ≤ (9/5 : ℝ) := by
    have h := hc.2.2.2.1.2
    change kappa p c ≤ (17904/10000 : ℝ) at h
    linarith
  have hκ0 : 0 ≤ kappa p c := by linarith
  have hident : (quadraticCoefficient c (p-1))^2*(criticalValue c p)^3 =
      (kappa p c)^2*criticalValue c p := by
    unfold kappa
    ring
  have hmullo := mul_le_mul_of_nonneg_right hlo (pow_nonneg hd.le 3)
  have hmulhi := mul_le_mul_of_nonneg_right hhi (pow_nonneg hd.le 3)
  have hlo' : (7/50 : ℝ)*(kappa p c)^2*criticalValue c p ≤ normalizedQuartic c p := by
    calc
      _ = (7/50 : ℝ)*((quadraticCoefficient c (p-1))^2*(criticalValue c p)^3) :=
        by rw [hident]; ring
      _ ≤ normalizedQuartic c p := by simpa only [normalizedQuartic,mul_assoc] using hmullo
  have hhi' : normalizedQuartic c p ≤ (17/100 : ℝ)*(kappa p c)^2*criticalValue c p := by
    calc
      _ ≤ (17/100 : ℝ)*((quadraticCoefficient c (p-1))^2*(criticalValue c p)^3) :=
        by simpa only [normalizedQuartic,mul_assoc] using hmulhi
      _ = _ := by rw [hident]; ring
  have hdlo := actual_return_scale_lower hp hc
  have hsqlo := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 179/100) hklo 2
  have hsqhi := pow_le_pow_left₀ hκ0 hkhi 2
  have hlow1 := mul_le_mul_of_nonneg_right hklo hq.le
  have hdlo' : (179/25 : ℝ)*scale p ≤ criticalValue c p := by linarith
  have hlow2 := mul_le_mul hsqlo hdlo'
    (show 0 ≤ (179/25 : ℝ)*scale p by positivity) (sq_nonneg _)
  have hhi2 := mul_le_mul hsqhi hc.2.2.1 hd.le (by norm_num : (0 : ℝ) ≤ (9/5)^2)
  constructor
  · nlinarith only [hlo',hlow2,hq]
  · nlinarith only [hhi',hhi2,hq]

end
end ActualCrestQuarticScale
