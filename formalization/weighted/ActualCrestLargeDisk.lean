import NearTwoTip

/-!
# Actual return control on a disk containing the full-parent crossing orbit

The original crest estimates control a smaller disk. Excluding a second
terminal gate on the full parent needs an estimate at the larger second
image. This auxiliary bound comes from the complete polynomial remainder;
no actual intermediate-domain containment is assumed.
-/

namespace ActualCrestLargeDisk

open Set Function Filter
open scoped Topology
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn LimitingCrest
open LoopsLimitingCrestParameter

noncomputable section

/-- The full actual return is controlled on the disk of radius two. -/
theorem normalized_return_error_two (c : ℝ) (p : ℕ) (hp : 17 ≤ p)
    (hcrit : ∀ j : ℕ, j ≤ p → |criticalValue c j| ≤ 2)
    (hd : 0 < criticalValue c p)
    (hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p) :
    ∀ z : ℂ, ‖z‖ ≤ 2 →
      ‖normalizedReturn c p z -
        complexMap (-quadraticCoefficient c (p-1)*criticalValue c p) z‖ ≤
          216/(4 : ℝ)^p := by
  cases p with
  | zero => omega
  | succ n =>
    intro z hz
    let d := criticalValue c (n+1)
    let S : ℝ := (4 : ℝ)^(n+1)
    let R : ℝ := 2
    have hd0 : 0 < d := hd
    have hS0 : 0 < S := by dsimp [S]; positivity
    have hS : (67108864 : ℝ) ≤ (4 : ℝ)^(n+1) := by
      have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4)
        (show 13 ≤ n+1 by omega)
      norm_num at h
      exact h
    change 67108864 ≤ S at hS
    have hSd : S*d ≤ 12 := by
      have h := (le_div_iff₀ hS0).mp hsmall
      nlinarith only [h]
    have hSd0 : 0 ≤ S*d := mul_nonneg hS0.le hd0.le
    have hr : 0 ≤ d*R := by dsimp [R]; positivity
    have hdR : S*(d*R)^2 ≤ 1 := by
      have hsquare := pow_le_pow_left₀ hSd0 hSd 2
      have hnorm : S*(S*(d*R)^2) = (S*d)^2*R^2 := by ring
      have hm := mul_le_mul_of_nonneg_right hsquare (sq_nonneg R)
      have hprod := mul_le_mul_of_nonneg_right hS
        (show 0 ≤ S*(d*R)^2 by positivity)
      dsimp [R] at hm hnorm ⊢
      dsimp [R] at hprod
      nlinarith only [hm, hnorm, hprod]
    have hdz : ‖(d : ℂ)*z‖ ≤ d*R := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd0]
      exact mul_le_mul_of_nonneg_left hz hd0.le
    have herr := complete_remainder_bound c n (d*R) ((d : ℂ)*z) hr hcrit hdR hdz
    change ‖quadraticRemainder c n ((d : ℂ)*z)‖ ≤ (S*(d*R)^2)^2/128 at herr
    have hdne : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
    have hid : normalizedReturn c (n+1) z -
        complexMap (-quadraticCoefficient c n*d) z =
          quadraticRemainder c n ((d : ℂ)*z)/(d : ℂ) := by
      dsimp [normalizedReturn, complexMap, quadraticRemainder]
      change ((quadraticMap c)^[n+1]) ((d : ℂ)*z)/(d : ℂ) -
        (1-((-quadraticCoefficient c n*d : ℝ) : ℂ)*z^2) =
          (((quadraticMap c)^[n+1]) ((d : ℂ)*z) - (d : ℂ) -
            (quadraticCoefficient c n : ℂ)*((d : ℂ)*z)^2)/(d : ℂ)
      push_cast
      field_simp [hdne]
      ring
    have hcubed := pow_le_pow_left₀ hSd0 hSd 3
    have hbound : (S*(d*R)^2)^2/128/d ≤ 216/S := by
      apply (div_le_div_iff₀ hd0 hS0).mpr
      have hm := mul_le_mul_of_nonneg_right hcubed (hd0.le)
      have hr4 : R^4 ≤ (16 : ℝ) := by norm_num [R]
      have hform : ((S*(d*R)^2)^2/128)*S =
          (S*d)^3*d*R^4/128 := by ring
      rw [hform]
      have h1 := mul_le_mul_of_nonneg_right hm
        (pow_nonneg (by norm_num [R] : (0 : ℝ) ≤ R) 4)
      have h2 := mul_le_mul_of_nonneg_left hr4 (show 0 ≤ (1728 : ℝ)*d by positivity)
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 128)).mpr
      calc
        (S*d)^3*d*R^4 ≤ 12^3*d*R^4 := h1
        _ = 1728*d*R^4 := by norm_num
        _ ≤ 1728*d*16 := h2
        _ = (216*d)*128 := by ring
    change ‖normalizedReturn c (n+1) z -
      complexMap (-quadraticCoefficient c n*d) z‖ ≤ 216/S
    rw [hid, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd0]
    exact (div_le_div_of_nonneg_right herr hd0.le).trans hbound

/-- Uniform error against the single constructed limiting polynomial on
the larger disk needed for the full-parent exclusion. -/
theorem actual_tip_limit_map_error {p : ℕ} (hp : 17 ≤ p) {c k₀ : ℝ}
    (hc : ActualTip p c) (hk₀ : k₀ ∈ parameterInterval) (hroot : relation k₀ = 0)
    {z : ℂ} (hz : ‖z‖ ≤ 2) :
    ‖normalizedReturn c p z-complexMap k₀ z‖ ≤ 63208*scale p := by
  have hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p := by
    simpa only [scale,one_div_pow,mul_one_div] using hc.2.2.1
  have hnorm := normalized_return_error_two c p hp hc.2.2.2.2.2.2 hc.2.1 hsmall z hz
  change ‖normalizedReturn c p z-complexMap (kappa p c) z‖ ≤ _ at hnorm
  have hnorm' : ‖normalizedReturn c p z-complexMap (kappa p c) z‖ ≤ 216*scale p := by
    simpa only [scale,one_div_pow,mul_one_div] using hnorm
  have hk := actual_tip_coefficient_error hp hc hk₀ hroot
  have hz2 : ‖z‖^2 ≤ (4 : ℝ) := by
    nlinarith [pow_le_pow_left₀ (norm_nonneg z) hz 2]
  have hid : complexMap (kappa p c) z-complexMap k₀ z =
      ((k₀-kappa p c : ℝ) : ℂ)*z^2 := by
    unfold complexMap
    push_cast
    ring
  have hmodel : ‖complexMap (kappa p c) z-complexMap k₀ z‖ ≤ 62992*scale p := by
    rw [hid,norm_mul,Complex.norm_real,Real.norm_eq_abs,norm_pow,abs_sub_comm]
    have hm := mul_le_mul hk hz2 (sq_nonneg ‖z‖) (by positivity : 0 ≤ 15748*scale p)
    nlinarith only [hm]
  have htri : ‖normalizedReturn c p z-complexMap k₀ z‖ ≤
      ‖normalizedReturn c p z-complexMap (kappa p c) z‖+
        ‖complexMap (kappa p c) z-complexMap k₀ z‖ := by
    simpa only [dist_eq_norm] using dist_triangle
      (normalizedReturn c p z) (complexMap (kappa p c) z) (complexMap k₀ z)
  linarith only [htri,hnorm',hmodel]

/-- The enlarged approximation is uniform for every selection of the
actual signed-tip parameters. -/
theorem map_convergence {k₀ : ℝ} (hk₀ : k₀ ∈ parameterInterval)
    (hroot : relation k₀ = 0) (c : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n)) :
    TendstoUniformlyOn (fun n => normalizedReturn (c n) (n+17))
      (complexMap k₀) atTop {z : ℂ | ‖z‖ ≤ 2} := by
  have hbase : Tendsto (fun n : ℕ => (1/4 : ℝ)^n) atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hzero : Tendsto (fun n : ℕ => 63208*scale (n+17)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [scale,pow_add,mul_zero,zero_mul] using
      (hbase.mul_const ((1/4 : ℝ)^17)).const_mul (63208 : ℝ)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [(tendsto_order.mp hzero).2 ε hε] with n hn
  intro z hz
  rw [dist_comm,dist_eq_norm]
  exact (actual_tip_limit_map_error (by omega) (hc n) hk₀ hroot hz).trans_lt hn

end
end ActualCrestLargeDisk

