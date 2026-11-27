import NearTwoTip
import QuadraticCrestCrossing
import LimitingCrestCoefficient

/-!
# Quantitative convergence of actual selected crest curves

The parameters are constructed by the real shooting theorem. Their
normalized polynomial returns, angular crossings, and selected circle
points converge to the declared limiting model with explicit bounds.
No extremal-width interpretation is used in these statements.
-/

namespace ActualCrestLimit

open Set Function LimitingCrest NearTwoTip NearTwoShooting
open LimitingCrestQuadraticReturn QuadraticCrestCrossing
open LoopsLimitingCrestParameter
noncomputable section

/-- Uniform approximation to the single constructed limiting quadratic,
rather than to a period-dependent quadratic coefficient. -/
theorem actual_tip_limit_map_error {p : ℕ} (hp : 17 ≤ p) {c k₀ : ℝ}
    (hc : ActualTip p c) (hk₀ : k₀ ∈ parameterInterval) (hroot : relation k₀ = 0)
    {z : ℂ} (hz : ‖z‖ ≤ 23/20) :
    ‖normalizedReturn c p z-complexMap k₀ z‖ ≤ 23646*scale p := by
  have hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p := by
    simpa only [scale,one_div_pow,mul_one_div] using hc.2.2.1
  have hnorm := normalized_return_error c p (by omega) hc.2.2.2.2.2.2 hc.2.1 hsmall z hz
  change ‖normalizedReturn c p z-complexMap (kappa p c) z‖ ≤ _ at hnorm
  have hnorm' : ‖normalizedReturn c p z-complexMap (kappa p c) z‖ ≤ 24*scale p := by
    simpa only [scale,one_div_pow,mul_one_div] using hnorm
  have hk := actual_tip_coefficient_error hp hc hk₀ hroot
  have hscale := scale_pos p
  have hz2 : ‖z‖^2 ≤ (3/2 : ℝ) := by
    have hs := pow_le_pow_left₀ (norm_nonneg z) hz 2
    nlinarith only [hs]
  have hid : complexMap (kappa p c) z-complexMap k₀ z =
      ((k₀-kappa p c : ℝ) : ℂ)*z^2 := by
    unfold complexMap
    push_cast
    ring
  have hmodel : ‖complexMap (kappa p c) z-complexMap k₀ z‖ ≤ 23622*scale p := by
    rw [hid,norm_mul,Complex.norm_real,Real.norm_eq_abs,norm_pow,abs_sub_comm]
    have hm := mul_le_mul hk hz2 (sq_nonneg ‖z‖) (by positivity : 0 ≤ 15748*scale p)
    nlinarith only [hm]
  have htri : ‖normalizedReturn c p z-complexMap k₀ z‖ ≤
      ‖normalizedReturn c p z-complexMap (kappa p c) z‖+
        ‖complexMap (kappa p c) z-complexMap k₀ z‖ := by
    simpa only [dist_eq_norm] using dist_triangle
      (normalizedReturn c p z) (complexMap (kappa p c) z) (complexMap k₀ z)
  linarith only [htri,hnorm',hmodel]

/-- Every selected actual angular crossing has an exponentially small
error from the same limiting angular formula, uniformly in radius. -/
theorem actual_tip_angle_error {p : ℕ} (hp : 17 ≤ p) {c k₀ s u : ℝ}
    (hc : ActualTip p c) (hk₀ : k₀ ∈ parameterInterval) (hroot : relation k₀ = 0)
    (hs : s ∈ Icc (63/1000 : ℝ) (33/500))
    (hu : u ∈ Icc (-1/100 : ℝ) (1/100))
    (hzero : (normalizedReturn c p (circlePoint s u)).re = 0) :
    |u-crossingCos k₀ s| ≤ 236460*scale p := by
  have hmap := actual_tip_limit_map_error hp hc hk₀ hroot (circlePoint_disk hs hu)
  have hreal := (Complex.abs_re_le_norm
    (normalizedReturn c p (circlePoint s u)-complexMap k₀ (circlePoint s u))).trans hmap
  have hu1 : u ∈ Icc (-1 : ℝ) 1 := by constructor <;> linarith [hu.1,hu.2]
  have hq : (complexMap k₀ (circlePoint s u)).re = crossing k₀ s u := by
    rw [circle_image k₀ s hu1]
    simp
  simp only [Complex.sub_re,hzero,hq,zero_sub,abs_neg] at hreal
  have hspec := crossingCos_spec hk₀ hs
  have hv : crossingCos k₀ s ∈ Icc (-1/100 : ℝ) (1/100) :=
    ⟨hspec.1.1.le,hspec.1.2.le⟩
  rcases le_total u (crossingCos k₀ s) with hle | hle
  · have hg := crossing_growth hk₀ hs hu hv hle
    rw [hspec.2] at hg
    rw [abs_of_nonpos (sub_nonpos.mpr hle)]
    linarith only [hg,(abs_le.mp hreal).1]
  · have hg := crossing_growth hk₀ hs hv hu hle
    rw [hspec.2] at hg
    rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    linarith only [hg,(abs_le.mp hreal).2]

/-- The normalized selected circle points themselves converge uniformly,
with a constant independent of the period and the selected radius. -/
theorem actual_tip_point_error {p : ℕ} (hp : 17 ≤ p) {c k₀ s u : ℝ}
    (hc : ActualTip p c) (hk₀ : k₀ ∈ parameterInterval) (hroot : relation k₀ = 0)
    (hs : s ∈ Icc (63/1000 : ℝ) (33/500))
    (hu : u ∈ Icc (-1/100 : ℝ) (1/100))
    (hzero : (normalizedReturn c p (circlePoint s u)).re = 0) :
    ‖circlePoint s u-circlePoint s (crossingCos k₀ s)‖ ≤ 32000*scale p := by
  have hspec := (crossingCos_spec hk₀ hs).1
  have hv : crossingCos k₀ s ∈ Icc (-1/100 : ℝ) (1/100) := ⟨hspec.1.le,hspec.2.le⟩
  have hang := actual_tip_angle_error hp hc hk₀ hroot hs hu hzero
  have hcircle := circlePoint_angle_bound s hu hv
  rw [abs_of_pos (by linarith [hs.1] : 0 < s)] at hcircle
  have hm := mul_le_mul (show 2*s ≤ (33/250 : ℝ) by linarith [hs.2]) hang
    (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 33/250)
  have hq := scale_pos p
  nlinarith only [hcircle,hm,hq]

/-- One model root and an actual Lipschitz angular family for every period
at least seventeen, with uniform coefficient, angle, and curve-point errors. -/
theorem exists_actual_crest_families_converging :
    ∃ k₀ : ℝ, k₀ ∈ parameterInterval ∧ relation k₀ = 0 ∧
      ∀ p : ℕ, 17 ≤ p → ∃ c : ℝ, ActualTip p c ∧
        |kappa p c-k₀| ≤ 15748*scale p ∧
        ∃ a : CrestRadius → ℝ, LipschitzWith 100 a ∧
          ∀ s : CrestRadius,
            a s ∈ Ioo (-1/100 : ℝ) (1/100) ∧
            (normalizedReturn c p (circlePoint s (a s))).re = 0 ∧
            |a s-crossingCos k₀ s| ≤ 236460*scale p ∧
            ‖circlePoint s (a s)-circlePoint s (crossingCos k₀ s)‖ ≤ 32000*scale p := by
  obtain ⟨k₀,hk₀,hroot,hfamily⟩ := exists_actual_tips_with_coefficient_limit
  refine ⟨k₀,hk₀,hroot,?_⟩
  intro p hp
  obtain ⟨c,hc,hkerr⟩ := hfamily p hp
  have hband := parameter_band hp hc.1
  have hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p := by
    simpa only [scale,one_div_pow,mul_one_div] using hc.2.2.1
  obtain ⟨a,hLip,ha⟩ := exists_lipschitz_actual_angle c p (by omega)
    ⟨hband.1,by linarith [hband.2]⟩ hc.2.1 hsmall hc.2.2.2.1
  refine ⟨c,hc,hkerr,a,hLip,?_⟩
  intro s
  have hu : a s ∈ Icc (-1/100 : ℝ) (1/100) :=
    ⟨(ha s).1.1.le,(ha s).1.2.le⟩
  exact ⟨(ha s).1,(ha s).2,
    actual_tip_angle_error hp hc hk₀ hroot s.property hu (ha s).2,
    actual_tip_point_error hp hc hk₀ hroot s.property hu (ha s).2⟩


open Filter
open scoped Topology

private theorem scaled_error_tendsto_zero (C : ℝ) :
    Tendsto (fun n : ℕ => C*scale (n+17)) atTop (𝓝 0) := by
  have hbase : Tendsto (fun n : ℕ => (1/4 : ℝ)^n) atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa only [scale,pow_add,mul_zero,zero_mul] using
    (hbase.mul_const ((1/4 : ℝ)^17)).const_mul C

/-- Actual quadratic parameters and crest selections can be chosen as
sequences. Their parameters tend to minus two, their normalized returns
converge uniformly on the certified disk, and both the angular and curve
point selections converge uniformly over the entire radius interval. -/
theorem exists_uniformly_converging_actual_crests :
    ∃ k₀ : ℝ, k₀ ∈ parameterInterval ∧ relation k₀ = 0 ∧
      ∃ c : ℕ → ℝ, ∃ a : ℕ → CrestRadius → ℝ,
        (∀ n, ActualTip (n+17) (c n)) ∧
        (∀ n, LipschitzWith 100 (a n)) ∧
        (∀ n s, a n s ∈ Ioo (-1/100 : ℝ) (1/100) ∧
          (normalizedReturn (c n) (n+17) (circlePoint s (a n s))).re = 0) ∧
        Tendsto c atTop (𝓝 (-2)) ∧
        Tendsto (fun n => kappa (n+17) (c n)) atTop (𝓝 k₀) ∧
        TendstoUniformlyOn (fun n z => normalizedReturn (c n) (n+17) z)
          (complexMap k₀) atTop {z : ℂ | ‖z‖ ≤ 23/20} ∧
        TendstoUniformly a (fun s : CrestRadius => crossingCos k₀ s) atTop ∧
        TendstoUniformly (fun (n : ℕ) (s : CrestRadius) => circlePoint s (a n s))
          (fun s : CrestRadius => circlePoint s (crossingCos k₀ s)) atTop := by
  classical
  obtain ⟨k₀,hk₀,hroot,hfamily⟩ := exists_actual_crest_families_converging
  have hex (n : ℕ) := hfamily (n+17) (by omega)
  choose c hc hkerr a hLip ha using hex
  have hevent (C ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ n : ℕ in atTop, C*scale (n+17) < ε :=
    (tendsto_order.mp (scaled_error_tendsto_zero C)).2 ε hε
  refine ⟨k₀,hk₀,hroot,c,a,hc,hLip,?_,?_,?_,?_,?_,?_⟩
  · intro n s
    exact ⟨(ha n s).1,(ha n s).2.1⟩
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hevent 20 ε hε] with n hn
    have hpar := (hc n).1
    rw [Real.dist_eq,sub_neg_eq_add,abs_of_nonneg (by linarith [hpar.1])]
    linarith [hpar.2]
  · apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hevent 15748 ε hε] with n hn
    rw [Real.dist_eq]
    exact (hkerr n).trans_lt hn
  · apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [hevent 23646 ε hε] with n hn
    intro z hz
    rw [dist_comm,dist_eq_norm]
    exact (actual_tip_limit_map_error (by omega) (hc n) hk₀ hroot hz).trans_lt hn
  · apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [hevent 236460 ε hε] with n hn
    intro s
    rw [Real.dist_eq,abs_sub_comm]
    exact (ha n s).2.2.1.trans_lt hn
  · apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [hevent 32000 ε hε] with n hn
    intro s
    rw [dist_comm,dist_eq_norm]
    exact (ha n s).2.2.2.trans_lt hn


end
end ActualCrestLimit
