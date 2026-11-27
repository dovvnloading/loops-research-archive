import LimitingCrestSharpCoefficient
import Mathlib

/-!
# Moving-endpoint limits for selected radial crest integrals

The angular inputs below are functions on a fixed compact radial interval.
The endpoint may move and need not approach monotonically. These are radial
integrals; identifying them with marked conformal widths is a separate task.
-/

namespace CrestIntegralLimit

open Set Filter MeasureTheory
open scoped Topology
noncomputable section

/-- The fixed window includes the parent inner circle and the terminal exit. -/
def radiusInterval : Set ℝ := Icc (1/16 : ℝ) (133/2000)

/-- The angular variable is the cosine of the selected upper-circle angle. -/
def radialIntegrand (angle : ℝ → ℝ) (s : ℝ) : ℝ :=
  1 / (s * Real.arccos (angle s))

/-- The parent normalization is the full chosen parent, not the retained collar. -/
def radialCoefficient (p : ℕ) (angle : ℝ → ℝ) (r : ℝ) : ℝ :=
  (2 * Real.pi / Real.log (2 - 2 / (p : ℝ))) *
    ∫ s in (1/16 : ℝ)..r, radialIntegrand angle s

/-- Uniform convergence on one fixed interval gives uniform convergence of
all primitives with the same lower endpoint, including the interval boundary. -/
theorem primitives_tendstoUniformlyOn {a b : ℝ} (hab : a ≤ b)
    {F : ℕ → ℝ → ℝ} {g : ℝ → ℝ}
    (hF : ∀ n, ContinuousOn (F n) (Icc a b))
    (hg : ContinuousOn g (Icc a b))
    (hconv : TendstoUniformlyOn F g atTop (Icc a b)) :
    TendstoUniformlyOn (fun n r => ∫ s in a..r, F n s)
      (fun r => ∫ s in a..r, g s) atTop (Icc a b) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hden : 0 < b-a+1 := by linarith
  have hδ : 0 < ε/(b-a+1) := div_pos hε hden
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv (ε/(b-a+1)) hδ] with n hn
  intro r hr
  have hsub : Icc a r ⊆ Icc a b := fun s hs => ⟨hs.1, hs.2.trans hr.2⟩
  have hFi : IntervalIntegrable (F n) volume a r :=
    (hF n |>.mono hsub).intervalIntegrable_of_Icc hr.1
  have hgi : IntervalIntegrable g volume a r :=
    (hg.mono hsub).intervalIntegrable_of_Icc hr.1
  have hb : ‖∫ s in a..r, g s-F n s‖ ≤ (ε/(b-a+1))*|r-a| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun s hs => by
      have hs' : s ∈ Icc a b := by
        rw [uIoc_of_le hr.1] at hs
        exact ⟨hs.1.le, hs.2.trans hr.2⟩
      simpa only [Real.norm_eq_abs, Real.dist_eq] using (hn s hs').le)
  rw [intervalIntegral.integral_sub hgi hFi] at hb
  have hlen : |r-a| ≤ b-a := by
    rw [abs_of_nonneg (sub_nonneg.mpr hr.1)]
    linarith [hr.2]
  have hbound := hb.trans (mul_le_mul_of_nonneg_left hlen hδ.le)
  have hprod : (ε/(b-a+1))*(b-a+1) = ε := div_mul_cancel₀ ε hden.ne'
  rw [Real.dist_eq]
  rw [Real.norm_eq_abs] at hbound
  nlinarith only [hbound, hprod, hδ]

/-- The moving endpoints can oscillate; convergence within the fixed
interval and uniform convergence of the integrands are sufficient. -/
theorem integral_tendsto_of_moving_endpoint {a b r₀ : ℝ} (hab : a ≤ b)
    {F : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {r : ℕ → ℝ}
    (hF : ∀ n, ContinuousOn (F n) (Icc a b))
    (hg : ContinuousOn g (Icc a b))
    (hconv : TendstoUniformlyOn F g atTop (Icc a b))
    (hr : ∀ n, r n ∈ Icc a b) (hr₀ : r₀ ∈ Icc a b)
    (hrconv : Tendsto r atTop (𝓝 r₀)) :
    Tendsto (fun n => ∫ s in a..r n, F n s) atTop
      (𝓝 (∫ s in a..r₀, g s)) := by
  have hgi : IntervalIntegrable g volume a b := hg.intervalIntegrable_of_Icc hab
  have hc : ContinuousOn (fun x => ∫ s in a..x, g s) (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      intervalIntegral.continuousOn_primitive_interval' hgi
        (show a ∈ uIcc a b from left_mem_uIcc)
  apply (primitives_tendstoUniformlyOn hab hF hg hconv).tendsto_comp (hc r₀ hr₀)
  exact tendsto_nhdsWithin_iff.mpr ⟨hrconv, Eventually.of_forall hr⟩

/-- Every selected cosine in this compact band has a continuous,
nondegenerate radial integrand on the complete endpoint window. -/
theorem radialIntegrand_continuousOn {angle : ℝ → ℝ}
    (hc : ContinuousOn angle radiusInterval)
    (hb : ∀ s ∈ radiusInterval, angle s ∈ Icc (-1/100 : ℝ) (1/100)) :
    ContinuousOn (radialIntegrand angle) radiusInterval := by
  apply continuousOn_const.div (continuousOn_id.mul hc.arccos)
  intro s hs
  have hs0 : 0 < s := by have := hs.1; norm_num at this ⊢; linarith
  have ha : 0 < Real.arccos (angle s) :=
    Real.arccos_pos.mpr (by linarith [(hb s hs).2])
  exact (mul_pos hs0 ha).ne'

/-- Uniform angular convergence passes through the reciprocal-angle
integrand on the compact rectangle; no differentiation or quadrature is used. -/
theorem radialIntegrand_tendstoUniformlyOn {angle : ℕ → ℝ → ℝ} {u : ℝ → ℝ}
    (hb : ∀ n s, s ∈ radiusInterval → angle n s ∈ Icc (-1/100 : ℝ) (1/100))
    (hconv : TendstoUniformlyOn angle u atTop radiusInterval) :
    TendstoUniformlyOn (fun n => radialIntegrand (angle n))
      (radialIntegrand u) atTop radiusInterval := by
  have hu : ∀ s ∈ radiusInterval, u s ∈ Icc (-1/100 : ℝ) (1/100) := by
    intro s hs
    exact isClosed_Icc.mem_of_tendsto (hconv.tendsto_at hs)
      (Eventually.of_forall (fun n => hb n s hs))
  let kernel : ℝ × ℝ → ℝ := fun t => 1/(t.1*Real.arccos t.2)
  have hc : ContinuousOn kernel (radiusInterval ×ˢ Icc (-1/100 : ℝ) (1/100)) := by
    apply continuousOn_const.div (continuousOn_fst.mul continuousOn_snd.arccos)
    intro t ht
    have ht0 : 0 < t.1 := by have := ht.1.1; norm_num at this ⊢; linarith
    have ha : 0 < Real.arccos t.2 :=
      Real.arccos_pos.mpr (by linarith [ht.2.2])
    exact (mul_pos ht0 ha).ne'
  have huc := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous hc
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨δ,hδ,hδprop⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hconv δ hδ] with n hn
  intro s hs
  exact hδprop (s,u s) ⟨hs,hu s hs⟩ (s,angle n s) ⟨hs,hb n s hs⟩
    (by simpa only [Prod.dist_eq, dist_self, max_eq_right dist_nonneg] using hn s hs)

/-- The original chosen-parent normalization tends to the model's log-two
normalization. The period offset only selects the certified parameter range. -/
theorem parent_normalization_tendsto :
    Tendsto (fun n : ℕ => 2*Real.pi/Real.log (2-2/((n+17 : ℕ) : ℝ)))
      atTop (𝓝 (2*Real.pi/Real.log 2)) := by
  have hzero : Tendsto (fun n : ℕ => (2 : ℝ)/((n+17 : ℕ) : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).comp (tendsto_add_atTop_nat 17)
  have hbase : Tendsto (fun n : ℕ => (2 : ℝ)-2/((n+17 : ℕ) : ℝ)) atTop (𝓝 2) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hzero
  have hlog := (Real.continuousAt_log (by norm_num : (2 : ℝ) ≠ 0)).tendsto.comp hbase
  exact tendsto_const_nhds.div hlog (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'

/-- The whole moving radial integral converges to the full model coefficient,
using the source's original period-dependent parent normalization. The inputs
include endpoint convergence; no radial monotonicity or optimizer is assumed. -/
theorem radialCoefficient_tendsto_fullModel {κ r₀ : ℝ}
    (hk : κ ∈ Icc (17903/10000 : ℝ) (17904/10000))
    {angle : ℕ → ℝ → ℝ} {r : ℕ → ℝ}
    (hc : ∀ n, ContinuousOn (angle n) radiusInterval)
    (hb : ∀ n s, s ∈ radiusInterval → angle n s ∈ Icc (-1/100 : ℝ) (1/100))
    (hconv : TendstoUniformlyOn angle (LimitingCrest.crossingCos κ) atTop radiusInterval)
    (hr : ∀ n, r n ∈ radiusInterval) (hr₀ : r₀ ∈ radiusInterval)
    (hrconv : Tendsto r atTop (𝓝 r₀)) :
    Tendsto (fun n => radialCoefficient (n+17) (angle n) (r n)) atTop
      (𝓝 (LimitingCrest.fullModelCoefficient κ r₀)) := by
  have hmodel : ContinuousOn (radialIntegrand (LimitingCrest.crossingCos κ))
      radiusInterval :=
    (LimitingCrest.full_integrand_continuousOn hk).mono
      (fun _ hs => ⟨hs.1, by linarith [hs.2]⟩)
  have hint := integral_tendsto_of_moving_endpoint
    (a := (1/16 : ℝ)) (b := (133/2000 : ℝ)) (by norm_num)
    (fun n => radialIntegrand_continuousOn (hc n) (hb n)) hmodel
    (radialIntegrand_tendstoUniformlyOn hb hconv) hr hr₀ hrconv
  simpa only [radialCoefficient, LimitingCrest.fullModelCoefficient, radialIntegrand] using
    parent_normalization_tendsto.mul hint

/-- Once the moving endpoint converges to the certified model endpoint,
the actual selected radial coefficients eventually exceed one third. -/
theorem radialCoefficient_eventually_gt_third {κ r₀ : ℝ}
    (hk : κ ∈ Icc (17903/10000 : ℝ) (17904/10000))
    {angle : ℕ → ℝ → ℝ} {r : ℕ → ℝ}
    (hc : ∀ n, ContinuousOn (angle n) radiusInterval)
    (hb : ∀ n s, s ∈ radiusInterval → angle n s ∈ Icc (-1/100 : ℝ) (1/100))
    (hconv : TendstoUniformlyOn angle (LimitingCrest.crossingCos κ) atTop radiusInterval)
    (hr : ∀ n, r n ∈ radiusInterval) (hr₀ : r₀ ∈ radiusInterval)
    (hrlower : (663/10000 : ℝ) ≤ r₀)
    (hrconv : Tendsto r atTop (𝓝 r₀)) :
    ∀ᶠ n : ℕ in atTop, (1/3 : ℝ) < radialCoefficient (n+17) (angle n) (r n) := by
  have hpos := LimitingCrest.fullModelCoefficient_gt_third hk
    (show r₀ ∈ Icc (663/10000 : ℝ) (1/8) from
      ⟨hrlower, by linarith [hr₀.2]⟩)
  exact (radialCoefficient_tendsto_fullModel hk hc hb hconv hr hr₀ hrconv).eventually
    (lt_mem_nhds hpos)

end
end CrestIntegralLimit
