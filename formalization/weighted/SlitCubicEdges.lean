import SlitCubicImaginaryBoundary
import Mathlib.Topology.Order.IntermediateValue

/-!
# The two vertical sides of the actual cubic rectangle

The real left ray and marked gap map bijectively to the open vertical
sides of the period rectangle. Strictness follows from positivity of the
explicit cubic density on every intervening interval.
-/

namespace SlitCubicEdges

open Set Filter MeasureTheory SlitCubicCalibration SlitCubicBoundary
open SlitCubicBoundaryRange SlitCubicImaginaryBoundary
open scoped Topology
noncomputable section

theorem tail_im_real_continuous {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    Continuous (fun x : ℝ => (tail a b c (x:ℂ)).im) := by
  exact Complex.continuous_im.comp
    ((tail_continuousOn_closedUpper (realDensity_integrable hab hbc)).comp_continuous
      Complex.continuous_ofReal (fun x => by simp [closedUpper]))

private theorem interval_density_pos {a b c x y : ℝ} (hab : a < b) (hbc : b < c)
    (hxy : x < y) (havoid : ∀ t ∈ Ioo x y, t ≠ a ∧ t ≠ b ∧ t ≠ c) :
    0 < ∫ t in x..y, realDensity a b c t := by
  rw [intervalIntegral.integral_of_le hxy.le, integral_Ioc_eq_integral_Ioo]
  have hs : Ioo x y ⊆ Function.support (realDensity a b c) := by
    intro t ht
    obtain ⟨ha,hb,hc⟩ := havoid t ht
    exact (SlitCubicIntegrability.kernel_pos ha hb hc).ne'
  have hn (t : ℝ) : 0 ≤ realDensity a b c t := SlitCubicIntegrability.kernel_nonneg a b c t
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall hn)
    (realDensity_integrable hab hbc).integrableOn,
    inter_eq_self_of_subset_right hs, Real.volume_Ioo]
  exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hxy)

/-- The left real ray runs strictly down the left vertical side. -/
theorem tail_im_strictAntiOn_left {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    StrictAntiOn (fun x : ℝ => (tail a b c (x:ℂ)).im) (Iio a) := by
  intro x hx y hy hxy
  dsimp only
  rw [tail_im_left hab hbc hx.le, tail_im_left hab hbc hy.le]
  have hi := realDensity_integrable hab hbc
  have hd := intervalIntegral.integral_Iic_sub_Iic
    (hi.integrableOn (s := Iic x)) (hi.integrableOn (s := Iic y))
  have hp := interval_density_pos hab hbc hxy (fun t ht =>
    ⟨(ht.2.trans hy).ne, ((ht.2.trans hy).trans hab).ne,
      (((ht.2.trans hy).trans hab).trans hbc).ne⟩)
  linarith

/-- The gap runs strictly up the right vertical side. -/
theorem tail_im_strictMonoOn_gap {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    StrictMonoOn (fun x : ℝ => (tail a b c (x:ℂ)).im) (Ioo b c) := by
  intro x hx y hy hxy
  dsimp only
  rw [tail_im_gap hab hbc hx.1.le hx.2.le, tail_im_gap hab hbc hy.1.le hy.2.le]
  have hi := realDensity_integrable hab hbc
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hi.intervalIntegrable (a := x) (b := y)) (hi.intervalIntegrable (a := y) (b := c))
  rw [intervalIntegral.integral_of_le hx.2.le, intervalIntegral.integral_of_le hy.2.le] at hadd
  have hp := interval_density_pos hab hbc hxy (fun t ht =>
    ⟨((hab.trans hx.1).trans ht.1).ne', (hx.1.trans ht.1).ne', (ht.2.trans hy.2).ne⟩)
  linarith

private theorem tail_im_atBot {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    Tendsto (fun x : ℝ => (tail a b c (x:ℂ)).im) atBot (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => -(∫ t in Iic x, realDensity a b c t)) atBot (𝓝 0) := by
    simpa only [neg_zero, id_eq] using
      (tendsto_integral_Iic_zero (f := realDensity a b c) (μ := volume) tendsto_id).neg
  apply h.congr'
  filter_upwards [eventually_le_atBot a] with x hx
  exact (tail_im_left hab hbc hx).symm

/-- Every interior point of the left rectangle side has an actual real
preimage strictly to the left of the first branch point. -/
theorem exists_left_edge_preimage {a b c y : ℝ} (hab : a < b) (hbc : b < c)
    (hy : y ∈ Ioo (-height a b c) 0) :
    ∃ x ∈ Iio a, tail a b c (x:ℂ) = (y:ℂ)*Complex.I := by
  have hc := tail_im_real_continuous hab hbc
  have ha : Tendsto (fun x : ℝ => (tail a b c (x:ℂ)).im)
      (𝓝[<] a) (𝓝 (-height a b c)) := by
    have h := (hc.tendsto a).mono_left (nhdsWithin_le_nhds (s := Iio a))
    rwa [tail_im_first hab hbc le_rfl hab.le] at h
  have hbot : (atBot : Filter ℝ) ≤ 𝓟 (Iio a) :=
    tendsto_principal.mpr (eventually_lt_atBot a)
  have hsurj := isPreconnected_Iio.intermediate_value_Ioo
    (s := Iio a) (l₁ := 𝓝[<] a) (l₂ := atBot) inf_le_right hbot hc.continuousOn
    ha (tail_im_atBot hab hbc)
  obtain ⟨x,hx,hxy⟩ := hsurj hy
  refine ⟨x,hx,?_⟩
  apply Complex.ext
  · simpa using tail_re_left hab hbc hx.le
  · simpa using hxy

/-- Every interior point of the right rectangle side has an actual real
preimage strictly inside the marked gap. -/
theorem exists_gap_edge_preimage {a b c y : ℝ} (hab : a < b) (hbc : b < c)
    (hy : y ∈ Ioo (-height a b c) 0) :
    ∃ x ∈ Ioo b c, tail a b c (x:ℂ) = (period a b c:ℂ)+(y:ℂ)*Complex.I := by
  have hsurj := intermediate_value_Ioo hbc.le (tail_im_real_continuous hab hbc).continuousOn
  have hb : (tail a b c (b:ℂ)).im = -height a b c := tail_im_first hab hbc hab.le le_rfl
  have hc : (tail a b c (c:ℂ)).im = 0 := tail_im_right hab hbc le_rfl
  rw [hb,hc] at hsurj
  obtain ⟨x,hx,hxy⟩ := hsurj hy
  refine ⟨x,hx,?_⟩
  apply Complex.ext
  · simpa using tail_re_gap hab hbc hx.1.le hx.2.le
  · simpa using hxy


/-- Finite left-ray points land strictly between the rectangle corners. -/
theorem tail_im_mem_Ioo_left {a b c x : ℝ} (hab : a < b) (hbc : b < c) (hx : x < a) :
    (tail a b c (x:ℂ)).im ∈ Ioo (-height a b c) 0 := by
  have hlow := (tail_im_mem_Icc hab hbc ((x+a)/2)).1
  have hhigh := (tail_im_mem_Icc hab hbc (x-1)).2
  have hdown := tail_im_strictAntiOn_left hab hbc
    (show x ∈ Iio a from hx) (show (x+a)/2 ∈ Iio a by change (x+a)/2 < a; linarith)
    (show x < (x+a)/2 by linarith)
  have hup := tail_im_strictAntiOn_left hab hbc
    (show x-1 ∈ Iio a by change x-1 < a; linarith) (show x ∈ Iio a from hx)
    (show x-1 < x by linarith)
  exact ⟨hlow.trans_lt hdown,hup.trans_le hhigh⟩

/-- Every gap-interior point avoids both rectangle corners. -/
theorem tail_im_mem_Ioo_gap {a b c x : ℝ} (hab : a < b) (hbc : b < c)
    (hx : x ∈ Ioo b c) :
    (tail a b c (x:ℂ)).im ∈ Ioo (-height a b c) 0 := by
  have hlow := (tail_im_mem_Icc hab hbc ((b+x)/2)).1
  have hhigh := (tail_im_mem_Icc hab hbc ((x+c)/2)).2
  have hdown := tail_im_strictMonoOn_gap hab hbc
    (show (b+x)/2 ∈ Ioo b c by constructor <;> linarith [hx.1,hx.2]) hx
    (show (b+x)/2 < x by linarith [hx.1])
  have hup := tail_im_strictMonoOn_gap hab hbc hx
    (show (x+c)/2 ∈ Ioo b c by constructor <;> linarith [hx.1,hx.2])
    (show x < (x+c)/2 by linarith [hx.2])
  exact ⟨hlow.trans_lt hdown,hup.trans_le hhigh⟩

end
end SlitCubicEdges
