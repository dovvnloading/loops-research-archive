import SlitFourPointMetric
import SlitCubicOptimality
import SlitWaveScaling

/-!
# Continuity and scale invariance of the exact four-electrode value

The complete cubic optimum identifies the period ratio with an actual
geometric modulus.  Its proved mark transport and exact dilation laws
then give continuity and scale invariance for all ordered electrodes.
-/

namespace SlitFourPointLimit

open Set Filter Function MarkedSlitTransport SlitWaveLimit SlitWaveScaling
open SlitFourPointChart SlitFourPointMetric
open scoped Topology ENNReal NNReal

noncomputable section

def ratio (u v w t : ℝ) : ℝ :=
  SlitFourPointChart.height u v w t / (2*SlitFourPointChart.width u v w t)

theorem ratio_pos {u v w t : ℝ} (huv : u < v) (hvw : v < w) (hwt : w < t) :
    0 < ratio u v w t :=
  div_pos (SlitFourPointChart.height_pos huv hvw hwt)
    (mul_pos (by norm_num) (SlitFourPointChart.width_pos huv hvw hwt))

theorem ratio_eq_width {u v w t : ℝ} (huv : u < v) (hvw : v < w) (hwt : w < t) :
    ENNReal.ofReal (ratio u v w t) =
      SlitWaveLimit.width (cubicMarking huv hvw hwt) univ :=
  (SlitCubicOptimality.width_eq_period_ratio (cubicMarking huv hvw hwt)).symm

private theorem marking_separation (M : Marking) :
    ∃ r : ℝ, 0 < r ∧ ∀ i j : Fin 4, i ≠ j →
      r ≤ |markCoords M i-markCoords M j| := by
  let r := min (M.first-M.left) (min (M.second-M.first) (M.right-M.second))
  have hr : 0 < r := lt_min (sub_pos.mpr M.left_lt_first)
    (lt_min (sub_pos.mpr M.first_lt_second) (sub_pos.mpr M.second_lt_right))
  have h0 : r ≤ M.first-M.left := min_le_left _ _
  have h1 : r ≤ M.second-M.first := (min_le_right _ _).trans (min_le_left _ _)
  have h2 : r ≤ M.right-M.second := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨r,hr,?_⟩
  intro i j hij
  have ha := le_abs_self (markCoords M i-markCoords M j)
  have hb := neg_le_abs (markCoords M i-markCoords M j)
  have ho0 := M.left_lt_first
  have ho1 := M.first_lt_second
  have ho2 := M.second_lt_right
  fin_cases i <;> fin_cases j
  all_goals norm_num at hij
  all_goals norm_num [markCoords] at ha hb ⊢
  all_goals linarith

/-- The full-plane complete optimum is continuous under all four mark
motions; neither an outer cutoff nor an optimizer is an extra premise. -/
theorem plane_width_tendsto (M : Marking) (A : ℕ → Marking)
    (hmarks : ∀ i, Tendsto (fun n => markCoords (A n) i) atTop (𝓝 (markCoords M i))) :
    Tendsto (fun n => SlitWaveLimit.width (A n) univ) atTop
      (𝓝 (SlitWaveLimit.width M univ)) := by
  obtain ⟨r,hr,hsep⟩ := marking_separation M
  let E : ℕ → ℝ := fun n => cutError (markCoords M) (markCoords (A n))
  have hE : Tendsto E atTop (𝓝 0) := by
    have hi (i : Fin 4) :
        Tendsto (fun n => |markCoords (A n) i-markCoords M i|) atTop (𝓝 0) := by
      simpa using ((hmarks i).sub_const (markCoords M i)).abs
    simpa [E,cutError] using tendsto_finsetSum Finset.univ (fun i _ => hi i)
  have hs : ∀ᶠ n in atTop, E n < r := (tendsto_order.mp hE).2 r hr
  have hC : Tendsto (fun n => distortion (E n) r) atTop (𝓝 1) := by
    have hf : Tendsto (fun n => E n/r) atTop (𝓝 0) := by simpa using hE.div_const r
    have hi : Tendsto (fun n => (1-E n/r)⁻¹) atTop (𝓝 (1 : ℝ)) := by
      simpa using (tendsto_const_nhds.sub hf).inv₀ (by norm_num : (1 : ℝ)-0 ≠ 0)
    have hp : Tendsto (fun n => 1+E n/r) atTop (𝓝 (1 : ℝ)) := by
      simpa using tendsto_const_nhds.add hf
    simpa [distortion,Function.comp_def] using
      ENNReal.continuous_ofReal.tendsto (1 : ℝ) |>.comp
        (by simpa using (hi.pow 2).mul (hp.pow 2))
  have hlower := width_tendsto_of_mark_convergence M A (fun n => (n : ℝ)) hr hsep hmarks
    tendsto_natCast_atTop_atTop
  have hupper : Tendsto (fun n => distortion (E n) r*SlitWaveLimit.width M univ) atTop
      (𝓝 (SlitWaveLimit.width M univ)) := by
    simpa using ENNReal.Tendsto.mul_const hC (Or.inl one_ne_zero)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper
  · exact Filter.Eventually.of_forall (fun n => width_mono (A n) (subset_univ _))
  · filter_upwards [hs] with n hn
    exact width_small_marks_upper M (A n) hr hsep hn univ

theorem realMap_tendsto {u v : ℝ} (huv : u < v) {U V : ℕ → ℝ}
    (hU : Tendsto U atTop (𝓝 u)) (hV : Tendsto V atTop (𝓝 v)) :
    Tendsto (fun n => realMap (U n) (V n)) atTop (𝓝 (realMap u v)) :=
  ((hV.sub hU).inv₀ (sub_ne_zero.mpr huv.ne')).neg

/-- Continuity of the exact value for four independently moving ordered
real electrodes. -/
theorem ofReal_ratio_tendsto {u v w t : ℝ}
    (huv : u < v) (hvw : v < w) (hwt : w < t) (U V W T : ℕ → ℝ)
    (hUV : ∀ n, U n < V n) (hVW : ∀ n, V n < W n) (hWT : ∀ n, W n < T n)
    (hU : Tendsto U atTop (𝓝 u)) (hV : Tendsto V atTop (𝓝 v))
    (hW : Tendsto W atTop (𝓝 w)) (hT : Tendsto T atTop (𝓝 t)) :
    Tendsto (fun n => ENNReal.ofReal (ratio (U n) (V n) (W n) (T n))) atTop
      (𝓝 (ENNReal.ofReal (ratio u v w t))) := by
  let M := cubicMarking huv hvw hwt
  let A : ℕ → Marking := fun n => cubicMarking (hUV n) (hVW n) (hWT n)
  have h0 := realMap_tendsto huv hU hV
  have h1 := realMap_tendsto (huv.trans hvw) hU hW
  have h2 := realMap_tendsto (huv.trans (hvw.trans hwt)) hU hT
  have hcoords : ∀ i, Tendsto (fun n => markCoords (A n) i) atTop (𝓝 (markCoords M i)) := by
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h2.add_const 1
  simpa only [A,M,← ratio_eq_width] using plane_width_tendsto M A hcoords

theorem ratio_tendsto {u v w t : ℝ}
    (huv : u < v) (hvw : v < w) (hwt : w < t) (U V W T : ℕ → ℝ)
    (hUV : ∀ n, U n < V n) (hVW : ∀ n, V n < W n) (hWT : ∀ n, W n < T n)
    (hU : Tendsto U atTop (𝓝 u)) (hV : Tendsto V atTop (𝓝 v))
    (hW : Tendsto W atTop (𝓝 w)) (hT : Tendsto T atTop (𝓝 t)) :
    Tendsto (fun n => ratio (U n) (V n) (W n) (T n)) atTop (𝓝 (ratio u v w t)) := by
  have he := ofReal_ratio_tendsto huv hvw hwt U V W T hUV hVW hWT hU hV hW hT
  have hr := (ENNReal.tendsto_toReal ENNReal.ofReal_ne_top).comp he
  rw [ENNReal.toReal_ofReal (ratio_pos huv hvw hwt).le] at hr
  apply hr.congr'
  filter_upwards [] with n
  exact ENNReal.toReal_ofReal (ratio_pos (hUV n) (hVW n) (hWT n)).le

theorem realMap_scale (s u v : ℝ) : realMap (s*u) (s*v) = s⁻¹*realMap u v := by
  unfold realMap
  rw [← mul_sub,mul_inv_rev]
  ring

/-- A common positive change of electrode scale leaves the exact value
unchanged. -/
theorem ratio_scale {s u v w t : ℝ} (hs : 0 < s)
    (huv : u < v) (hvw : v < w) (hwt : w < t) :
    ratio (s*u) (s*v) (s*w) (s*t) = ratio u v w t := by
  let M := cubicMarking huv hvw hwt
  have hd := width_dilation M univ s⁻¹ (inv_pos.mpr hs)
  rw [image_univ,(dilation s⁻¹ (inv_pos.mpr hs)).surjective.range_eq] at hd
  rw [SlitCubicOptimality.width_eq_period_ratio,SlitCubicOptimality.width_eq_period_ratio] at hd
  have he : ENNReal.ofReal (ratio (s*u) (s*v) (s*w) (s*t)) = ENNReal.ofReal (ratio u v w t) := by
    simpa only [ratio,SlitFourPointChart.width,SlitFourPointChart.height,realMap_scale,
      SlitCubicBoundaryRange.height,SlitCubicBoundary.period,
      M,cubicMarking,Marking.map,OrderIso.mulLeft₀_apply] using hd
  have hr := congrArg ENNReal.toReal he
  rw [ENNReal.toReal_ofReal (ratio_pos (mul_lt_mul_of_pos_left huv hs)
    (mul_lt_mul_of_pos_left hvw hs) (mul_lt_mul_of_pos_left hwt hs)).le,
      ENNReal.toReal_ofReal (ratio_pos huv hvw hwt).le] at hr
  exact hr

end
end SlitFourPointLimit
