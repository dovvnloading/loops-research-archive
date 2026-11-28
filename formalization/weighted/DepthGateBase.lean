import DepthGateChart
import ThreeLevelReference

/-!
# An unconditional initial chart for the depth induction

A sharp one-period parameter corridor initializes every numerical field.
No physical tower or domain hypothesis is assumed at the base.
-/

namespace DepthGate

open Set Function Metric
open LimitingCrestQuadraticReturn LimitingCrest NearTwoShooting
open TwoLevelOuterChart TwoLevelConjugacy

noncomputable section

private theorem sharp_input_bound {r : ℕ} {a b t : ℝ}
    (h : SharpChart r a b) (ht : t ∈ Icc a b)
    {z : ℂ} (hz : ‖z‖ ≤ 6/5) :
    ‖(criticalValue t r : ℂ)*z‖ ≤ 15*scale r := by
  have hd := h.return_range t ht
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd.1]
  have hm := mul_le_mul_of_nonneg_left hz hd.1.le
  nlinarith only [hm, hd.2, (scale_pos r).le]

private theorem sharp_displacement {r : ℕ} (hr : 17 ≤ r) {a b t : ℝ}
    (h : SharpChart r a b) (ht : t ∈ Icc a b)
    {z : ℂ} (hz : ‖z‖ ≤ 6/5) (n : ℕ) (hn : 1 ≤ n) (hnr : n ≤ r) :
    ‖((quadraticMap t)^[n]) ((criticalValue t r : ℂ)*z)-
      (criticalValue t n : ℂ)‖ ≤ 75*scale r :=
  ThreeLevelReference.small_disk_displacement hr
    (TwoLevelReference.chart_parameter_band hr h ht) (sharp_input_bound h ht hz)
    n (by omega) hnr

private theorem sharp_pair {r : ℕ} (hr : 17 ≤ r) {a b t : ℝ}
    (h : SharpChart r a b) (ht : t ∈ Icc a b)
    {z w : ℂ} (hz : ‖z‖ ≤ 6/5) (hw : ‖w‖ ≤ 6/5)
    (n : ℕ) (hn : 1 ≤ n) (hnr : n < r) :
    scale r/10000 ≤
      ‖((quadraticMap t)^[n]) ((criticalValue t r : ℂ)*z)+
        ((quadraticMap t)^[n]) ((criticalValue t r : ℂ)*w)‖ := by
  let v := ((quadraticMap t)^[n]) ((criticalValue t r : ℂ)*z)
  let u := ((quadraticMap t)^[n]) ((criticalValue t r : ℂ)*w)
  let x := criticalValue t n
  have hv : ‖v-(x : ℂ)‖ ≤ 75*scale r := sharp_displacement hr h ht hz n hn hnr.le
  have hu : ‖u-(x : ℂ)‖ ≤ 75*scale r := sharp_displacement hr h ht hw n hn hnr.le
  have hx : (7/5 : ℝ) ≤ |x| := TwoLevelReference.chart_phase_abs hr h ht hn hnr
  have htri := norm_le_norm_sub_add ((x : ℂ)+(x : ℂ)) (v+u)
  have hid : (x : ℂ)+(x : ℂ)-(v+u) = ((x : ℂ)-v)+((x : ℂ)-u) := by ring
  rw [hid] at htri
  have hsub := norm_add_le ((x : ℂ)-v) ((x : ℂ)-u)
  rw [norm_sub_rev (x : ℂ) v, norm_sub_rev (x : ℂ) u] at hsub
  have hnorm : ‖(x : ℂ)+(x : ℂ)‖ = 2*|x| := by
    rw [← two_mul, norm_mul]
    norm_num [Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm] at htri
  change scale r/10000 ≤ ‖v+u‖
  linarith [scale_small hr]

private theorem sharp_first {r : ℕ} (hr : 17 ≤ r) {a b t : ℝ}
    (h : SharpChart r a b) (ht : t ∈ Icc a b)
    {z : ℂ} (hz : ‖z‖ ≤ 6/5) (n : ℕ) (hn : 1 ≤ n) (hnr : n < r) :
    |criticalValue t r| *(23/20)+scale r/10000 ≤
      ‖((quadraticMap t)^[n]) ((criticalValue t r : ℂ)*z)‖ := by
  have he := sharp_displacement hr h ht hz n hn hnr.le
  have hx := TwoLevelReference.chart_phase_abs hr h ht hn hnr
  have ht1 := norm_le_norm_sub_add (criticalValue t n : ℂ)
    (((quadraticMap t)^[n]) ((criticalValue t r : ℂ)*z))
  rw [norm_sub_rev, Complex.norm_real, Real.norm_eq_abs] at ht1
  have hd := h.return_range t ht
  rw [abs_of_pos hd.1]
  linarith [scale_small hr]

/-- The initialized family has an enlarged control disk of radius 6/5,
while half of the allowed normalized error remains reserved. -/
noncomputable def TerminalChart.ofSharp {r : ℕ} (hr : 17 ≤ r) {a b : ℝ}
    (h : SharpChart r a b) : TerminalChart := by
  refine {
    period := r
    left := a
    right := b
    margin := scale r/10000
    buffer := 1/20
    slack := 1/1000000
    orientation := -1
    coefficient := kappa r
    period_ge := hr
    ordered := h.ordered
    parameter_band := ?_
    margin_pos := div_pos (scale_pos r) (by norm_num)
    margin_le := by linarith [scale_small hr]
    buffer_pos := by norm_num
    buffer_le := le_rfl
    slack_pos := by norm_num
    slack_le := le_rfl
    orientation_unit := Or.inr rfl
    coefficient_band := ?_
    scale_bounds := ?_
    orbit_bound := ?_
    pair_bound := ?_
    first_bound := ?_
    normalized_error := ?_
    relation_left := ?_
    relation_right := ?_ }
  · intro t ht
    exact NearTwoShooting.parameter_band hr (h.parameter_range t ht)
  · intro t ht
    exact h.coefficient_range ht
  · intro t ht
    have hd := TwoLevelReference.chart_return_bounds hr h ht
    rw [abs_of_pos (h.return_range t ht).1]
    constructor <;> linarith [scale_pos r, scale_small hr]
  · intro t ht z hz n hn
    have hz' : ‖z‖ ≤ 6/5 := by convert hz using 1 <;> norm_num
    exact ThreeLevelReference.small_disk_orbit hr
      (TwoLevelReference.chart_parameter_band hr h ht) (sharp_input_bound h ht hz') n hn
  · intro t ht z w hz hw n hn hnr
    have hz' : ‖z‖ ≤ 6/5 := by convert hz using 1 <;> norm_num
    have hw' : ‖w‖ ≤ 6/5 := by convert hw using 1 <;> norm_num
    exact sharp_pair hr h ht hz' hw' n hn hnr
  · intro t ht z hz n hn hnr
    have hz' : ‖z‖ ≤ 6/5 := by convert hz using 1 <;> norm_num
    exact sharp_first hr h ht hz' n hn hnr
  · intro t ht z hz
    have he := normalized_return_error t r (by omega)
      (fun n _ => TwoLevelReference.chart_global_orbit_bound hr h ht n)
      (h.return_range t ht).1
      (by simpa only [scale, one_div_pow, mul_one_div] using (h.return_range t ht).2) z hz
    change ‖normalizedReturn t r z-complexMap (kappa r t) z‖ ≤ 24/(4 : ℝ)^r at he
    have he' : ‖normalizedReturn t r z-complexMap (kappa r t) z‖ ≤ 24*scale r := by
      simpa only [scale, one_div_pow, mul_one_div] using he
    linarith [scale_small hr]
  · have hl := TwoLevelReference.chart_left_relation_margin hr h
    linarith only [hl]
  · have hr' := TwoLevelReference.chart_right_relation_margin hr h
    linarith only [hr']

def Ancestors.empty (C : TerminalChart) : Ancestors C 0 where
  period := Fin.elim0
  target := Fin.elim0
  barrier := Fin.elim0
  core := Fin.elim0
  barrier_eq_half := fun i => Fin.elim0 i
  period_ge := fun i => Fin.elim0 i
  period_divides := fun i => Fin.elim0 i
  period_lt := fun i => Fin.elim0 i
  period_order := fun i => Fin.elim0 i
  radii := fun i => Fin.elim0 i
  orbit_bound := fun i => Fin.elim0 i
  critical_inside := fun i => Fin.elim0 i
  circle_escape := fun i => Fin.elim0 i
  core_inside := fun i => Fin.elim0 i
  pair_bound := fun i => Fin.elim0 i
  first_bound := fun i => Fin.elim0 i
  target_nesting := fun i => Fin.elim0 i
  nesting := fun i => Fin.elim0 i
  terminal_nesting := fun i => Fin.elim0 i

theorem exists_initial_chart : Nonempty TerminalChart := by
  obtain ⟨a,b,h⟩ := exists_sharp_chart 17 (by norm_num)
  exact ⟨TerminalChart.ofSharp (by norm_num : 17 ≤ 17) h⟩

/-- Every finite chart budget is attained by arbitrarily large new
outer periods; no asymptotic premise is assumed by the induction. -/
theorem TerminalChart.exists_admissible_prefix (C : TerminalChart) (lower : ℕ) :
    ∃ p : ℕ, lower ≤ p ∧ C.AdmissiblePrefix p := by
  obtain ⟨n,hn⟩ := pow_unbounded_of_one_lt
    (128*(5 : ℝ)^(6*C.period)/C.budget) (by norm_num : (1 : ℝ) < 4)
  let p := max n (max lower 17)
  have hnp : n ≤ p := le_max_left _ _
  have hlp : lower ≤ p := (le_max_left lower 17).trans (le_max_right n _)
  have h17 : 17 ≤ p := (le_max_right lower 17).trans (le_max_right n _)
  have hpow : (4 : ℝ)^n ≤ (4 : ℝ)^p := pow_le_pow_right₀ (by norm_num) hnp
  have hb := (div_lt_iff₀ C.budget_pos).mp (hn.trans_le hpow)
  have hm := mul_lt_mul_of_pos_right hb (scale_pos p)
  have hid : ((4 : ℝ)^p*C.budget)*scale p = C.budget := by
    calc
      _ = C.budget*(scale p*(4 : ℝ)^p) := by ring
      _ = C.budget := by rw [TwoLevelPerturbation.scale_mul_power, mul_one]
  rw [hid] at hm
  refine ⟨p,hlp,h17,?_⟩
  nlinarith only [hm]

end
end DepthGate
