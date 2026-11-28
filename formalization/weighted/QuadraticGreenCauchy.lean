import QuadraticGreenPressure
import Mathlib.Analysis.Complex.Liouville

/-! Necessary finite-scale parameter sensitivity bounds from actual Green
sublevel disks. The analytic input is the classical Cauchy estimate. -/

namespace QuadraticEscape

open Set Metric

noncomputable section

private theorem criticalValue_parameter_differentiable (n : ℕ) :
    Differentiable ℂ (fun d : ℂ => orbit d n d) := by
  induction n with
  | zero =>
      change Differentiable ℂ (id : ℂ → ℂ)
      exact differentiable_id
  | succ n ih =>
      change Differentiable ℂ (fun d : ℂ => (orbit d n d)^2+d)
      exact (ih.pow 2).add differentiable_id

/-- A bound at the natural Green scale bounds the actual critical-value
polynomial. The height B is arbitrary; no bounded-orbit premise is needed. -/
theorem criticalValue_norm_of_green_scale (d : ℂ) (n : ℕ) {C B : ℝ}
    (hd : ‖d‖ ≤ C) (hg : parameterEscape d ≤ weight n * B) :
    ‖orbit d n d‖ ≤ (1+C) * Real.exp B := by
  have hC : 0 < 1+C := by linarith only [hd, norm_nonneg d]
  have herr := (abs_le.mp (escape_error d d hd n)).2
  have hg' : escape d d ≤ weight n * B := hg
  change weight n * logSize (orbit d n d) - escape d d ≤
    weight n * Real.log (1+C) at herr
  have hscaled : weight n * logSize (orbit d n d) ≤
      weight n * (B+Real.log (1+C)) := by
    nlinarith only [herr, hg']
  have hlog := (mul_le_mul_iff_right₀ (weight_pos n)).mp hscaled
  unfold logSize at hlog
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (size_pos _), Real.exp_add, Real.exp_log hC] at he
  calc
    ‖orbit d n d‖ ≤ size (orbit d n d) := norm_le_size _
    _ ≤ Real.exp B * (1+C) := he
    _ = (1+C) * Real.exp B := by ring

private theorem green_scale_circle_bound (c : ℂ) (n : ℕ) {r B : ℝ}
    (hg : ∀ d : ℂ, ‖d-c‖ ≤ r → parameterEscape d ≤ weight n * B) :
    ∀ d ∈ sphere c r,
      ‖orbit d n d‖ ≤ (1+‖c‖+r) * Real.exp B := by
  intro d hd
  have hdist : ‖d-c‖ = r := mem_sphere_iff_norm.mp hd
  have hdn : ‖d‖ ≤ ‖c‖+r := by
    calc
      ‖d‖ = ‖(d-c)+c‖ := by rw [sub_add_cancel]
      _ ≤ ‖d-c‖+‖c‖ := norm_add_le _ _
      _ = ‖c‖+r := by rw [hdist]; ring
  have h := criticalValue_norm_of_green_scale d n hdn (hg d hdist.le)
  simpa only [add_assoc] using h

/-- Every parameter derivative order supplies a necessary condition for
an actual Green sublevel disk. The factorial is the classical Cauchy one. -/
theorem green_disk_iteratedDeriv_bound (c : ℂ) (n k : ℕ) {r B : ℝ}
    (hr : 0 < r)
    (hg : ∀ d : ℂ, ‖d-c‖ ≤ r → parameterEscape d ≤ weight n * B) :
    r^k * ‖iteratedDeriv k (fun d : ℂ => orbit d n d) c‖ ≤
      (k.factorial : ℝ) * (1+‖c‖+r) * Real.exp B := by
  have hbound := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    k hr (criticalValue_parameter_differentiable n).diffContOnCl
    (green_scale_circle_bound c n hg)
  have hmul := (le_div_iff₀ (pow_pos hr k)).mp hbound
  calc
    r^k * ‖iteratedDeriv k (fun d : ℂ => orbit d n d) c‖ =
        ‖iteratedDeriv k (fun d : ℂ => orbit d n d) c‖ * r^k := by ring
    _ ≤ (k.factorial : ℝ) * ((1+‖c‖+r) * Real.exp B) := hmul
    _ = (k.factorial : ℝ) * (1+‖c‖+r) * Real.exp B := by ring

/-- First parameter sensitivity version, on the actual polynomial P_n(c). -/
theorem green_disk_deriv_bound (c : ℂ) (n : ℕ) {r B : ℝ}
    (hr : 0 < r)
    (hg : ∀ d : ℂ, ‖d-c‖ ≤ r → parameterEscape d ≤ weight n * B) :
    r * ‖deriv (fun d : ℂ => orbit d n d) c‖ ≤
      (1+‖c‖+r) * Real.exp B := by
  have hbound := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
    (criticalValue_parameter_differentiable n).diffContOnCl
    (green_scale_circle_bound c n hg)
  have hmul := (le_div_iff₀ hr).mp hbound
  calc
    r * ‖deriv (fun d : ℂ => orbit d n d) c‖ =
        ‖deriv (fun d : ℂ => orbit d n d) c‖ * r := by ring
    _ ≤ (1+‖c‖+r) * Real.exp B := hmul

/-- On a radius-at-most-one disk centered in the actual Mandelbrot locus,
the geometric factor in the necessary sensitivity bound is at most four. -/
theorem green_disk_deriv_bound_four (c : ℂ) (n : ℕ) {r B : ℝ}
    (hc : parameterEscape c = 0) (hr : 0 < r) (hr1 : r ≤ 1)
    (hg : ∀ d : ℂ, ‖d-c‖ ≤ r → parameterEscape d ≤ weight n * B) :
    r * ‖deriv (fun d : ℂ => orbit d n d) c‖ ≤ 4 * Real.exp B := by
  have h := green_disk_deriv_bound c n hr hg
  have hcoef : 1+‖c‖+r ≤ 4 := by
    linarith only [parameter_norm_le_two c hc, hr1]
  exact h.trans (mul_le_mul_of_nonneg_right hcoef (Real.exp_pos B).le)

/-- Excess actual parameter sensitivity forces a genuine parameter in the
disk above the proposed Green sublevel. No sample points are assumed. -/
theorem green_disk_superlevel_of_deriv (c : ℂ) (n : ℕ) {r B : ℝ}
    (hr : 0 < r)
    (hd : (1+‖c‖+r) * Real.exp B <
      r * ‖deriv (fun d : ℂ => orbit d n d) c‖) :
    ∃ d : ℂ, ‖d-c‖ ≤ r ∧ weight n * B < parameterEscape d := by
  by_contra h
  push_neg at h
  exact (not_le_of_gt hd) (green_disk_deriv_bound c n hr h)

end

end QuadraticEscape
