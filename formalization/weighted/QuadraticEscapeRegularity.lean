import QuadraticEscapeHolder

/-!
# Uniform strict improvement away from the Chebyshev parameter

The anchors are actual parameters with bounded critical orbit. Separation
from the parameter -2 gives one common power, one common constant, and a
uniform small-scale estimate relative to the square-root modulus.
-/

namespace QuadraticEscape

open Filter
open scoped Topology

private theorem separated_base_bounds (η : ℝ) (hη : 0 ≤ η) (hη4 : η ≤ 4) :
    3 ≤ 4-η^2/576 ∧ 4-η^2/576 ≤ 4 := by
  have hs := pow_le_pow_left₀ hη hη4 2
  constructor <;> nlinarith [sq_nonneg η]

private theorem separated_exponent_gt_half (η : ℝ) (hη : 0 < η) (hη4 : η ≤ 4) :
    (1:ℝ)/2 < Real.log 2 / Real.log (4-η^2/576) := by
  have hA := (separated_base_bounds η hη.le hη4).1
  have hlt : 4-η^2/576 < 4 := by nlinarith [sq_pos_of_pos hη]
  have hlogA : 0 < Real.log (4-η^2/576) := Real.log_pos (by linarith)
  have hloglt : Real.log (4-η^2/576) < Real.log 4 :=
    Real.log_lt_log (by linarith) hlt
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    have hp := Real.log_pow (2:ℝ) 2
    norm_num at hp
    exact hp
  apply (lt_div_iff₀ hlogA).mpr
  rw [hlog4] at hloglt
  linarith

/-- A single strictly improved exponent and the same explicit constant
work at every zero-potential parameter at least η away from -2. -/
theorem parameter_escape_holder_uniform (η : ℝ) (hη : 0 < η) (hη4 : η ≤ 4)
    (c d : ℂ) (hc : parameterEscape c = 0) (hsep : η ≤ ‖c+2‖)
    (hd : ‖d-c‖ ≤ 1/2) :
    parameterEscape d ≤ 4 * Real.log 4 *
      (2*‖d-c‖) ^ (Real.log 2 / Real.log (4-η^2/576)) := by
  obtain ⟨hA,hA4⟩ := separated_base_bounds η hη.le hη4
  apply parameter_escape_holder_of_growth c d hc hA hA4 _ hd
  intro j
  have hb := (parameter_gap_base c hc).2.2 j
  have hs := pow_le_pow_left₀ hη.le hsep 2
  nlinarith

/-- The square-root-normalized potential has a positive-power bound,
uniformly over all separated zero-potential anchors. The estimate also
includes d=c, where the normalized quotient is zero. -/
theorem parameter_escape_sqrt_ratio_bound (η : ℝ) (hη : 0 < η) (hη4 : η ≤ 4)
    (c d : ℂ) (hc : parameterEscape c = 0) (hsep : η ≤ ‖c+2‖)
    (hd : ‖d-c‖ ≤ 1/2) :
    parameterEscape d / Real.sqrt ‖d-c‖ ≤
      (4 * Real.log 4 * (2:ℝ) ^ (Real.log 2 / Real.log (4-η^2/576))) *
        ‖d-c‖ ^ (Real.log 2 / Real.log (4-η^2/576) - 1/2) := by
  let α : ℝ := Real.log 2 / Real.log (4-η^2/576)
  have hα : 1/2 < α := separated_exponent_gt_half η hη hη4
  by_cases hdc : d = c
  · subst d
    simp only [sub_self, norm_zero, Real.sqrt_zero, div_zero]
    positivity
  · have hδ : 0 < ‖d-c‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hdc)
    have hb := parameter_escape_holder_uniform η hη hη4 c d hc hsep hd
    have hdiv := div_le_div_of_nonneg_right hb (Real.sqrt_nonneg ‖d-c‖)
    change parameterEscape d / Real.sqrt ‖d-c‖ ≤
      (4 * Real.log 4 * (2:ℝ)^α) * ‖d-c‖^(α-1/2)
    calc
      parameterEscape d / Real.sqrt ‖d-c‖ ≤
          (4 * Real.log 4 * (2*‖d-c‖)^α) / Real.sqrt ‖d-c‖ := hdiv
      _ = (4 * Real.log 4 * (2:ℝ)^α) * ‖d-c‖^(α-1/2) := by
        rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hδ.le,
          Real.sqrt_eq_rpow, Real.rpow_sub hδ]
        ring

/-- Uniform little-o estimate with an explicit common radius. This is
a quantitative statement over all anchors, not a separate pointwise
continuity assertion for each parameter. -/
theorem parameter_escape_uniform_sqrt_decay
    (η ε : ℝ) (hη : 0 < η) (hη4 : η ≤ 4) (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ c d : ℂ,
      parameterEscape c = 0 → η ≤ ‖c+2‖ → ‖d-c‖ ≤ ρ →
      parameterEscape d / Real.sqrt ‖d-c‖ ≤ ε := by
  let α : ℝ := Real.log 2 / Real.log (4-η^2/576)
  let β : ℝ := α-1/2
  let C : ℝ := 4 * Real.log 4 * (2:ℝ)^α
  have hα : 1/2 < α := separated_exponent_gt_half η hη hη4
  have hβ : 0 < β := by dsimp [β]; linarith
  have hC : 0 < C := by
    dsimp [C]
    exact mul_pos (mul_pos (by norm_num) (Real.log_pos (by norm_num)))
      (Real.rpow_pos_of_pos (by norm_num) _)
  let ρ : ℝ := min (1/2) ((ε/C)^β⁻¹)
  have hρ : 0 < ρ := lt_min (by norm_num)
    (Real.rpow_pos_of_pos (div_pos hε hC) _)
  refine ⟨ρ,hρ,?_⟩
  intro c d hc hsep hd
  have hdhalf : ‖d-c‖ ≤ 1/2 := hd.trans (min_le_left _ _)
  have hb := parameter_escape_sqrt_ratio_bound η hη hη4 c d hc hsep hdhalf
  change parameterEscape d / Real.sqrt ‖d-c‖ ≤ C * ‖d-c‖^β at hb
  have hpow : ‖d-c‖^β ≤ ε/C := by
    calc
      ‖d-c‖^β ≤ ((ε/C)^β⁻¹)^β :=
        Real.rpow_le_rpow (norm_nonneg _) (hd.trans (min_le_right _ _)) hβ.le
      _ = ε/C := Real.rpow_inv_rpow (div_pos hε hC).le (ne_of_gt hβ)
  calc
    parameterEscape d / Real.sqrt ‖d-c‖ ≤ C * ‖d-c‖^β := hb
    _ ≤ C * (ε/C) := mul_le_mul_of_nonneg_left hpow hC.le
    _ = ε := mul_div_cancel₀ _ (ne_of_gt hC)

/-- At every bounded-critical-orbit parameter except -2, the actual
potential divided by square-root distance tends to zero. -/
theorem parameter_escape_sqrt_ratio_tendsto_zero (c : ℂ)
    (hc : parameterEscape c = 0) (hne : c ≠ -2) :
    Tendsto (fun d : ℂ => parameterEscape d / Real.sqrt ‖d-c‖) (𝓝 c) (𝓝 0) := by
  have hη : 0 < ‖c+2‖ := norm_pos_iff.mpr (by
    intro h
    apply hne
    linear_combination h)
  have hη4 : ‖c+2‖ ≤ 4 := by
    calc
      ‖c+2‖ ≤ ‖c‖ + ‖(2:ℂ)‖ := norm_add_le _ _
      _ ≤ 4 := by rw [Complex.norm_two]; linarith [parameter_norm_le_two c hc]
  apply Metric.tendsto_nhds_nhds.mpr
  intro ε hε
  obtain ⟨ρ,hρ,hb⟩ := parameter_escape_uniform_sqrt_decay ‖c+2‖ (ε/2)
    hη hη4 (by linarith)
  refine ⟨ρ,hρ,?_⟩
  intro d hd
  have hd' : ‖d-c‖ ≤ ρ := by simpa only [dist_eq_norm] using hd.le
  have he := hb c d hc le_rfl hd'
  have hg : 0 ≤ parameterEscape d / Real.sqrt ‖d-c‖ :=
    div_nonneg (escape_nonneg d d) (Real.sqrt_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hg]
  linarith

/-- Formal little-o version, with the zero-denominator case tied
to the actual zero-potential anchor. -/
theorem parameter_escape_isLittleO_sqrt (c : ℂ)
    (hc : parameterEscape c = 0) (hne : c ≠ -2) :
    parameterEscape =o[𝓝 c] (fun d : ℂ => Real.sqrt ‖d-c‖) := by
  apply (Asymptotics.isLittleO_iff_tendsto (fun d hd => ?_)).mpr
    (parameter_escape_sqrt_ratio_tendsto_zero c hc hne)
  have hnorm : ‖d-c‖ = 0 := (Real.sqrt_eq_zero (norm_nonneg _)).mp hd
  have hdc : d = c := sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  simpa only [hdc] using hc

end QuadraticEscape
