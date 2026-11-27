import NearTwoTip
import QuadraticCrestCrossing

/-!
# A coherent crest curve in the original quadratic dynamical plane

For every period at least seventeen the parameter is constructed, then
one continuous injective curve supplies all selected radial crossings.
Every stated image and terminal inequality concerns the literal iterate
of the original quadratic polynomial.
-/

namespace ActualCrestTransport

open Set Function
open NearTwoShooting NearTwoTip LimitingCrestQuadraticReturn QuadraticCrestCrossing
noncomputable section

private theorem quadratic_iterate_zero (c : ℝ) (n : ℕ) :
    ((quadraticMap c)^[n]) (0 : ℂ) = (criticalValue c n : ℂ) := by
  induction n with
  | zero => simp [criticalValue]
  | succ n ih =>
    rw [iterate_succ_apply', ih, criticalValue_step]
    simp only [quadraticMap, Complex.ofReal_add, Complex.ofReal_pow]

/-- With no assumed parameter, return scale, or coefficient inequalities,
every p at least seventeen has an actual signed-tip parameter and one
injective continuous original-plane curve crossing every selected circle.
The complete second and third returns and both actual terminal cuts are
certified along the entire curve. -/
theorem exists_actual_unscaled_crest_curve (p : ℕ) (hp : 17 ≤ p) :
    ∃ c : ℝ, ActualTip p c ∧ ∃ γ : CrestRadius → ℂ,
      Continuous γ ∧ Injective γ ∧
      (∀ s t, ‖γ s-γ t‖ ≤ (15*criticalValue c p)*|(s : ℝ)-(t : ℝ)|) ∧
      ∀ s : CrestRadius,
        ‖γ s+((3*criticalValue c p/4 : ℝ) : ℂ)‖ = criticalValue c p*(s : ℝ) ∧
        (((quadraticMap c)^[p]) (γ s)).re = 0 ∧
        0 < (((quadraticMap c)^[p]) (γ s)).im ∧
        (((quadraticMap c)^[2*p]) (γ s)).im = 0 ∧
        (((quadraticMap c)^[3*p]) (γ s)).im = 0 ∧
        -criticalValue c p < (((quadraticMap c)^[3*p]) (γ s)).re ∧
        (((quadraticMap c)^[3*p]) (γ s)).re < -criticalValue c (4*p) := by
  obtain ⟨c, hc⟩ := exists_actual_tip p hp
  have hd : 0 < criticalValue c p := hc.2.1
  have hband := parameter_band hp hc.1
  have hsmall : criticalValue c p ≤ 12/(4 : ℝ)^p := by
    simpa only [scale, one_div_pow, mul_one_div] using hc.2.2.1
  obtain ⟨g, hLip, hginj, hgcont, hg⟩ := exists_lipschitz_actual_curve c p (by omega)
    ⟨hband.1, by linarith [hband.2]⟩ hd hsmall hc.2.2.2.1
  let d := criticalValue c p
  let γ : CrestRadius → ℂ := fun s => (d : ℂ)*g s
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hcont : Continuous γ := continuous_const.mul hgcont
  have hinj : Injective γ := by
    intro s t h
    apply hginj
    exact mul_left_cancel₀ hdC h
  have hbound (s t : CrestRadius) :
      ‖γ s-γ t‖ ≤ (15*criticalValue c p)*|(s : ℝ)-(t : ℝ)| := by
    have hnorm : ‖g s-g t‖ ≤ (15 : ℝ)*|(s : ℝ)-(t : ℝ)| := by
      simpa only [dist_eq_norm, Subtype.dist_eq, Real.dist_eq, Real.norm_eq_abs, NNReal.coe_ofNat]
        using hLip.dist_le_mul s t
    calc
      ‖γ s-γ t‖ = ‖(d : ℂ)*(g s-g t)‖ := by congr 1; dsimp [γ]; ring
      _ = d*‖g s-g t‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
      _ ≤ d*(15*|(s : ℝ)-(t : ℝ)|) := mul_le_mul_of_nonneg_left hnorm hd.le
      _ = (15*criticalValue c p)*|(s : ℝ)-(t : ℝ)| := by dsimp [d]; ring
  have hscale (s : CrestRadius) (m : ℕ) :
      ((quadraticMap c)^[m*p]) (γ s) =
        (d : ℂ)*((normalizedReturn c p)^[m]) (g s) :=
    (normalized_iterate_scale c p hd.ne' m (g s)).symm
  have hfourth := normalized_iterate_scale c p hd.ne' 4 (0 : ℂ)
  simp only [mul_zero] at hfourth
  rw [quadratic_iterate_zero] at hfourth
  have hfourthReal := congrArg Complex.re hfourth
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] at hfourthReal
  refine ⟨c, hc, γ, hcont, hinj, hbound, ?_⟩
  intro s
  obtain ⟨hr, hz, hpos, htwo, hthree, hlo, _, hcut⟩ := hg s
  have hfirst : ((quadraticMap c)^[p]) (γ s) =
      (d : ℂ)*normalizedReturn c p (g s) := by
    simpa only [one_mul, iterate_one] using hscale s 1
  have hthird : (((quadraticMap c)^[3*p]) (γ s)).re =
      d*(((normalizedReturn c p)^[3]) (g s)).re := by
    rw [hscale s 3]
    simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ‖γ s+((3*d/4 : ℝ) : ℂ)‖ = d*(s : ℝ)
    calc
      ‖γ s+((3*d/4 : ℝ) : ℂ)‖ = ‖(d : ℂ)*(g s+(3/4 : ℂ))‖ := by
        congr 1
        dsimp [γ]
        push_cast
        ring
      _ = d*‖g s+(3/4 : ℂ)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
      _ = d*(s : ℝ) := by rw [hr]
  · rw [hfirst]
    simpa using congrArg (fun t : ℝ => d*t) hz
  · rw [hfirst]
    simpa using mul_pos hd hpos
  · rw [hscale s 2]
    simpa using congrArg (fun t : ℝ => d*t) htwo
  · rw [hscale s 3]
    simpa using congrArg (fun t : ℝ => d*t) hthree
  · rw [hthird]
    have hnorm : (-1 : ℝ) < (((normalizedReturn c p)^[3]) (g s)).re :=
      (show (-1 : ℝ) < -999/1000 by norm_num).trans hlo
    have hm := mul_lt_mul_of_pos_left hnorm hd
    change -d < d*(((normalizedReturn c p)^[3]) (g s)).re
    linarith
  · rw [hthird]
    have hm := mul_lt_mul_of_pos_left hcut hd
    change d*(((normalizedReturn c p)^[3]) (g s)).re < -criticalValue c (4*p)
    dsimp [d] at *
    linarith

end
end ActualCrestTransport
