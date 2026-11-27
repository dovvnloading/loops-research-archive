import NearTwoTip

/-!
# Literal first-return separation on the positive shooting branch

The positive inverse itinerary controls the complete complex polynomial,
not just its critical orbit. Every intermediate image of the full physical
control disk stays outside the unit disk before the selected p-return.
-/

namespace ActualFirstReturnSeparation

open Set Function
open LimitingCrestQuadraticReturn NearTwoInverse NearTwoShooting NearTwoTip

noncomputable section

private theorem orbit_shadowing (c : ℝ) (n : ℕ) :
    ∀ (r : ℝ) (z : ℂ), 0 ≤ r →
      (∀ j : ℕ, j ≤ n+1 → |criticalValue c j| ≤ 2) →
      (8 : ℝ)^n*r^2 ≤ 1 → ‖z‖ ≤ r →
      ‖((quadraticMap c)^[n+1]) z - (criticalValue c (n+1) : ℂ)‖ ≤
        (8 : ℝ)^n*r^2 := by
  induction n with
  | zero =>
    intro r z hr hcrit hscale hz
    simpa only [Nat.zero_add, iterate_one, quadraticMap, criticalValue,
      iterate_one, zero_pow (by decide : 2 ≠ 0), zero_add, sub_self,
      Complex.ofReal_add, Complex.ofReal_zero, add_sub_cancel_right,
      norm_pow, pow_zero, one_mul] using pow_le_pow_left₀ (norm_nonneg z) hz 2
  | succ n ih =>
    intro r z hr hcrit hscale hz
    have hpow : (8 : ℝ)^n ≤ (8 : ℝ)^(n+1) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hsmall : (8 : ℝ)^n*r^2 ≤ 1 :=
      (mul_le_mul_of_nonneg_right hpow (sq_nonneg r)).trans hscale
    have hprev := ih r z hr (fun j hj => hcrit j (by omega)) hsmall hz
    have hcrit' := hcrit (n+1) (by omega)
    have hsum : ‖((quadraticMap c)^[n+1]) z +
        (criticalValue c (n+1) : ℂ)‖ ≤ 5 := by
      have hdecomp : ((quadraticMap c)^[n+1]) z + (criticalValue c (n+1) : ℂ) =
          (((quadraticMap c)^[n+1]) z - (criticalValue c (n+1) : ℂ)) +
            2*(criticalValue c (n+1) : ℂ) := by ring
      rw [hdecomp]
      have ht := norm_add_le
        (((quadraticMap c)^[n+1]) z - (criticalValue c (n+1) : ℂ))
        (2*(criticalValue c (n+1) : ℂ))
      rw [norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs] at ht
      linarith
    have hident : ((quadraticMap c)^[n+1+1]) z -
        (criticalValue c (n+1+1) : ℂ) =
        (((quadraticMap c)^[n+1]) z - (criticalValue c (n+1) : ℂ)) *
          (((quadraticMap c)^[n+1]) z + (criticalValue c (n+1) : ℂ)) := by
      rw [iterate_succ_apply', criticalValue_step]
      simp only [quadraticMap, Complex.ofReal_add, Complex.ofReal_pow]
      ring
    rw [hident, norm_mul]
    calc
      _ ≤ ((8 : ℝ)^n*r^2)*5 :=
        mul_le_mul hprev hsum (norm_nonneg _) (by positivity)
      _ ≤ (8 : ℝ)^(n+1)*r^2 := by
        rw [pow_succ (8 : ℝ) n]
        nlinarith only [show 0 ≤ (8 : ℝ)^n*r^2 by positivity]

private theorem scaled_disk_budget {p : ℕ} (hp : 17 ≤ p) {d : ℝ}
    (hd : 0 ≤ d) (hsmall : d ≤ 12*scale p) :
    (8 : ℝ)^p*((23/20 : ℝ)*d)^2 < 1/100 := by
  have hs : 0 ≤ scale p := (scale_pos p).le
  have hd' : (23/20 : ℝ)*d ≤ (69/5 : ℝ)*scale p := by linarith
  have hsq := pow_le_pow_left₀ (mul_nonneg (by norm_num : (0 : ℝ) ≤ 23/20) hd) hd' 2
  have hmul := mul_le_mul_of_nonneg_left hsq (show 0 ≤ (8 : ℝ)^p by positivity)
  have he : (scale p)^2 = ((1/4 : ℝ)^2)^p := by
    simp only [scale, ← pow_mul]
    rw [Nat.mul_comm p 2]
  have hscale : (8 : ℝ)^p*(scale p)^2 = (1/2 : ℝ)^p := by
    rw [he, ← mul_pow]
    norm_num
  have hbound : (8 : ℝ)^p*((23/20 : ℝ)*d)^2 ≤
      (4761/25 : ℝ)*(1/2 : ℝ)^p := by
    calc
      _ ≤ (8 : ℝ)^p*((69/5 : ℝ)*scale p)^2 := hmul
      _ = (4761/25 : ℝ)*((8 : ℝ)^p*(scale p)^2) := by ring
      _ = _ := by rw [hscale]
  have hpow := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) ≤ 1) hp
  norm_num at hpow
  linarith

/-- Every point in the complete physical p-return control disk shadows
its literal critical orbit to within one hundredth at every positive
iterate through p. The estimate is uniform in the selected parameter. -/
theorem actual_control_disk_shadowing {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {j : ℕ} (hj : 1 ≤ j) (hjp : j ≤ p)
    {z : ℂ} (hz : ‖z‖ ≤ (23/20 : ℝ)*criticalValue c p) :
    ‖((quadraticMap c)^[j]) z - (criticalValue c j : ℂ)‖ < 1/100 := by
  have hbudget := scaled_disk_budget hp hc.2.1.le hc.2.2.1
  have hpow : (8 : ℝ)^(j-1) ≤ (8 : ℝ)^p :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hsmall := mul_le_mul_of_nonneg_right hpow
    (sq_nonneg ((23/20 : ℝ)*criticalValue c p))
  have hscale : (8 : ℝ)^(j-1)*((23/20 : ℝ)*criticalValue c p)^2 ≤ 1 := by
    linarith
  have he := orbit_shadowing c (j-1) ((23/20 : ℝ)*criticalValue c p) z
    (mul_nonneg (by norm_num) hc.2.1.le)
    (fun k hk => hc.2.2.2.2.2.2 k (by omega)) hscale hz
  rw [Nat.sub_add_cancel hj] at he
  exact he.trans_lt (hsmall.trans_lt hbudget)

/-- The retained positive shooting identity forces every nonterminal
real critical iterate after the first one onto the positive inverse branch. -/
theorem shooting_critical_prefix_lower {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c)
    (hshoot : shooting (p-2) (criticalValue c p) c = 0)
    {j : ℕ} (hj : 2 ≤ j) (hjp : j < p) :
    7/5 ≤ criticalValue c j := by
  have hband := parameter_band hp hc.1
  have hd : criticalValue c p ∈ Icc (0 : ℝ) 2 :=
    terminal_band hp ⟨hc.2.1.le, hc.2.2.1⟩
  have hit := shooting_critical_itinerary hband hd hshoot (j-2) (by omega)
  rw [Nat.sub_add_cancel hj] at hit
  rw [hit]
  have hn : (p-2)-(j-2) = (p-j-1)+1 := by omega
  rw [hn]
  exact back_lower hband hd (p-j-1)

/-- The complete control disk has no early physical return: every
positive intermediate image before p lies outside the unit disk. This
is a theorem about the actual complex polynomial at every point of the
disk, with the inverse shooting identity supplied by the parameter chart. -/
theorem actual_first_return_exclusion {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c)
    (hshoot : shooting (p-2) (criticalValue c p) c = 0)
    {j : ℕ} (hj : 1 ≤ j) (hjp : j < p)
    {z : ℂ} (hz : ‖z‖ ≤ (23/20 : ℝ)*criticalValue c p) :
    1 < ‖((quadraticMap c)^[j]) z‖ := by
  have hshadow := actual_control_disk_shadowing hp hc hj hjp.le hz
  have htriangle := norm_le_norm_sub_add (criticalValue c j : ℂ)
    (((quadraticMap c)^[j]) z)
  rw [norm_sub_rev, Complex.norm_real, Real.norm_eq_abs] at htriangle
  by_cases hjone : j = 1
  · subst j
    have hval : criticalValue c 1 = c := by simp [criticalValue]
    rw [hval] at hshadow
    rw [hval, abs_of_nonpos (by linarith [(parameter_band hp hc.1).2])] at htriangle
    linarith [(parameter_band hp hc.1).2]
  · have hcrit := shooting_critical_prefix_lower hp hc hshoot (by omega) hjp
    rw [abs_of_nonneg (by linarith : 0 ≤ criticalValue c j)] at htriangle
    linarith

/-- The entire physical control disk lies inside the fixed disk of
radius one hundredth. -/
theorem actual_control_radius_small {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    (23/20 : ℝ)*criticalValue c p < 1/100 := by
  linarith [hc.2.2.1, scale_small hp]

/-- No positive iterate below the selected return time sends even one
point of the complete closed control disk back into that disk. -/
theorem actual_early_image_disjoint {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c)
    (hshoot : shooting (p-2) (criticalValue c p) c = 0)
    {j : ℕ} (hj : 1 ≤ j) (hjp : j < p) :
    Disjoint (Metric.closedBall (0 : ℂ) ((23/20 : ℝ)*criticalValue c p))
      (((quadraticMap c)^[j]) ''
        Metric.closedBall (0 : ℂ) ((23/20 : ℝ)*criticalValue c p)) := by
  apply Set.disjoint_left.mpr
  rintro z hz ⟨w, hw, rfl⟩
  have hw' : ‖w‖ ≤ (23/20 : ℝ)*criticalValue c p := by simpa using hw
  have hz' : ‖((quadraticMap c)^[j]) w‖ ≤ (23/20 : ℝ)*criticalValue c p := by
    simpa using hz
  linarith [actual_first_return_exclusion hp hc hshoot hj hjp hw',
    actual_control_radius_small hp hc]

end
end ActualFirstReturnSeparation
