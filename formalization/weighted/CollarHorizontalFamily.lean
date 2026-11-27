import CollarStraightLength
import CollarMetricEnergy
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A full horizontal family in an actual compact collar

The last contact with the inner plate and the first contact with the outer
circle produce a literal straight joining curve on every horizontal slice
through the inner disk. The full family gives a positive two-modulus, not
only existence of one curve. No regularity of the inner boundary is used.
-/

namespace CollarHorizontalFamily

open Set Metric MeasureTheory
open CollarExtremalLength CollarCapacityLower CollarStraightLength
open scoped ENNReal NNReal Topology

noncomputable section

theorem horizontal_norm_sq (y x : ℝ) :
    ‖horizontal y x‖^2 = x^2+y^2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [horizontal, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero,
    sub_zero, add_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add]
  ring

/-- The first outer-circle point of a horizontal half-ray. -/
theorem horizontal_circle_exit {R y : ℝ} (hR : 0 < R) (hy : |y| < R) :
    ∃ b : ℝ, 0 < b ∧ b ≤ R ∧ ‖horizontal y b‖ = R ∧
      ∀ x : ℝ, 0 ≤ x → x < b → ‖horizontal y x‖ < R := by
  have hy2 : y^2 < R^2 := by
    have h := mul_self_lt_mul_self (abs_nonneg y) hy
    nlinarith [sq_abs y]
  let b := Real.sqrt (R^2-y^2)
  have hbpos : 0 < b := Real.sqrt_pos.2 (sub_pos.mpr hy2)
  have hb2 : b^2 = R^2-y^2 := Real.sq_sqrt (sub_nonneg.mpr hy2.le)
  have hbR : b ≤ R := by nlinarith [sq_nonneg y]
  have hbnorm : ‖horizontal y b‖ = R := by
    have h := horizontal_norm_sq y b
    nlinarith [norm_nonneg (horizontal y b)]
  refine ⟨b, hbpos, hbR, hbnorm, ?_⟩
  intro x hx hxb
  have hsq := mul_self_lt_mul_self hx hxb
  have hn := horizontal_norm_sq y x
  nlinarith [norm_nonneg (horizontal y x)]

/-- Every horizontal slice through an inner point has a complete
straight joining segment after its last contact with the compact plate. -/
theorem exists_horizontal_joining {K : Set ℂ} {R y : ℝ}
    (hK : IsCompact K) (hinside : K ⊆ ball 0 R)
    (hR : 0 < R) (hy : |y| < R) (hzero : horizontal y 0 ∈ K) :
    ∃ a b : ℝ, 0 ≤ a ∧ a < b ∧ b ≤ R ∧
      Joining K R (straightCurve y a b) := by
  obtain ⟨b, hbpos, hbR, hbnorm, hbinner⟩ := horizontal_circle_exit hR hy
  let S : Set ℝ := Icc 0 b ∩ horizontal y ⁻¹' K
  have hS : IsCompact S :=
    isCompact_Icc.inter_right (hK.isClosed.preimage (horizontal_lipschitz y).continuous)
  have hS0 : (0 : ℝ) ∈ S := ⟨⟨le_rfl, hbpos.le⟩, hzero⟩
  obtain ⟨a, ha⟩ := hS.exists_isGreatest ⟨0, hS0⟩
  have ha0 : 0 ≤ a := ha.1.1.1
  have haK : horizontal y a ∈ K := ha.1.2
  have hab : a < b := by
    have hn : ‖horizontal y a‖ < R := by simpa using hinside haK
    by_contra h
    have he : a = b := le_antisymm ha.1.1.2 (le_of_not_gt h)
    rw [he, hbnorm] at hn
    exact lt_irrefl _ hn
  refine ⟨a, b, ha0, hab, hbR, ?_, ?_, ?_⟩
  · change horizontal y (a+(b-a)*0) ∈ K
    simpa using haK
  · change horizontal y (a+(b-a)*1) ∈ sphere 0 R
    simpa only [mul_one, add_sub_cancel, mem_sphere_zero_iff_norm] using hbnorm
  · intro t ht
    have hat : a < a+(b-a)*t := by
      nlinarith [mul_pos (sub_pos.mpr hab) ht.1]
    have htb : a+(b-a)*t < b := by
      nlinarith [mul_pos (sub_pos.mpr hab) (sub_pos.mpr ht.2)]
    have ht0 : 0 ≤ a+(b-a)*t := ha0.trans hat.le
    change horizontal y (a+(b-a)*t) ∈ ball 0 R \ K
    refine ⟨?_, ?_⟩
    · simpa only [mem_ball_zero_iff] using hbinner _ ht0 htb
    · intro hmem
      have hs : a+(b-a)*t ∈ S := ⟨⟨ht0, htb.le⟩, hmem⟩
      exact (not_le_of_gt hat) (ha.2 hs)

/-- Every admissible density has length at least one on the full
horizontal segment, since that segment contains a genuine joining curve. -/
theorem admissible_horizontal_slice {K : Set ℂ} {r R : ℝ}
    (hK : IsCompact K) (hinside : K ⊆ ball 0 R)
    (hr : 0 < r) (hrR : r < R) (hinner : ball (0 : ℂ) r ⊆ K)
    {ρ : ℂ → ℝ≥0∞} (hρ : admissibleMetric K R ρ)
    {y : ℝ} (hy : y ∈ Ioc (-r/2) (r/2)) :
    1 ≤ ∫⁻ x in Icc (0 : ℝ) R, ρ (horizontal y x) := by
  have hyabs : |y| < r := abs_lt.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hzero : horizontal y 0 ∈ K := by
    apply hinner
    simpa [horizontal, norm_mul, Complex.norm_real, Real.norm_eq_abs] using hyabs
  obtain ⟨a, b, ha0, hab, hbR, hj⟩ := exists_horizontal_joining hK hinside
    (hr.trans hrR) (hyabs.trans hrR) hzero
  have hlength := hρ.2 (straightCurve y a b) hj
  rw [metricLength_straightCurve hab hρ.1] at hlength
  exact hlength.trans (lintegral_mono_set (Icc_subset_Icc ha0 hbR))

/-- A disk in the actual plate forces positive modulus for the whole
rectifiable joining family. The density may be infinite and need not be
continuous or bounded. -/
theorem curveModulus_lower {K : Set ℂ} {r R : ℝ}
    (hK : IsCompact K) (hinside : K ⊆ ball 0 R)
    (hr : 0 < r) (hrR : r < R) (hinner : ball (0 : ℂ) r ⊆ K) :
    ENNReal.ofReal (r/R) ≤ curveModulus K R := by
  apply le_sInf
  rintro _ ⟨ρ, hρ, rfl⟩
  exact CollarMetricEnergy.planar_square_integral_lower hρ.1 hr (hr.trans hrR)
    (fun y hy => admissible_horizontal_slice hK hinside hr hrR hinner hρ hy)

/-- The same positive-area family bounds the standard joining-curve
extremal length from above. -/
theorem extremalLength_le_of_disk_subset {K : Set ℂ} {r R : ℝ}
    (hK : IsCompact K) (hinside : K ⊆ ball 0 R)
    (hr : 0 < r) (hrR : r < R) (hinner : ball (0 : ℂ) r ⊆ K) :
    extremalLength K R ≤ ENNReal.ofReal (R/r) := by
  change (curveModulus K R)⁻¹ ≤ _
  calc
    (curveModulus K R)⁻¹ ≤ (ENNReal.ofReal (r/R))⁻¹ :=
      ENNReal.inv_le_inv.mpr (curveModulus_lower hK hinside hr hrR hinner)
    _ = ENNReal.ofReal ((r/R)⁻¹) :=
      (ENNReal.ofReal_inv_of_pos (div_pos hr (hr.trans hrR))).symm
    _ = ENNReal.ofReal (R/r) := by rw [inv_div]

end
end CollarHorizontalFamily
