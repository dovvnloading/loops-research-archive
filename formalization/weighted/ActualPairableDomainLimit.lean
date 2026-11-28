import ActualPairableSource
import ActualParentMarks

/-!
# The actual normalized pairable sources exhaust the plane

The source is the complete archived component, normalized by its actual
critical value.  The full physical-disk divided-difference estimate gives
a quadratic growth bound throughout the expanding normalized disk.
Consequently every fixed compact set eventually lies in the actual source.
-/

namespace ActualPairableDomainLimit

open Set Filter Metric
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn
open QuadraticCrestDividedDifference ActualPairableSource ActualParentMarks
open scoped Topology

noncomputable section

def normalizedSource (c : ℝ) (p : ℕ) : Set ℂ :=
  (fun z : ℂ => (criticalValue c p : ℂ)*z) ⁻¹' source c p

private theorem radius_scale_identity (p : ℕ) :
    (4 : ℝ)^p * ((1/2 : ℝ)^p)^2 = 1 := by
  rw [← pow_mul, Nat.mul_comm p 2, pow_mul, ← mul_pow]
  norm_num

private theorem four_pow_mul_scale (p : ℕ) :
    (4 : ℝ)^p * scale p = 1 := by
  simp only [scale, ← mul_pow]
  norm_num

/-- After multiplication by the actual critical scale, the complete
divided difference is uniformly bounded on the whole physical disk. -/
theorem scaled_evenSecant_norm_le_two {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z w : ℂ}
    (hz : ‖z‖ ≤ radius p) (hw : ‖w‖ ≤ radius p) :
    criticalValue c p * ‖evenSecant c (p-1) z w‖ ≤ 2 := by
  have hp' : p-1+1 = p := by omega
  have hpow : (4 : ℝ)^p = (4 : ℝ)^(p-1)*4 := by
    simpa only [hp'] using pow_succ (4 : ℝ) (p-1)
  have he := evenSecant_error c (p-1) ((1/2 : ℝ)^p) z w (by positivity)
    (by simpa only [hp'] using hc.2.2.2.2.2.2)
    (by rw [hp',radius_scale_identity]) hz hw
  rw [hp',radius_scale_identity,mul_one] at he
  have he' : ‖evenSecant c (p-1) z w - (quadraticCoefficient c (p-1) : ℂ)‖ ≤
      (4 : ℝ)^p / 64 := by linarith
  have hcoef := ActualPairableSourceBounds.coefficient_lower hc
  have hneg : quadraticCoefficient c (p-1) < 0 := by
    have hpos : 0 < (1/8 : ℝ) * (4 : ℝ)^p := by positivity
    linarith
  have hnorm : ‖evenSecant c (p-1) z w‖ ≤
      (4 : ℝ)^p/64 - quadraticCoefficient c (p-1) := by
    calc
      _ = ‖(evenSecant c (p-1) z w - (quadraticCoefficient c (p-1) : ℂ)) +
          (quadraticCoefficient c (p-1) : ℂ)‖ := by congr 1; ring
      _ ≤ ‖evenSecant c (p-1) z w - (quadraticCoefficient c (p-1) : ℂ)‖ +
          ‖(quadraticCoefficient c (p-1) : ℂ)‖ := norm_add_le _ _
      _ ≤ (4 : ℝ)^p/64 - quadraticCoefficient c (p-1) := by
        rw [Complex.norm_real,Real.norm_eq_abs,abs_of_neg hneg]
        linarith
  have hscale : criticalValue c p * (4 : ℝ)^p ≤ 12 := by
    have h := mul_le_mul_of_nonneg_right hc.2.2.1 (show 0 ≤ (4 : ℝ)^p by positivity)
    have hs := four_pow_mul_scale p
    nlinarith
  have hk : -quadraticCoefficient c (p-1) * criticalValue c p ≤ 17904/10000 :=
    hc.2.2.2.1.2
  have hm := mul_le_mul_of_nonneg_left hnorm hc.2.1.le
  nlinarith

/-- The complete return has a uniform quadratic growth bound throughout
the entire expanding normalized target disk. -/
theorem scaled_return_norm_le {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ}
    (hz : ‖(criticalValue c p : ℂ)*z‖ ≤ radius p) :
    ‖returnMap c p ((criticalValue c p : ℂ)*z)‖ ≤
      criticalValue c p * (1+2*‖z‖^2) := by
  have hs := scaled_evenSecant_norm_le_two hp hc hz
    (show ‖(0 : ℂ)‖ ≤ radius p by simpa using (radius_pos p).le)
  have hid := iterate_difference c (p-1) ((criticalValue c p : ℂ)*z) 0
  rw [show p-1+1 = p by omega] at hid
  change returnMap c p ((criticalValue c p : ℂ)*z) - returnMap c p 0 = _ at hid
  simp only [returnMap_zero,zero_pow (by omega : 2 ≠ 0),sub_zero] at hid
  have he : returnMap c p ((criticalValue c p : ℂ)*z) =
      (criticalValue c p : ℂ) + ((criticalValue c p : ℂ)*z)^2 *
        evenSecant c (p-1) ((criticalValue c p : ℂ)*z) 0 := by
    linear_combination hid
  rw [he]
  have ht := norm_add_le (criticalValue c p : ℂ)
    (((criticalValue c p : ℂ)*z)^2 * evenSecant c (p-1) ((criticalValue c p : ℂ)*z) 0)
  simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hc.2.1] at ht
  have hm := mul_le_mul_of_nonneg_left hs
    (mul_nonneg hc.2.1.le (sq_nonneg ‖z‖))
  nlinarith

theorem closedBall_subset_normalizedSource {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {L : ℝ}
    (hsmall : L < targetRadius c p) (himage : 1+2*L^2 < targetRadius c p) :
    closedBall (0 : ℂ) L ⊆ normalizedSource c p := by
  intro z hz
  have hn : ‖z‖ ≤ L := mem_closedBall_zero_iff.mp hz
  have hphys : ‖(criticalValue c p : ℂ)*z‖ ≤ radius p := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hc.2.1]
    have h := (lt_div_iff₀ hc.2.1).mp hsmall
    have hm := mul_le_mul_of_nonneg_left hn hc.2.1.le
    change L * criticalValue c p < radius p at h
    nlinarith
  apply (mem_source_iff hp hc hphys).mpr
  rw [mem_ball_zero_iff]
  have hg := scaled_return_norm_le hp hc hphys
  have hs : ‖z‖^2 ≤ L^2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have h := (lt_div_iff₀ hc.2.1).mp himage
  change (1+2*L^2) * criticalValue c p < radius p at h
  nlinarith [mul_le_mul_of_nonneg_left hs hc.2.1.le]

/-- Every fixed normalized closed ball eventually lies in the complete
actual archived source, for every sequence of actual signed tips. -/
theorem eventually_closedBall_subset (c : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n)) (L : ℝ) :
    ∀ᶠ n in atTop, closedBall (0 : ℂ) L ⊆ normalizedSource (c n) (n+17) := by
  have hR := targetRadius_tendsto c hc
  filter_upwards [hR.eventually (eventually_gt_atTop (max L 0)),
    hR.eventually (eventually_gt_atTop (1+2*(max L 0)^2))] with n hsmall himage
  exact (closedBall_subset_closedBall (le_max_left L 0)).trans
    (closedBall_subset_normalizedSource (by omega) (hc n) hsmall himage)

/-- Compact subsets of the plane are eventually contained in the
normalized actual sources; this is a conclusion, not a kernel-limit premise. -/
theorem eventually_compact_subset (c : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n)) {K : Set ℂ} (hK : IsCompact K) :
    ∀ᶠ n in atTop, K ⊆ normalizedSource (c n) (n+17) := by
  obtain ⟨L,hL⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  filter_upwards [eventually_closedBall_subset c hc L] with n hn
  exact hL.trans hn

end
end ActualPairableDomainLimit
