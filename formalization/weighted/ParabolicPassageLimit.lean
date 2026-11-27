import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

/-!
# Passage limits from a uniform discrete angular estimate

The hypothesis is a quantitative estimate at every prescribed error level.
Its two remaining terms vanish for every fixed positive angular window.
-/

namespace ParabolicPassageLimit

open Filter Set
open scoped Topology

/-- A fixed positive window exhausts a half-angle as the bottleneck scale
tends to zero through positive values. -/
theorem tendsto_arctan_scaled_sqrt {t : ℕ → ℝ} {R D : ℝ}
    (hR : 0 < R) (hD : 0 < D) (htpos : ∀ n, 0 < t n)
    (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => Real.arctan (D / Real.sqrt (R * t n)))
      atTop (𝓝 (Real.pi / 2)) := by
  have hproduct : Tendsto (fun n => R * t n) atTop (𝓝 0) := by
    simpa only [mul_zero] using ht.const_mul R
  have hsqrt : Tendsto (fun n => Real.sqrt (R * t n)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using hproduct.sqrt
  have hsqrtpos : ∀ᶠ n in atTop, 0 < Real.sqrt (R * t n) :=
    Eventually.of_forall fun n => Real.sqrt_pos.2 (mul_pos hR (htpos n))
  have hsqrtright : Tendsto (fun n => Real.sqrt (R * t n)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hsqrt, hsqrtpos⟩
  have hinv : Tendsto (fun n => (Real.sqrt (R * t n))⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp hsqrtright
  have hquot : Tendsto (fun n => D / Real.sqrt (R * t n)) atTop atTop := by
    simpa only [div_eq_mul_inv] using hinv.const_mul_atTop hD
  exact (Real.tendsto_arctan_atTop.mono_right inf_le_left).comp hquot

/-- The explicit outer-flight and angular-tail terms tend to zero. -/
theorem tendsto_passage_tail {t : ℕ → ℝ} {R D : ℝ}
    (hR : 0 < R) (hD : 0 < D) (htpos : ∀ n, 0 < t n)
    (ht : Tendsto t atTop (𝓝 0)) (C : ℝ) :
    Tendsto (fun n => C * Real.sqrt (t n) +
      (Real.pi - 2 * Real.arctan (D / Real.sqrt (R * t n))))
      atTop (𝓝 0) := by
  have hsqrt : Tendsto (fun n => Real.sqrt (t n)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using ht.sqrt
  have hangle := tendsto_arctan_scaled_sqrt hR hD htpos ht
  have hflight := hsqrt.const_mul C
  have htail : Tendsto
      (fun n => Real.pi - 2 * Real.arctan (D / Real.sqrt (R * t n)))
      atTop (𝓝 (Real.pi - 2 * (Real.pi / 2))) :=
    tendsto_const_nhds.sub (hangle.const_mul 2)
  have hconstant : Real.pi - 2 * (Real.pi / 2) = 0 := by ring
  simpa only [mul_zero, hconstant, zero_add] using hflight.add htail

/-- A quantitative error bound at every fixed small error level forces the
full angular passage limit.  The constants and window may depend on that
error level, but are fixed before the sequence index tends to infinity. -/
theorem tendsto_of_angle_error {f t : ℕ → ℝ} {R : ℝ}
    (hR : 0 < R) (htpos : ∀ n, 0 < t n)
    (ht : Tendsto t atTop (𝓝 0))
    (hbound : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ∃ C D : ℝ, 0 < D ∧ ∀ᶠ n in atTop,
        |f n - Real.pi| ≤ 280 * ε + C * Real.sqrt (t n) +
          (Real.pi - 2 * Real.arctan (D / Real.sqrt (R * t n)))) :
    Tendsto f atTop (𝓝 Real.pi) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η : ℝ := min (ε / 1120) (1 / 2)
  have hη : 0 < η := by
    dsimp [η]
    exact lt_min (by positivity) (by norm_num)
  have hηhalf : η ≤ 1 / 2 := min_le_right _ _
  have hηε : 280 * η ≤ ε / 4 := by
    have hle : η ≤ ε / 1120 := min_le_left _ _
    nlinarith
  obtain ⟨C, D, hD, hb⟩ := hbound η hη hηhalf
  have htail := tendsto_passage_tail hR hD htpos ht C
  have hsmall : ∀ᶠ n in atTop,
      C * Real.sqrt (t n) +
        (Real.pi - 2 * Real.arctan (D / Real.sqrt (R * t n))) < ε / 2 :=
    htail.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 2))
  filter_upwards [hb, hsmall] with n hbn hsn
  rw [Real.dist_eq]
  linarith

/-- Remove the exact factor seven from the angular passage normalization. -/
theorem tendsto_rate_of_scaled_rate {k : ℕ → ℕ} {t : ℕ → ℝ}
    (h : Tendsto (fun n => 7 * (k n : ℝ) * Real.sqrt (t n))
      atTop (𝓝 Real.pi)) :
    Tendsto (fun n => (k n : ℝ) * Real.sqrt (t n))
      atTop (𝓝 (Real.pi / 7)) := by
  have hdiv := h.div_const 7
  convert hdiv using 1
  funext n
  ring

/-- Squaring the passage limit gives the period-three parameter asymptotic. -/
theorem tendsto_quadratic_rate_of_rate {k : ℕ → ℕ} {t : ℕ → ℝ}
    (htnonneg : ∀ n, 0 ≤ t n)
    (h : Tendsto (fun n => (k n : ℝ) * Real.sqrt (t n))
      atTop (𝓝 (Real.pi / 7))) :
    Tendsto (fun n => 9 * (k n : ℝ) ^ 2 * t n)
      atTop (𝓝 (9 * Real.pi ^ 2 / 49)) := by
  have hsquare := (h.pow 2).const_mul 9
  have hsqrt_sq : ∀ n, Real.sqrt (t n) ^ 2 = t n :=
    fun n => Real.sq_sqrt (htnonneg n)
  have hconstant : 9 * (Real.pi / 7) ^ 2 = 9 * Real.pi ^ 2 / 49 := by ring
  simpa only [mul_pow, hsqrt_sq, hconstant, mul_assoc] using hsquare

/-- The full physical period `3*(k+2)`, including both exterior returns,
has the same sharp parameter coefficient. -/
theorem tendsto_physical_period_rate {k : ℕ → ℕ} {t : ℕ → ℝ}
    (htnonneg : ∀ n, 0 ≤ t n) (ht : Tendsto t atTop (𝓝 0))
    (hrate : Tendsto (fun n => (k n : ℝ) * Real.sqrt (t n))
      atTop (𝓝 (Real.pi / 7))) :
    Tendsto (fun n => ((3 * (k n + 2) : ℕ) : ℝ) ^ 2 * t n)
      atTop (𝓝 (9 * Real.pi ^ 2 / 49)) := by
  have hsqrt : Tendsto (fun n => Real.sqrt (t n)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using ht.sqrt
  have heq : (fun n => 3 * ((k n : ℝ) * Real.sqrt (t n)) +
      6 * Real.sqrt (t n)) =
      (fun n => ((3 * (k n + 2) : ℕ) : ℝ) * Real.sqrt (t n)) := by
    funext n
    push_cast
    ring
  have hconstant : 3 * (Real.pi / 7) + 6 * (0 : ℝ) = 3 * Real.pi / 7 := by ring
  have hlinear : Tendsto
      (fun n => ((3 * (k n + 2) : ℕ) : ℝ) * Real.sqrt (t n))
      atTop (𝓝 (3 * Real.pi / 7)) := by
    rw [← heq]
    simpa only [hconstant] using (hrate.const_mul 3).add (hsqrt.const_mul 6)
  have hsqrt_sq : ∀ n, Real.sqrt (t n) ^ 2 = t n :=
    fun n => Real.sq_sqrt (htnonneg n)
  have hconstant_sq : (3 * Real.pi / 7) ^ 2 = 9 * Real.pi ^ 2 / 49 := by ring
  simpa only [mul_pow, hsqrt_sq, hconstant_sq] using hlinear.pow 2

end ParabolicPassageLimit
