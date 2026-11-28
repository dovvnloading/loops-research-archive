import GlobalRestrictiveWindow
import GlobalInverseWindow

/-!+# Global localization of physical restrictive return intervals

The entire restrictive interval and all its intermediate images are given
in the original real quadratic coordinate.  Its parameter and physical
return scale are conclusions of the theorem below.
-/

namespace GlobalRestrictiveWindow

open Set Function
open NearTwoInverse NearTwoShooting LimitingCrestQuadraticReturn

noncomputable section

theorem PositiveRestrictiveReturn.small_parameter_band {c : ℝ} {p : ℕ}
    (hp : 17 ≤ p) (h : PositiveRestrictiveReturn c p) :
    c ∈ Icc (-2 : ℝ) (-2+1/10000) := by
  have hupper := h.parameter_upper hp
  have hscale := scale_small hp
  exact ⟨h.parameter_band.1, by linarith⟩

theorem PositiveRestrictiveReturn.inverse_parameter_budget {c : ℝ} {p : ℕ}
    (hp : 17 ≤ p) (h : PositiveRestrictiveReturn c p) :
    ((p-1 : ℕ) : ℝ)*(c+2) ≤ 1/10000 := by
  have hupper := h.parameter_upper hp
  have hscale := horizon_scale_small hp
  have hn : ((p-1 : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 1
  have hc : 0 ≤ c+2 := by linarith [h.parameter_band.1]
  have hmul := mul_le_mul_of_nonneg_right hn hc
  have hmul' := mul_le_mul_of_nonneg_left
    (show c+2 ≤ 20*scale p by linarith) (show (0 : ℝ) ≤ p by positivity)
  nlinarith only [hmul, hmul', hscale]

/-- The physical critical return has the sharp base-four scale, deduced
from invariance and the full intermediate itinerary. -/
theorem PositiveRestrictiveReturn.return_scale {c : ℝ} {p : ℕ}
    (hp : 17 ≤ p) (h : PositiveRestrictiveReturn c p) :
    criticalValue c p < 14*scale p := by
  apply GlobalInverseWindow.return_scale_bound hp (h.small_parameter_band hp)
    (h.inverse_parameter_budget hp) h.return_pos h.return_lt_three_halves
    (e := (realMap c)^[p] (criticalValue c p))
  · exact h.endpoint_return_mem
  · exact (h.inverse_displacement (by omega)).symm

/-- Global quantitative localization of every actual positive-itinerary
restrictive interval, with no assumed small parameter or return scale. -/
theorem restrictive_return_localization {c : ℝ} {p : ℕ}
    (hp : 17 ≤ p) (h : PositiveRestrictiveReturn c p) :
    c ∈ Ico (-2 : ℝ) (-2+20*scale p) ∧
      criticalValue c p ∈ Ioo (0 : ℝ) (14*scale p) :=
  ⟨⟨h.parameter_band.1, h.parameter_upper hp⟩,
    ⟨h.return_pos, h.return_scale hp⟩⟩

end

end GlobalRestrictiveWindow
