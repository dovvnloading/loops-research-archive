import ThreeReturnDegree
import NearTwoTip

/-!
# Complete-polynomial estimates on the archived physical target disk

The whole disk of radius `2⁻ᵖ`, rather than a fixed smaller normalized
collar, has a nonvanishing even divided difference and a strict return
barrier.  These are the analytic inputs for constructing the full
archived two-sheet source component.
-/

namespace ActualPairableSourceBounds

open Set Function
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn
open QuadraticCrestDividedDifference ThreeReturnDegree

noncomputable section

private theorem radius_scale_identity (p : ℕ) :
    (4 : ℝ)^p * ((1/2 : ℝ)^p)^2 = 1 := by
  rw [← pow_mul, Nat.mul_comm p 2, pow_mul, ← mul_pow]
  norm_num

private theorem four_pow_mul_scale (p : ℕ) :
    (4 : ℝ)^p * scale p = 1 := by
  simp only [scale, ← mul_pow]
  norm_num

/-- A coefficient lower bound valid for every actual signed tip, without
an additional positive-inverse itinerary hypothesis. -/
theorem coefficient_lower {p : ℕ} {c : ℝ} (hc : ActualTip p c) :
    (1/8 : ℝ) * (4 : ℝ)^p ≤ -quadraticCoefficient c (p-1) := by
  have hk : (7/4 : ℝ) ≤ -quadraticCoefficient c (p-1) * criticalValue c p := by
    have hl := hc.2.2.2.1.1
    change 17903/10000 ≤ kappa p c at hl
    unfold kappa at hl
    linarith
  have hcoef : 0 < -quadraticCoefficient c (p-1) := by
    by_contra h
    have hn := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hc.2.1.le
    linarith
  have hmul := mul_le_mul_of_nonneg_left hc.2.2.1 hcoef.le
  apply (mul_le_mul_iff_left₀ (scale_pos p)).mp
  have he := four_pow_mul_scale p
  nlinarith

/-- The divided difference has uniformly negative real part on the entire
closed archived physical disk. -/
theorem evenSecant_re_le {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z w : ℂ}
    (hz : ‖z‖ ≤ (1/2 : ℝ)^p) (hw : ‖w‖ ≤ (1/2 : ℝ)^p) :
    (evenSecant c (p-1) z w).re ≤ -(7/64 : ℝ) * (4 : ℝ)^p := by
  have hp' : p-1+1 = p := by omega
  have hpow : (4 : ℝ)^p = (4 : ℝ)^(p-1)*4 := by
    simpa only [hp'] using pow_succ (4 : ℝ) (p-1)
  have he := evenSecant_error c (p-1) ((1/2 : ℝ)^p) z w (by positivity)
    (by simpa only [hp'] using hc.2.2.2.2.2.2)
    (by rw [hp',radius_scale_identity]) hz hw
  rw [hp',radius_scale_identity,mul_one] at he
  have hre := (Complex.re_le_norm
    (evenSecant c (p-1) z w - (quadraticCoefficient c (p-1) : ℂ))).trans he
  simp only [Complex.sub_re,Complex.ofReal_re] at hre
  have ha := coefficient_lower hc
  linarith

theorem evenSecant_re_neg {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z w : ℂ}
    (hz : ‖z‖ ≤ (1/2 : ℝ)^p) (hw : ‖w‖ ≤ (1/2 : ℝ)^p) :
    (evenSecant c (p-1) z w).re < 0 :=
  (evenSecant_re_le hp hc hz hw).trans_lt
    (mul_neg_of_neg_of_pos (by norm_num) (by positivity))

theorem evenSecant_ne_zero {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z w : ℂ}
    (hz : ‖z‖ ≤ (1/2 : ℝ)^p) (hw : ‖w‖ ≤ (1/2 : ℝ)^p) :
    evenSecant c (p-1) z w ≠ 0 := by
  intro he
  have h := evenSecant_re_neg hp hc hz hw
  simp [he] at h

/-- The complete p-return has exactly the original quadratic collision
relation on the closed physical target disk. -/
theorem archived_collision_iff {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z w : ℂ}
    (hz : ‖z‖ ≤ (1/2 : ℝ)^p) (hw : ‖w‖ ≤ (1/2 : ℝ)^p) :
    ((quadraticMap c)^[p]) z = ((quadraticMap c)^[p]) w ↔ z = w ∨ z = -w := by
  have hp' : p-1+1 = p := by omega
  have hid := iterate_difference c (p-1) z w
  rw [hp'] at hid
  constructor
  · intro h
    have hprod : (z^2-w^2)*evenSecant c (p-1) z w = 0 := by
      rw [← hid,h,sub_self]
    have hzsq := (mul_eq_zero.mp hprod).resolve_right (evenSecant_ne_zero hp hc hz hw)
    have hfactor : (z-w)*(z+w) = 0 := by
      calc
        (z-w)*(z+w) = z^2-w^2 := by ring
        _ = 0 := hzsq
    rcases mul_eq_zero.mp hfactor with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  · intro h
    apply sub_eq_zero.mp
    rw [hid]
    rcases h with rfl | rfl <;> simp

theorem archived_hasDerivAt (c : ℝ) {p : ℕ} (hp : 1 ≤ p) (z : ℂ) :
    HasDerivAt ((quadraticMap c)^[p]) (2*z*evenSecant c (p-1) z z) z := by
  simpa only [Nat.sub_add_cancel hp] using iterate_hasDerivAt c (p-1) z

theorem archived_derivative_ne_zero {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : ‖z‖ ≤ (1/2 : ℝ)^p) (hz0 : z ≠ 0) :
    2*z*evenSecant c (p-1) z z ≠ 0 :=
  mul_ne_zero (mul_ne_zero (by norm_num) hz0) (evenSecant_ne_zero hp hc hz hz)

/-- The nonlinear remainder is uniformly small on the original physical disk. -/
theorem archived_remainder_le {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : ‖z‖ ≤ (1/2 : ℝ)^p) :
    ‖quadraticRemainder c (p-1) z‖ ≤ (1/128 : ℝ) := by
  have hp' : p-1+1 = p := by omega
  have h := complete_remainder_bound c (p-1) ((1/2 : ℝ)^p) z (by positivity)
    (by simpa only [hp'] using hc.2.2.2.2.2.2)
    (by rw [hp',radius_scale_identity]) hz
  simpa only [hp',radius_scale_identity,one_pow] using h

/-- The physical target circle has a fixed positive complete-return margin. -/
theorem archived_boundary_norm_lower {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : ‖z‖ = (1/2 : ℝ)^p) :
    (1/10 : ℝ) < ‖((quadraticMap c)^[p]) z‖ := by
  have hp' : p-1+1 = p := by omega
  have hcoef := coefficient_lower hc
  have hneg : quadraticCoefficient c (p-1) < 0 := by
    have hpos : 0 < (1/8 : ℝ) * (4 : ℝ)^p := by positivity
    linarith
  have hlead : (1/8 : ℝ) ≤ ‖(quadraticCoefficient c (p-1) : ℂ)*z^2‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_neg hneg,norm_pow,hz]
    have hh := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ((1/2 : ℝ)^p))
    have hs := radius_scale_identity p
    nlinarith
  have hrem := archived_remainder_le hp hc hz.le
  have hid : (quadraticCoefficient c (p-1) : ℂ)*z^2 =
      ((quadraticMap c)^[p]) z - (criticalValue c p : ℂ) -
        quadraticRemainder c (p-1) z := by
    unfold quadraticRemainder
    rw [hp']
    ring
  have hnorm := norm_sub_le
    (((quadraticMap c)^[p]) z - (criticalValue c p : ℂ))
    (quadraticRemainder c (p-1) z)
  have hnorm' := norm_sub_le (((quadraticMap c)^[p]) z) (criticalValue c p : ℂ)
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hc.2.1] at hnorm'
  rw [← hid] at hnorm
  have hsmall := hc.2.2.1
  have hscale := scale_small hp
  linarith

/-- The entire archived physical target circle lies strictly outside
its own target under the complete p-return. -/
theorem archived_boundary_barrier {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : ‖z‖ = (1/2 : ℝ)^p) :
    (1/2 : ℝ)^p < ‖((quadraticMap c)^[p]) z‖ := by
  have hr : (1/2 : ℝ)^p ≤ (1/2 : ℝ)^17 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hp
  have h := archived_boundary_norm_lower hp hc hz
  norm_num at hr
  linarith

end
end ActualPairableSourceBounds
