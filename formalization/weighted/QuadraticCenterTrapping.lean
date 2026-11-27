import QuadraticCenterMultiplier
import QuadraticCollisionFactorization

/-!
# Uniform actual return trapping near quadratic centers

A positive critical return has zero spatial derivative at the critical
point. The exact secant factor and joint continuity produce one closed
disk mapped strictly into itself by that return for all nearby parameters.
No minimal-period or attracting-basin theorem is assumed.
-/

namespace LoopsQuadraticCenterMultiplier

open Filter
open scoped Topology
open LoopsQuadraticTransversality

noncomputable section

/-- The actual critical return plus its exact spatial secant remainder. -/
theorem returnOrbit_critical_secant (c z : ℂ) (p : ℕ) :
    returnOrbit c z p = orbit c p + z * returnSecant c z 0 p := by
  have h := returnOrbit_sub_secant c z 0 p
  have hzero : returnOrbit c 0 p = orbit c p := by
    simpa only [orbit, Nat.zero_add] using (returnOrbit_orbit c 0 p)
  rw [hzero, sub_zero] at h
  linear_combination h

/-- Every positive critical return supplies one actual trapping disk for
all sufficiently nearby complex parameters. The return time need not be
the minimal critical period. -/
theorem center_uniform_return_trapping (c : ℂ) (n : ℕ)
    (hreturn : orbit c (n+1) = 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ d in 𝓝 c,
      ∀ z : ℂ, ‖z‖ ≤ r → ‖returnOrbit d z (n+1)‖ < r := by
  have hpath : Continuous (fun v : ℂ × ℂ => (v.1, v.2, (0 : ℂ))) := by
    fun_prop
  have hScont : ContinuousAt
      (fun v : ℂ × ℂ => returnSecant v.1 v.2 0 (n+1)) (c,0) :=
    ((returnSecant_contDiff (n+1)).continuous.comp hpath).continuousAt
  have hSzero : returnSecant c 0 0 (n+1) = 0 := by
    rw [returnSecant_diagonal, returnMultiplier_zero_start]
  have hSsmall : ∀ᶠ v : ℂ × ℂ in 𝓝 (c,0),
      ‖returnSecant v.1 v.2 0 (n+1)‖ < (1 : ℝ)/2 :=
    hScont.norm.tendsto.eventually_lt_const (by rw [hSzero, norm_zero]; norm_num)
  obtain ⟨ε, hε, hεS⟩ := Metric.eventually_nhds_iff.mp hSsmall
  let r : ℝ := ε/2
  have hr : 0 < r := div_pos hε (by norm_num)
  have hparam : ∀ᶠ d in 𝓝 c, dist d c < ε := Metric.ball_mem_nhds c hε
  have hPsmall : ∀ᶠ d in 𝓝 c, ‖orbit d (n+1)‖ < r/2 :=
    (orbit_hasDerivAt (n+1) c).continuousAt.norm.tendsto.eventually_lt_const
      (by rw [hreturn, norm_zero]; exact div_pos hr (by norm_num))
  refine ⟨r, hr, ?_⟩
  filter_upwards [hparam, hPsmall] with d hd hPd
  intro z hz
  have hzε : dist z (0 : ℂ) < ε := by
    rw [dist_zero_right]
    dsimp only [r] at hz
    linarith
  have hpair : dist ((d,z) : ℂ × ℂ) (c,0) < ε := by
    rw [Prod.dist_eq]
    exact max_lt hd hzε
  have hSd : ‖returnSecant d z 0 (n+1)‖ < (1 : ℝ)/2 := hεS hpair
  rw [returnOrbit_critical_secant]
  calc
    ‖orbit d (n+1) + z * returnSecant d z 0 (n+1)‖ ≤
        ‖orbit d (n+1)‖ + ‖z * returnSecant d z 0 (n+1)‖ := norm_add_le _ _
    _ = ‖orbit d (n+1)‖ + ‖z‖ * ‖returnSecant d z 0 (n+1)‖ := by
      rw [norm_mul]
    _ ≤ ‖orbit d (n+1)‖ + r*((1 : ℝ)/2) :=
      add_le_add le_rfl (mul_le_mul hz hSd.le (norm_nonneg _) hr.le)
    _ < r := by linarith

end
end LoopsQuadraticCenterMultiplier
