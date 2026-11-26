import QuadraticCenterMultiplier
import QuadraticMultiplierIteration
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# Multiplier parameter coordinates at every exact-period quadratic center

Both the periodic motion and the inverse parameter coordinate are constructed.
The same coordinate puts every repeated-return multiplier in the exact form
t ↦ t^k. All inverse and dynamical identities have their local scope stated.
-/

namespace LoopsQuadraticCenterMultiplier

open Filter
open scoped Topology
open LoopsQuadraticTransversality

noncomputable section

/-- The explicit parameter derivative of the first-return multiplier. -/
def centerMultiplierSlope (c : ℂ) (n : ℕ) : ℂ :=
  2 * slope c (n+1) * returnMultiplier c c n

private theorem critical_return (c : ℂ) (n : ℕ) :
    returnOrbit c 0 n = orbit c n := by
  simpa only [orbit, Nat.zero_add] using (returnOrbit_orbit c 0 n)

private theorem analytic_inverse_zero (f : ℂ → ℂ) (c d : ℂ)
    (hf : AnalyticAt ℂ f c) (hzero : f c = 0)
    (hd : HasDerivAt f d c) (hne : d ≠ 0) :
    ∃ ψ : ℂ → ℂ, ψ 0 = c ∧ AnalyticAt ℂ ψ 0 ∧ HasDerivAt ψ d⁻¹ 0 ∧
      (∀ᶠ w in 𝓝 c, ψ (f w) = w) ∧
      (∀ᶠ t in 𝓝 (0 : ℂ), f (ψ t) = t) := by
  have hderiv : deriv f c ≠ 0 := by rwa [hd.deriv]
  let ψ := hf.hasStrictDerivAt.localInverse f (deriv f c) c hderiv
  have hleft : ∀ᶠ w in 𝓝 c, ψ (f w) = w :=
    HasStrictDerivAt.eventually_left_inverse ..
  have hright : ∀ᶠ t in 𝓝 (f c), f (ψ t) = t :=
    HasStrictDerivAt.eventually_right_inverse ..
  have hinv : HasDerivAt ψ (deriv f c)⁻¹ (f c) :=
    (hf.hasStrictDerivAt.to_localInverse hderiv).hasDerivAt
  refine ⟨ψ, ?_, ?_, ?_, hleft, ?_⟩
  · simpa only [hzero] using hleft.self_of_nhds
  · simpa only [hzero] using hf.analyticAt_localInverse hderiv
  · simpa only [hzero, hd.deriv] using hinv
  · simpa only [hzero] using hright

/-- At every exact-period quadratic center, construct a single analytic
motion with its exact tangent and a nonzero multiplier parameter derivative.
That same motion has the original exact period and is attracting nearby. -/
theorem center_multiplier_motion (c : ℂ) (n : ℕ)
    (hreturn : orbit c (n+1) = 0)
    (hmin : ∀ k : ℕ, 0 < k → k < n+1 → orbit c k ≠ 0) :
    ∃ ζ : ℂ → ℂ,
      ζ c = 0 ∧ AnalyticAt ℂ ζ c ∧ HasDerivAt ζ (slope c (n+1)) c ∧
      AnalyticAt ℂ (fun w => returnMultiplier w (ζ w) (n+1)) c ∧
      HasDerivAt (fun w => returnMultiplier w (ζ w) (n+1))
        (centerMultiplierSlope c n) c ∧ centerMultiplierSlope c n ≠ 0 ∧
      ∀ᶠ w in 𝓝 c,
        returnOrbit w (ζ w) (n+1) = ζ w ∧
        Function.minimalPeriod (fun z : ℂ => z^2+w) (ζ w) = n+1 ∧
        ‖returnMultiplier w (ζ w) (n+1)‖ < 1 := by
  have hper : returnOrbit c 0 (n+1) = 0 :=
    (critical_return c (n+1)).trans hreturn
  have hshort : ∀ k : ℕ, 0 < k → k < n+1 → returnOrbit c 0 k ≠ 0 := by
    intro k hk hkn
    rw [critical_return]
    exact hmin k hk hkn
  have hmult : returnMultiplier c 0 (n+1) ≠ 1 := by
    rw [returnMultiplier_zero_start]
    exact zero_ne_one
  obtain ⟨ζ, hself, han, hμan, hstable⟩ :=
    periodic_point_exact_period_stability c 0 (n+1) (by omega) hper hshort hmult
  have hret : (fun w : ℂ => returnOrbit w (ζ w) (n+1)) =ᶠ[𝓝 c] ζ := by
    filter_upwards [hstable] with w hw
    have hp := Function.isPeriodicPt_minimalPeriod (fun z : ℂ => z^2+w) (ζ w)
    rw [hw.1] at hp
    simpa only [returnOrbit_eq_iterate, Function.IsPeriodicPt, Function.IsFixedPt] using hp
  have hd := moving_center_hasDerivAt c n ζ han hself hret
  have hμd := moving_center_multiplier_hasDerivAt c n ζ _ hd hself
  refine ⟨ζ, hself, han, hd, hμan, hμd,
    center_multiplier_derivative_ne_zero c n hreturn hmin, ?_⟩
  filter_upwards [hret, hstable] with w hw hs
  exact ⟨hw, hs.1, hs.2.1 (by rw [returnMultiplier_zero_start]; norm_num)⟩

/-- The actual first-return multiplier is a local analytic parameter
coordinate at every exact-period center. Its constructed inverse realizes
all sufficiently small multiplier values on the same attracting exact-period
cycle. Simultaneously, the genuine spatial derivative at every repeated
return becomes exactly t^k in this coordinate. -/
theorem center_multiplier_parameter_coordinate (c : ℂ) (n : ℕ)
    (hreturn : orbit c (n+1) = 0)
    (hmin : ∀ k : ℕ, 0 < k → k < n+1 → orbit c k ≠ 0) :
    ∃ ζ ψ : ℂ → ℂ,
      ζ c = 0 ∧ AnalyticAt ℂ ζ c ∧
      AnalyticAt ℂ (fun w => returnMultiplier w (ζ w) (n+1)) c ∧
      HasDerivAt (fun w => returnMultiplier w (ζ w) (n+1))
        (centerMultiplierSlope c n) c ∧ centerMultiplierSlope c n ≠ 0 ∧
      ψ 0 = c ∧ AnalyticAt ℂ ψ 0 ∧
      HasDerivAt ψ (centerMultiplierSlope c n)⁻¹ 0 ∧
      (∀ᶠ w in 𝓝 c,
        ψ (returnMultiplier w (ζ w) (n+1)) = w ∧
        (returnMultiplier w (ζ w) (n+1) = 0 ↔ w = c)) ∧
      (∀ᶠ w in 𝓝 c,
        returnOrbit w (ζ w) (n+1) = ζ w ∧
        Function.minimalPeriod (fun z : ℂ => z^2+w) (ζ w) = n+1 ∧
        ‖returnMultiplier w (ζ w) (n+1)‖ < 1) ∧
      (∀ k : ℕ,
        analyticOrderAt (fun w => returnMultiplier w (ζ w) ((n+1)*k)) c = (k : ℕ∞)) ∧
      (∀ᶠ t in 𝓝 (0 : ℂ),
        returnMultiplier (ψ t) (ζ (ψ t)) (n+1) = t ∧
        returnOrbit (ψ t) (ζ (ψ t)) (n+1) = ζ (ψ t) ∧
        Function.minimalPeriod (fun z : ℂ => z^2+ψ t) (ζ (ψ t)) = n+1 ∧
        ‖t‖ < 1 ∧
        ∀ k : ℕ,
          deriv ((fun z : ℂ => z^2+ψ t)^[(n+1)*k]) (ζ (ψ t)) = t^k) := by
  obtain ⟨ζ, hself, han, _, hμan, hμd, hD, hstable⟩ :=
    center_multiplier_motion c n hreturn hmin
  let μ : ℂ → ℂ := fun w => returnMultiplier w (ζ w) (n+1)
  have hμzero : μ c = 0 := by
    dsimp only [μ]
    rw [hself, returnMultiplier_zero_start]
  obtain ⟨ψ, hψzero, hψan, hψd, hleft, hright⟩ :=
    analytic_inverse_zero μ c (centerMultiplierSlope c n) hμan hμzero hμd hD
  have hψlim : Tendsto ψ (𝓝 (0 : ℂ)) (𝓝 c) := by
    simpa only [hψzero] using hψan.continuousAt.tendsto
  refine ⟨ζ, ψ, hself, han, hμan, hμd, hD, hψzero, hψan, hψd,
    ?_, hstable, ?_, ?_⟩
  · filter_upwards [hleft] with w hw
    refine ⟨hw, ?_⟩
    change μ w = 0 ↔ w = c
    constructor
    · intro hz
      rw [hz, hψzero] at hw
      exact hw.symm
    · intro hwc
      subst w
      exact hμzero
  · intro k
    apply periodic_motion_returnMultiplier_order c ζ (n+1) k han
      (hstable.mono (fun w hw => hw.1)) hμzero
    rwa [hμd.deriv]
  · filter_upwards [hright, hψlim.eventually hstable] with t ht hs
    have hval : returnMultiplier (ψ t) (ζ (ψ t)) (n+1) = t := ht
    refine ⟨hval, hs.1, hs.2.1, ?_, ?_⟩
    · simpa only [hval] using hs.2.2
    · intro k
      have hd := (returnMultiplier_hasDerivAt (ψ t) (ζ (ψ t)) ((n+1)*k)).deriv
      simp only [returnOrbit_eq_iterate] at hd
      rw [hd, periodic_returnMultiplier_mul (ψ t) (ζ (ψ t)) (n+1) k hs.1, hval]

end
end LoopsQuadraticCenterMultiplier
