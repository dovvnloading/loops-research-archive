import ActualPairableConvergence
import ActualPairableLimitModel

/-!
# Actual pairable optima converge to the attained limiting optimum

Both endpoints of the convergence statement are literal complete
geometric pairable suprema, and both have explicitly constructed
maximizing Waves. No convergence of maximizers is assumed or asserted.
-/

namespace ActualPairableLimit

open Set Filter NearTwoTip LoopsLimitingCrestParameter
open ActualPairableMarking ActualPairableLimitModel
open scoped Topology ENNReal
noncomputable section

/-- Every sequence of actual quadratic tips has the same complete
geometric pairable limit, equal to the maximum on the full limiting
domain with its literal limiting physical source ports. -/
theorem pairable_optimum_converges {k : ℝ} (hk : k ∈ parameterInterval)
    (hroot : relation k = 0) (c : ℕ → ℝ) (hc : ∀ n, ActualTip (n+17) (c n)) :
    Tendsto (fun n => pairableWidth (by omega : 17 ≤ n+17) (hc n)) atTop
      (𝓝 (limitingPairableWidth k hk)) := by
  rw [limitingPairableWidth_eq_period_ratio hk]
  exact ActualPairableConvergence.pairableWidth_tendsto hk hroot c hc

theorem pairable_optimum_real_converges {k : ℝ} (hk : k ∈ parameterInterval)
    (hroot : relation k = 0) (c : ℕ → ℝ) (hc : ∀ n, ActualTip (n+17) (c n)) :
    Tendsto (fun n => (pairableWidth (by omega : 17 ≤ n+17) (hc n)).toReal) atTop
      (𝓝 (limitingPairableWidth k hk).toReal) :=
  (ENNReal.tendsto_toReal (limitingPairableWidth_ne_top hk)).comp
    (pairable_optimum_converges hk hroot c hc)

end
end ActualPairableLimit
