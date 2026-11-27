import ActualCrestEndpoint
import CrestIntegralLimit

/-!
# The moving-endpoint radial coefficient of actual quadratic returns

This integral is defined from the literal return's selected crossings
and its initial terminal-gate component. Its source normalization is
period dependent. It is not identified here with a marked extremal width.
-/

namespace ActualCrestIntegral

open Set Function Filter
open scoped Topology
open NearTwoTip NearTwoShooting LimitingCrest LoopsLimitingCrestParameter
open ActualCrestCrossingWindow ActualCrestEndpoint CrestIntegralLimit

noncomputable section

/-- Every admissible choice of actual parameters and crossing families
has convergent initial endpoints and convergent full radial coefficients.
The coefficients eventually exceed one third. -/
theorem actual_initial_coefficients_converge {k₀ : ℝ}
    (hk₀ : k₀ ∈ parameterInterval) (hroot : relation k₀ = 0)
    (c : ℕ → ℝ) (hc : ∀ n, ActualTip (n+17) (c n))
    (F : ∀ n, Family (n+17) (c n)) :
    ∃ r ∈ Ioo (663/10000 : ℝ) (133/2000), crestTerminal k₀ r = -1 ∧
      ∃ radii : ℕ → ℝ,
        (∀ n, radii n ∈ radiusInterval) ∧
        Tendsto radii atTop (𝓝 r) ∧
        (∀ᶠ n in atTop, InitialCollar (F n) (radii n)) ∧
        Tendsto (fun n => radialCoefficient (n+17) (realAngle (F n)) (radii n))
          atTop (𝓝 (fullModelCoefficient k₀ r)) ∧
        (1/3 : ℝ) < fullModelCoefficient k₀ r ∧
        ∀ᶠ n in atTop,
          (1/3 : ℝ) < radialCoefficient (n+17) (realAngle (F n)) (radii n) := by
  obtain ⟨r, hr, hterm, radii, hmem, hlimit, hcollars⟩ :=
    actual_initial_collars_converge hk₀ hroot c hc F
  have hangcont (n : ℕ) : ContinuousOn (realAngle (F n)) radiusInterval :=
    (realAngle_continuous (F n)).continuousOn
  have hangbound (n : ℕ) (s : ℝ) (_hs : s ∈ radiusInterval) :
      realAngle (F n) s ∈ Icc (-1/100 : ℝ) (1/100) :=
    ⟨((F n).angle_mem (radiusProjection s)).1.le,
      ((F n).angle_mem (radiusProjection s)).2.le⟩
  have hconv := actual_angles_tendsto hk₀ hroot c hc F
  have hrmem : r ∈ radiusInterval :=
    ⟨(by norm_num : (1/16 : ℝ) ≤ 663/10000).trans hr.1.le, hr.2.le⟩
  have hint := radialCoefficient_tendsto_fullModel hk₀ hangcont hangbound hconv
    hmem hrmem hlimit
  have hthird := fullModelCoefficient_gt_third hk₀
    (show r ∈ Icc (663/10000 : ℝ) (1/8) from
      ⟨hr.1.le, hr.2.le.trans (by norm_num)⟩)
  have hevent := radialCoefficient_eventually_gt_third hk₀ hangcont hangbound hconv
    hmem hrmem hr.1.le hlimit
  exact ⟨r, hr, hterm, radii, hmem, hlimit, hcollars, hint, hthird, hevent⟩

/-- An unconditional existence theorem for literal quadratic parameters,
their selected curves, maximal initial terminal components, and positive
limiting full radial coefficients. No approximation or parameter-existence
premise remains in this theorem. -/
theorem exists_actual_initial_collars_and_positive_limit :
    ∃ k₀ ∈ parameterInterval, relation k₀ = 0 ∧
      ∃ c : ℕ → ℝ, (∀ n, ActualTip (n+17) (c n)) ∧
        ∃ F : ∀ n, Family (n+17) (c n),
          ∃ r ∈ Ioo (663/10000 : ℝ) (133/2000), crestTerminal k₀ r = -1 ∧
            ∃ radii : ℕ → ℝ,
              (∀ n, radii n ∈ radiusInterval) ∧
              Tendsto radii atTop (𝓝 r) ∧
              (∀ᶠ n in atTop, InitialCollar (F n) (radii n)) ∧
              Tendsto (fun n => radialCoefficient (n+17) (realAngle (F n)) (radii n))
                atTop (𝓝 (fullModelCoefficient k₀ r)) ∧
              (1/3 : ℝ) < fullModelCoefficient k₀ r ∧
              ∀ᶠ n in atTop,
                (1/3 : ℝ) < radialCoefficient (n+17) (realAngle (F n)) (radii n) := by
  classical
  obtain ⟨k₀, ⟨hk₀, hroot⟩, _⟩ := exists_unique_limiting_parameter
  choose c hc using fun n : ℕ => exists_actual_tip (n+17) (by omega)
  let F (n : ℕ) : Family (n+17) (c n) :=
    Classical.choice (exists_family (by omega) (hc n))
  exact ⟨k₀, hk₀, hroot, c, hc, F,
    actual_initial_coefficients_converge hk₀ hroot c hc F⟩

end
end ActualCrestIntegral
