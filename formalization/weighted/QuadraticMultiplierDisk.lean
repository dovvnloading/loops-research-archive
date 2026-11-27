import QuadraticMultiplierCoordinate
import QuadraticCenterParameterLocus

/-!
# An open disk of realized multipliers at every quadratic center

The parameter and periodic point vary analytically throughout a nonempty
open multiplier disk. The parameter map is injective there, and its image
has zero actual parameter escape. Every marked periodic point has the
prescribed exact period and actual multiplier.
-/

namespace LoopsQuadraticCenterMultiplier

open Filter
open scoped Topology
open LoopsQuadraticTransversality

noncomputable section

/-- A concrete holomorphic family over an open multiplier disk at every
exact-period center. The parameter map is injective, both maps are analytic
throughout the disk, all realized parameters have zero actual escape,
and the spatial derivatives of all repeated returns are exact powers of
the disk coordinate. -/
theorem center_multiplier_disk (c : ℂ) (n : ℕ)
    (hreturn : orbit c (n+1) = 0)
    (hmin : ∀ k : ℕ, 0 < k → k < n+1 → orbit c k ≠ 0) :
    ∃ ψ ξ : ℂ → ℂ, ∃ r : ℝ,
      0 < r ∧ ψ 0 = c ∧ ξ 0 = 0 ∧
      HasDerivAt ψ (centerMultiplierSlope c n)⁻¹ 0 ∧
      AnalyticOnNhd ℂ ψ (Metric.ball 0 r) ∧
      AnalyticOnNhd ℂ ξ (Metric.ball 0 r) ∧
      Set.InjOn ψ (Metric.ball 0 r) ∧
      ∀ t ∈ Metric.ball (0 : ℂ) r,
        QuadraticEscape.parameterEscape (ψ t) = 0 ∧
        returnMultiplier (ψ t) (ξ t) (n+1) = t ∧
        returnOrbit (ψ t) (ξ t) (n+1) = ξ t ∧
        Function.minimalPeriod (fun z : ℂ => z^2+ψ t) (ξ t) = n+1 ∧
        ‖t‖ < 1 ∧
        ∀ k : ℕ,
          deriv ((fun z : ℂ => z^2+ψ t)^[(n+1)*k]) (ξ t) = t^k := by
  obtain ⟨ζ, ψ, hself, han, _, _, _, hψzero, hψan, hψd, _, _, _, hfinal⟩ :=
    center_multiplier_parameter_coordinate c n hreturn hmin
  have hψlim : Tendsto ψ (𝓝 (0 : ℂ)) (𝓝 c) := by
    simpa only [hψzero] using hψan.continuousAt.tendsto
  have hreal := hψlim.eventually (center_parameter_escape_zero c n hreturn)
  have hall := hψan.eventually_analyticAt.and
    ((hψlim.eventually han.eventually_analyticAt).and (hreal.and hfinal))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hall
  let ξ : ℂ → ℂ := fun t => ζ (ψ t)
  refine ⟨ψ, ξ, r, hr, hψzero, ?_, hψd, ?_, ?_, ?_, ?_⟩
  · dsimp only [ξ]
    rw [hψzero, hself]
  · intro t ht
    exact (hball t ht).1
  · intro t ht
    exact (hball t ht).2.1.comp (hball t ht).1
  · intro s hs t ht heq
    have hvs := (hball s hs).2.2.2.1
    have hvt := (hball t ht).2.2.2.1
    rw [heq] at hvs
    exact hvs.symm.trans hvt
  · intro t ht
    exact (hball t ht).2.2

end
end LoopsQuadraticCenterMultiplier
