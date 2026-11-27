import ActualCrestIntegral
import ActualCrestRadialOrder
import ActualCrestUpperGate

/-!
# Constructed actual terminal collars with their full radial limit

One parameter sequence, one family of actual crossings, and one endpoint
sequence satisfy all conclusions simultaneously. The complete two-sided
terminal gate is classified on the extended window. The radial coefficient
is the integral of actual crossing data; no conformal-width identification
or marked proper-path interpretation is asserted.
-/

namespace ActualCrestTheorem

open Set Function Filter
open scoped Topology
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn LimitingCrest
open LoopsLimitingCrestParameter ActualCrestCrossingWindow ActualCrestEndpoint
open CrestIntegralLimit

noncomputable section

/-- The opposite cut is inactive on the window, so the actual initial
component is also the exact component of the complete two-sided gate.
Strict radial order makes its endpoint the unique terminal root. -/
theorem complete_terminal_component {p : ℕ} {c r : ℝ} (F : Family p c)
    (hr : InitialCollar F r)
    (hanti : StrictAntiOn (terminal F) radiusInterval)
    (hupper : ∀ s ∈ radiusInterval,
      terminal F s < -(((normalizedReturn c p)^[4]) 0).re) :
    (∀ s ∈ radiusInterval, terminal F s = -1 ↔ s = r) ∧
    (∀ s ∈ radiusInterval,
      (-1 < terminal F s ∧
        terminal F s < -(((normalizedReturn c p)^[4]) 0).re) ↔ s < r) ∧
    connectedComponentIn
      (radiusInterval ∩ {s : ℝ | -1 < terminal F s ∧
        terminal F s < -(((normalizedReturn c p)^[4]) 0).re}) (1/16) =
      Ico (1/16) r := by
  have hrmem : r ∈ radiusInterval := ⟨hr.1.1.le, hr.1.2.le⟩
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    constructor
    · intro he
      exact hanti.injOn hs hrmem (he.trans hr.2.1.symm)
    · rintro rfl
      exact hr.2.1
  · intro s hs
    constructor
    · rintro ⟨hpos, _⟩
      by_contra h
      have hm := hanti.antitoneOn hrmem hs (le_of_not_gt h)
      rw [hr.2.1] at hm
      linarith
    · intro hlt
      refine ⟨?_, hupper s hs⟩
      have hm := hanti hs hrmem hlt
      rwa [hr.2.1] at hm
  · have hset :
        (radiusInterval ∩ {s : ℝ | -1 < terminal F s ∧
          terminal F s < -(((normalizedReturn c p)^[4]) 0).re}) =
        radiusInterval ∩ {s : ℝ | -1 < terminal F s} := by
      ext s
      constructor
      · rintro ⟨hs, hlo, _⟩
        exact ⟨hs, hlo⟩
      · rintro ⟨hs, hlo⟩
        exact ⟨hs, hlo, hupper s hs⟩
    rw [hset]
    exact hr.2.2.2

/-- Literal quadratic parameters and actual crossing curves realize a
unique complete terminal collar in the extended radius window. Its moving
endpoint converges, its full source-normalized radial coefficient converges
to a value strictly above one third, and all geometric support and exact
polynomial endpoint conclusions hold at one common eventual threshold.
Every object is constructed: there are no input hypotheses. -/
theorem exists_actual_complete_collars_and_limit :
    ∃ k₀ ∈ parameterInterval, relation k₀ = 0 ∧
      ∃ c : ℕ → ℝ, (∀ n, ActualTip (n+17) (c n)) ∧
        ∃ F : ∀ n, Family (n+17) (c n),
          ∃ r ∈ Ioo (663/10000 : ℝ) (133/2000), crestTerminal k₀ r = -1 ∧
            ∃ radii : ℕ → ℝ,
              (∀ n, radii n ∈ radiusInterval) ∧
              Tendsto radii atTop (𝓝 r) ∧
              Tendsto (fun n => radialCoefficient (n+17) (realAngle (F n)) (radii n))
                atTop (𝓝 (fullModelCoefficient k₀ r)) ∧
              (1/3 : ℝ) < fullModelCoefficient k₀ r ∧
              ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop,
                InitialCollar (F n) (radii n) ∧
                StrictAntiOn (terminal (F n)) radiusInterval ∧
                (∀ s ∈ radiusInterval,
                  terminal (F n) s = -1 ↔ s = radii n) ∧
                (∀ s ∈ radiusInterval,
                  (-1 < terminal (F n) s ∧ terminal (F n) s <
                    -(((normalizedReturn (c n) (n+17))^[4]) 0).re) ↔ s < radii n) ∧
                connectedComponentIn
                  (radiusInterval ∩ {s : ℝ | -1 < terminal (F n) s ∧
                    terminal (F n) s <
                      -(((normalizedReturn (c n) (n+17))^[4]) 0).re}) (1/16) =
                    Ico (1/16) (radii n) ∧
                (∀ s ∈ radiusInterval, terminal (F n) s+δ <
                  -(((normalizedReturn (c n) (n+17))^[4]) 0).re) ∧
                (∀ z ∈ initialDisk,
                  (∀ m ≤ 4, ‖((normalizedReturn (c n) (n+17))^[m]) z‖ ≤ 23/20) ∧
                    0 < (((normalizedReturn (c n) (n+17))^[2]) z).re ∧
                    (((normalizedReturn (c n) (n+17))^[3]) z).re < 0) ∧
                InjOn ((normalizedReturn (c n) (n+17))^[4])
                  {z : ℂ | z ∈ initialDisk ∧
                    0 < (normalizedReturn (c n) (n+17) z).re} ∧
                (∃ z : ℂ,
                  ‖z+((3*criticalValue (c n) (n+17)/4 : ℝ) : ℂ)‖ =
                    criticalValue (c n) (n+17)*radii n ∧
                  (((quadraticMap (c n))^[n+17]) z).re = 0 ∧
                  0 < (((quadraticMap (c n))^[n+17]) z).im ∧
                  ((quadraticMap (c n))^[3*(n+17)]) z =
                    -(criticalValue (c n) (n+17) : ℂ)) ∧
                (1/3 : ℝ) < radialCoefficient (n+17) (realAngle (F n)) (radii n) := by
  obtain ⟨k₀, hk₀, hroot, c, hc, F, r, hr, hterm, radii, hmem, hlimit,
      hcollars, hcoeff, hthird, hevent⟩ :=
    ActualCrestIntegral.exists_actual_initial_collars_and_positive_limit
  obtain ⟨δ, hδ, hupper⟩ :=
    ActualCrestUpperGate.actual_upper_gate_with_margin hk₀ hroot c hc F
  refine ⟨k₀, hk₀, hroot, c, hc, F, r, hr, hterm, radii, hmem, hlimit,
    hcoeff, hthird, δ, hδ, ?_⟩
  filter_upwards [hcollars, ActualCrestRadialOrder.actual_terminal_strictAnti c hc F,
    hupper, ActualCrestSupport.actual_support_bounds c hc,
    ActualCrestSupport.actual_selected_side_fourfold_injective c hc, hevent]
      with n hcollar hanti hup hsupport hinj hcoef
  have hcut : ∀ s ∈ radiusInterval, terminal (F n) s <
      -(((normalizedReturn (c n) (n+17))^[4]) 0).re := by
    intro s hs
    linarith [hup s hs]
  obtain ⟨hunique, hgate, hcomponent⟩ :=
    complete_terminal_component (F n) hcollar hanti hcut
  exact ⟨hcollar, hanti, hunique, hgate, hcomponent, hup, hsupport, hinj,
    unscaled_endpoint (by omega) (hc n) (F n) hcollar, hcoef⟩

end
end ActualCrestTheorem
