import ActualCrestEndpoint

/-!
# Persistence of the actual upper terminal gate

The moving fourth critical cut is evaluated in the same literal polynomial
return as the selected crossings. Its convergence and the uniform terminal
limit leave one positive margin on the complete extended radial window.
This proves the second terminal inequality; it assumes no symbolic marking
or conformal-width identification.
-/

namespace ActualCrestUpperGate

open Set Function Filter
open scoped Topology
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn LimitingCrest
open LoopsLimitingCrestParameter ActualCrestCrossingWindow ActualCrestEndpoint

noncomputable section

private theorem model_critical_cast (k : ℝ) (m : ℕ) :
    ((complexMap k)^[m]) (0 : ℂ) = (((realMap k)^[m]) (0 : ℝ) : ℂ) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [iterate_succ_apply', iterate_succ_apply', ih, complexMap_real]

/-- The actual fourth critical cut has an explicit error from the fixed
limiting quadratic. Every intermediate approximation-disk check is supplied
by the perturbation theorem, rather than imposed as a hypothesis. -/
theorem actual_fourth_cut_error {p : ℕ} (hp : 17 ≤ p) {c k₀ : ℝ}
    (hc : ActualTip p c) (hk₀ : k₀ ∈ parameterInterval) (hroot : relation k₀ = 0) :
    ‖((normalizedReturn c p)^[4]) 0-((complexMap k₀)^[4]) 0‖ ≤
      3688776*scale p := by
  have he : 0 ≤ 23646*scale p := mul_nonneg (by norm_num) (scale_pos p).le
  have hemax : 23646*scale p ≤ (1/500000 : ℝ) := by
    linarith [scale_small hp]
  have h := LimitingCrestPerturbation.quadratic_fourth_cut_error k₀
    (by linarith [hk₀.1]) (by linarith [hk₀.2])
    (normalizedReturn c p) (23646*scale p) he hemax
    (by
      intro w hw
      simpa only [complexMap] using
        ActualCrestLimit.actual_tip_limit_map_error hp hc hk₀ hroot hw)
  calc
    _ ≤ 156*(23646*scale p) := h.1
    _ = 3688776*scale p := by ring

/-- The moving cut is an actual fourth critical iterate, and converges to
the corresponding real critical iterate of the fixed limiting quadratic. -/
theorem actual_fourth_cut_tendsto {k₀ : ℝ} (hk₀ : k₀ ∈ parameterInterval)
    (hroot : relation k₀ = 0) (c : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n)) :
    Tendsto (fun n => (((normalizedReturn (c n) (n+17))^[4]) 0).re)
      atTop (𝓝 (((realMap k₀)^[4]) 0)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : ∀ᶠ n : ℕ in atTop, 3688776*scale (n+17) < ε :=
    (tendsto_order.mp (scale_tendsto_zero 3688776)).2 ε hε
  filter_upwards [he] with n hn
  have hbound := (Complex.abs_re_le_norm
    (((normalizedReturn (c n) (n+17))^[4]) 0-((complexMap k₀)^[4]) 0)).trans
    (actual_fourth_cut_error (by omega) (hc n) hk₀ hroot)
  rw [model_critical_cast] at hbound
  simpa only [Real.dist_eq, Complex.sub_re, Complex.ofReal_re] using
    hbound.trans_lt hn

/-- There is one strictly positive upper-gate margin for every selected
radius, uniformly for all sufficiently large periods. Actual terminal
monotonicity is not a premise. -/
theorem actual_upper_gate_with_margin {k₀ : ℝ} (hk₀ : k₀ ∈ parameterInterval)
    (hroot : relation k₀ = 0) (c : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n))
    (F : ∀ n, Family (n+17) (c n)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ s ∈ Icc (1/16 : ℝ) (133/2000),
        terminal (F n) s+δ < -(((normalizedReturn (c n) (n+17))^[4]) 0).re := by
  have ha : (1/16 : ℝ) ∈ Icc (1/16 : ℝ) (1/8) := by
    constructor <;> norm_num
  have hgap := crestTerminal_upper_gate hk₀ ha
  let δ : ℝ := (-((realMap k₀)^[4]) 0-crestTerminal k₀ (1/16))/4
  have hδ : 0 < δ := div_pos (sub_pos.mpr hgap) (by norm_num)
  have hδeq : 4*δ = -((realMap k₀)^[4]) 0-crestTerminal k₀ (1/16) := by
    dsimp [δ]
    ring
  refine ⟨δ,hδ,?_⟩
  filter_upwards
    [Metric.tendstoUniformlyOn_iff.mp (actual_terminal_tendsto hk₀ hroot c hc F) δ hδ,
      Metric.tendsto_nhds.mp (actual_fourth_cut_tendsto hk₀ hroot c hc) δ hδ]
      with n hn hcut
  intro s hs
  have hmodel := (crestTerminal_strictAnti hk₀).antitoneOn ha
    (show s ∈ Icc (1/16 : ℝ) (1/8) from ⟨hs.1,hs.2.trans (by norm_num)⟩) hs.1
  have hterminal := hn s hs
  rw [Real.dist_eq] at hterminal hcut
  linarith [(abs_lt.mp hterminal).1, (abs_lt.mp hterminal).2,
    (abs_lt.mp hcut).1, (abs_lt.mp hcut).2]

/-- The opposite actual terminal cut does not obstruct any radius in the
extended endpoint window once the period is sufficiently large. -/
theorem actual_upper_gate {k₀ : ℝ} (hk₀ : k₀ ∈ parameterInterval)
    (hroot : relation k₀ = 0) (c : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n))
    (F : ∀ n, Family (n+17) (c n)) :
    ∀ᶠ n : ℕ in atTop, ∀ s ∈ Icc (1/16 : ℝ) (133/2000),
      terminal (F n) s < -(((normalizedReturn (c n) (n+17))^[4]) 0).re := by
  obtain ⟨δ,hδ,hgate⟩ := actual_upper_gate_with_margin hk₀ hroot c hc F
  filter_upwards [hgate] with n hn
  intro s hs
  linarith [hn s hs]

end
end ActualCrestUpperGate
