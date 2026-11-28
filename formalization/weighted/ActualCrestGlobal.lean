import ActualCrestGlobalModel
import ActualCrestTheorem

/-!
# The exact terminal gate on the complete original circular parent

The gate is defined by existence of an arbitrary upper-semicircle point
whose literal quadratic return crosses the positive imaginary axis and
whose third return lies between both actual terminal cuts. It does not
refer to a preselected angular family or a clipped radius projection.

The complete gate set is one interval. This excludes extra angular roots
and all disconnected later radial components on the original parent.
-/

namespace ActualCrestGlobal

open Set Function Filter
open scoped Topology
open LimitingCrest NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn
open LoopsLimitingCrestParameter ActualCrestCrossingWindow ActualCrestEndpoint
open CrestIntegralLimit

noncomputable section

/-- The literal two-cut gate, with every upper-semicircle angle eligible. -/
def TerminalGate (p : ℕ) (c s : ℝ) : Prop :=
  ∃ u ∈ Icc (-1 : ℝ) 1,
    (normalizedReturn c p (circlePoint s u)).re = 0 ∧
    0 < (normalizedReturn c p (circlePoint s u)).im ∧
    -1 < (((normalizedReturn c p)^[3]) (circlePoint s u)).re ∧
    (((normalizedReturn c p)^[3]) (circlePoint s u)).re <
      -(((normalizedReturn c p)^[4]) 0).re

/-- On the original short window, the existential gate agrees with the
selected terminal function because every actual semicircle crossing is
unique. This rules out an unnoticed angular branch. -/
theorem terminalGate_iff_selected {p : ℕ} (hp : 17 ≤ p) {c s : ℝ}
    (hc : ActualTip p c) (F : Family p c) (hs : s ∈ radiusInterval) :
    TerminalGate p c s ↔
      (-1 < terminal F s ∧
        terminal F s < -(((normalizedReturn c p)^[4]) 0).re) := by
  let ss : Radius := ⟨s,hs⟩
  have ha : F.angle ss ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [(F.angle_mem ss).1,(F.angle_mem ss).2]
  have ht : terminal F s =
      (((normalizedReturn c p)^[3]) (circlePoint s (F.angle ss))).re := by
    simp only [terminal,point,radiusProjection_eq hs,Family.point]
    rfl
  constructor
  · rintro ⟨u,hu,hzero,_,hlo,hhi⟩
    have he := actual_full_crossing_unique hp hc hs hu ha hzero (F.crossing ss)
    subst u
    rw [ht]
    exact ⟨hlo,hhi⟩
  · rintro ⟨hlo,hhi⟩
    rw [ht] at hlo hhi
    exact ⟨F.angle ss,ha,F.crossing ss,F.positive ss,hlo,hhi⟩

/-- One full-parent exclusion and the certified short-window endpoint
give the exact complete gate, not only its initial connected component. -/
theorem terminalGate_iff_below_endpoint {p : ℕ} (hp : 17 ≤ p) {c r : ℝ}
    (hc : ActualTip p c) (F : Family p c) (hr : InitialCollar F r)
    (hanti : StrictAntiOn (terminal F) radiusInterval)
    (hupper : ∀ s ∈ radiusInterval,
      terminal F s < -(((normalizedReturn c p)^[4]) 0).re)
    (htail : ∀ s ∈ Icc (133/2000 : ℝ) (1/8), ∀ u ∈ Icc (-1 : ℝ) 1,
      (normalizedReturn c p (circlePoint s u)).re = 0 →
        (((normalizedReturn c p)^[3]) (circlePoint s u)).re < -1) :
    ∀ s ∈ Icc (1/16 : ℝ) (1/8), TerminalGate p c s ↔ s < r := by
  have hlocal := (ActualCrestTheorem.complete_terminal_component F hr hanti hupper).2.1
  intro s hs
  by_cases hshort : s ≤ 133/2000
  · have hs' : s ∈ radiusInterval := ⟨hs.1,hshort⟩
    exact (terminalGate_iff_selected hp hc F hs').trans (hlocal s hs')
  · have hsr : r < s := hr.1.2.trans (lt_of_not_ge hshort)
    constructor
    · rintro ⟨u,hu,hzero,_,hlo,_⟩
      have hlate := htail s ⟨(lt_of_not_ge hshort).le,hs.2⟩ u hu hzero
      linarith
    · intro h
      exact False.elim ((not_lt_of_gt hsr) h)

/-- The original parent cutoff exceeds the entire endpoint window at
every period under consideration. -/
theorem original_parent_cutoff {p : ℕ} (hp : 17 ≤ p) :
    (133/2000 : ℝ) < ((p : ℝ)-1)/(8*(p : ℝ)) ∧
      ((p : ℝ)-1)/(8*(p : ℝ)) < 1/8 := by
  have hp' : (17 : ℝ) ≤ p := by exact_mod_cast hp
  have hpos : 0 < 8*(p : ℝ) :=
    mul_pos (by norm_num) (lt_of_lt_of_le (by norm_num) hp')
  constructor
  · apply (lt_div_iff₀ hpos).mpr
    nlinarith
  · apply (div_lt_iff₀ hpos).mpr
    nlinarith

/-- Once the terminal gate is classified on the full radius range,
its part in the open original parent is exactly the open maximal collar. -/
theorem original_parent_gate_set {p : ℕ} (hp : 17 ≤ p) {c r : ℝ}
    (hr : r < (133/2000 : ℝ))
    (hgate : ∀ s ∈ Icc (1/16 : ℝ) (1/8), TerminalGate p c s ↔ s < r) :
    {s : ℝ | 1/16 < s ∧ s < ((p : ℝ)-1)/(8*(p : ℝ)) ∧
      TerminalGate p c s} = Ioo (1/16) r := by
  obtain ⟨hcutlo, hcutup⟩ := original_parent_cutoff hp
  ext s
  constructor
  · rintro ⟨hlo,hcut,hg⟩
    exact ⟨hlo,(hgate s ⟨hlo.le,(hcut.trans hcutup).le⟩).mp hg⟩
  · rintro ⟨hlo,hsr⟩
    have hcut := hsr.trans (hr.trans hcutlo)
    exact ⟨hlo,hcut,(hgate s ⟨hlo.le,(hcut.trans hcutup).le⟩).mpr hsr⟩

/-- Every selection of the actual tip parameters has one complete
terminal collar on the original parent. The entire gate set, rather than
a presumed component, has the convergent endpoint and radial coefficient.
The eventual threshold is independent of radius and angle. -/
theorem actual_original_parent_collars {κ : ℝ}
    (hk : κ ∈ parameterInterval) (hroot : relation κ = 0)
    (c : ℕ → ℝ) (hc : ∀ n, ActualTip (n+17) (c n))
    (F : ∀ n, Family (n+17) (c n)) :
    ∃ r ∈ Ioo (663/10000 : ℝ) (133/2000), crestTerminal κ r = -1 ∧
      ∃ radii : ℕ → ℝ,
        (∀ n, radii n ∈ radiusInterval) ∧
        Tendsto radii atTop (𝓝 r) ∧
        Tendsto (fun n => radialCoefficient (n+17) (realAngle (F n)) (radii n))
          atTop (𝓝 (fullModelCoefficient κ r)) ∧
        (1/3 : ℝ) < fullModelCoefficient κ r ∧
        ∀ᶠ n in atTop,
          InitialCollar (F n) (radii n) ∧
          (∀ s ∈ Icc (1/16 : ℝ) (1/8),
            TerminalGate (n+17) (c n) s ↔ s < radii n) ∧
          {s : ℝ | 1/16 < s ∧
            s < (((n+17 : ℕ) : ℝ)-1)/(8*((n+17 : ℕ) : ℝ)) ∧
            TerminalGate (n+17) (c n) s} = Ioo (1/16) (radii n) := by
  obtain ⟨r,hr,hterm,radii,hmem,hlim,hcollars,hcoef,hthird,_⟩ :=
    ActualCrestIntegral.actual_initial_coefficients_converge hk hroot c hc F
  obtain ⟨δ,hδ,hupper⟩ :=
    ActualCrestUpperGate.actual_upper_gate_with_margin hk hroot c hc F
  refine ⟨r,hr,hterm,radii,hmem,hlim,hcoef,hthird,?_⟩
  filter_upwards [hcollars, ActualCrestRadialOrder.actual_terminal_strictAnti c hc F,
    hupper, ActualCrestGlobalModel.eventually_all_actual_tips_no_reentry]
    with n hn hanti hup htail
  have hu : ∀ s ∈ radiusInterval, terminal (F n) s <
      -(((normalizedReturn (c n) (n+17))^[4]) 0).re := by
    intro s hs
    linarith [hup s hs]
  have hgate := terminalGate_iff_below_endpoint (by omega) (hc n) (F n)
    hn hanti hu (htail (c n) (hc n))
  exact ⟨hn,hgate,original_parent_gate_set (by omega) hn.1.2 hgate⟩

/-- Actual parameters and crossing families are constructed. The complete
original-parent terminal gate is a single interval with convergent endpoint;
no geometric or existence premise is supplied by the caller. -/
theorem exists_actual_original_parent_collars :
    ∃ c : ℕ → ℝ, (∀ n, ActualTip (n+17) (c n)) ∧
      ∃ radii : ℕ → ℝ, ∃ r ∈ Ioo (663/10000 : ℝ) (133/2000),
        Tendsto radii atTop (𝓝 r) ∧
        ∀ᶠ n in atTop,
          (1/16 : ℝ) < radii n ∧ radii n < 133/2000 ∧
          (∀ s ∈ Icc (1/16 : ℝ) (1/8),
            TerminalGate (n+17) (c n) s ↔ s < radii n) ∧
          {s : ℝ | 1/16 < s ∧
            s < (((n+17 : ℕ) : ℝ)-1)/(8*((n+17 : ℕ) : ℝ)) ∧
            TerminalGate (n+17) (c n) s} = Ioo (1/16) (radii n) := by
  classical
  obtain ⟨κ,⟨hk,hroot⟩,_⟩ := exists_unique_limiting_parameter
  choose c hc using fun n : ℕ => exists_actual_tip (n+17) (by omega)
  let F : ∀ n, Family (n+17) (c n) := fun n =>
    Classical.choice (exists_family (by omega) (hc n))
  obtain ⟨r,hr,_,radii,_,hlim,_,_,hevent⟩ :=
    actual_original_parent_collars hk hroot c hc F
  refine ⟨c,hc,radii,r,hr,hlim,?_⟩
  filter_upwards [hevent] with n hn
  exact ⟨hn.1.1.1,hn.1.1.2,hn.2.1,hn.2.2⟩

end
end ActualCrestGlobal
