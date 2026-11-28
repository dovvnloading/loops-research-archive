import GlobalCrestOrder
import GlobalCrestEndpointValues
import GlobalCrestSourceGates
import CrestFirstExit

/-!
# Complete actual terminal-gate classification

For every return index at least seventeen, the actual full parent has one
terminal component and one endpoint. The endpoint is constructed by the
literal polynomial, and all later candidate radii are excluded.
-/

namespace GlobalCrestClassification

open Set Function
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn LimitingCrest
open GlobalCrestCrossing GlobalCrestOrder GlobalCrestEndpointValues

noncomputable section

def terminalGate {p : ℕ} {c : ℝ} (F : Family p c) (s : ℝ) : Prop :=
  -1 < terminal F s ∧
    terminal F s < -(((normalizedReturn c p)^[4]) 0).re

/-- The complete actual terminal coordinate is strictly decreasing on
the entire parent range, for every p at least seventeen. -/
theorem actual_terminal_strictAnti {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (F : Family p c) :
    StrictAntiOn (terminal F) (Icc (1/16 : ℝ) (1/8)) := by
  have hs := actual_endpoint_signs hp hc F
  rcases ContinuousOn.strictMonoOn_of_injOn_Icc'
    (by norm_num : (1/16 : ℝ) ≤ 1/8)
    (terminal_continuous F).continuousOn
    (actual_terminal_injective hp hc F) with hmono | hanti
  · have h := hmono
      (show (663/10000 : ℝ) ∈ Icc (1/16 : ℝ) (1/8) by constructor <;> norm_num)
      (show (133/2000 : ℝ) ∈ Icc (1/16 : ℝ) (1/8) by constructor <;> norm_num)
      (by norm_num : (663/10000 : ℝ) < 133/2000)
    linarith [hs.1,hs.2]
  · exact hanti

/-- The opposite terminal cut is inactive on the entire actual parent,
not only before the endpoint or at sufficiently late periods. -/
theorem actual_upper_gate {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (F : Family p c) :
    ∀ s ∈ Icc (1/16 : ℝ) (1/8),
      terminal F s < -(((normalizedReturn c p)^[4]) 0).re := by
  intro s hs
  have h := (actual_terminal_strictAnti hp hc F).antitoneOn
    (show (1/16 : ℝ) ∈ Icc (1/16 : ℝ) (1/8) by constructor <;> norm_num) hs hs.1
  exact h.trans_lt (actual_initial_upper_gate hp hc F)

/-- The entire two-sided terminal gate is one interval. This is a set
equality, so it excludes every later component and isolated reentry. -/
theorem actual_full_gate_classification {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (F : Family p c) :
    ∃ r ∈ Ioo (663/10000 : ℝ) (133/2000),
      terminal F r = -1 ∧
      (∀ s ∈ Icc (1/16 : ℝ) (1/8), terminal F s = -1 ↔ s = r) ∧
      (∀ s ∈ Icc (1/16 : ℝ) (1/8), terminalGate F s ↔ s < r) ∧
      Icc (1/16 : ℝ) (1/8) ∩ {s | terminalGate F s} = Ico (1/16) r := by
  have hsign := actual_endpoint_signs hp hc F
  obtain ⟨r,hr,hzero⟩ := intermediate_value_Icc'
    (by norm_num : (663/10000 : ℝ) ≤ 133/2000)
    (terminal_continuous F).continuousOn
    (show (-1 : ℝ) ∈ Icc (terminal F (133/2000)) (terminal F (663/10000)) from
      ⟨hsign.2.le,hsign.1.le⟩)
  have hri : r ∈ Ioo (663/10000 : ℝ) (133/2000) := by
    constructor
    · by_contra h
      have he : r = 663/10000 := by linarith [hr.1]
      rw [he] at hzero
      linarith [hsign.1]
    · by_contra h
      have he : r = 133/2000 := by linarith [hr.2]
      rw [he] at hzero
      linarith [hsign.2]
  have hrmem : r ∈ Icc (1/16 : ℝ) (1/8) := by
    constructor <;> linarith [hr.1,hr.2]
  have hanti := actual_terminal_strictAnti hp hc F
  have hgate : ∀ s ∈ Icc (1/16 : ℝ) (1/8), terminalGate F s ↔ s < r := by
    intro s hs
    constructor
    · intro hg
      by_contra h
      have hm := hanti.antitoneOn hrmem hs (le_of_not_gt h)
      rw [hzero] at hm
      linarith [hg.1]
    · intro hlt
      refine ⟨?_,actual_upper_gate hp hc F s hs⟩
      have h := hanti hs hrmem hlt
      rwa [hzero] at h
  refine ⟨r,hri,hzero,?_,hgate,?_⟩
  · intro s hs
    constructor
    · intro he
      exact hanti.injOn hs hrmem (he.trans hzero.symm)
    · rintro rfl
      exact hzero
  · ext s
    constructor
    · rintro ⟨hs,hg⟩
      exact ⟨hs.1,(hgate s hs).mp hg⟩
    · intro hs
      have hsfull : s ∈ Icc (1/16 : ℝ) (1/8) :=
        ⟨hs.1,hs.2.le.trans hrmem.2⟩
      exact ⟨hsfull,(hgate s hsfull).mpr hs.2⟩

/-- The original source outer radius, retaining its period dependence. -/
def parentOuter (p : ℕ) : ℝ := ((p : ℝ)-1)/(8*(p : ℝ))

theorem parentOuter_bounds {p : ℕ} (hp : 17 ≤ p) :
    (133/2000 : ℝ) < parentOuter p ∧ parentOuter p ≤ 1/8 := by
  have hp' : (17 : ℝ) ≤ p := by exact_mod_cast hp
  have hden : 0 < 8*(p : ℝ) := by positivity
  constructor
  · apply (lt_div_iff₀ hden).mpr
    linarith
  · apply (div_le_iff₀ hden).mpr
    linarith

/-- All literal q/w endpoint tests hold throughout the retained
terminal interval. Adding them leaves the complete admissible set
unchanged; their possible failure farther out cannot create a component. -/
theorem actual_complete_parent_classification {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (F : Family p c) :
    ∃ α ∈ Ioo (518/1000 : ℝ) (519/1000),
      normalizedReturn c p (α : ℂ) = (α : ℂ) ∧
      ∃ r ∈ Ioo (663/10000 : ℝ) (133/2000),
        terminal F r = -1 ∧
        StrictAntiOn (terminal F) (Icc (1/16 : ℝ) (1/8)) ∧
        (∀ s ∈ Icc (1/16 : ℝ) (1/8), terminal F s = -1 ↔ s = r) ∧
        Icc (1/16 : ℝ) (parentOuter p) ∩ {s | terminalGate F s} = Ico (1/16) r ∧
        Icc (1/16 : ℝ) (parentOuter p) ∩
          {s | GlobalCrestSourceGates.ActualEndpointGates c p s α ∧ terminalGate F s} =
            Ico (1/16) r ∧
        connectedComponentIn
          (Icc (1/16 : ℝ) (parentOuter p) ∩ {s | terminalGate F s}) (1/16) =
            Ico (1/16) r := by
  obtain ⟨α,hα,hfixed,hunique,hsource⟩ :=
    GlobalCrestSourceGates.actual_complete_endpoint_gates hp hc
  obtain ⟨r,hr,hzero,hroot,hgate,hset⟩ := actual_full_gate_classification hp hc F
  have hpout := parentOuter_bounds hp
  have hactual : Icc (1/16 : ℝ) (parentOuter p) ∩ {s | terminalGate F s} =
      Ico (1/16) r := by
    ext s
    constructor
    · rintro ⟨hs,hg⟩
      exact ⟨hs.1,(hgate s ⟨hs.1,hs.2.trans hpout.2⟩).mp hg⟩
    · intro hs
      have hsfull : s ∈ Icc (1/16 : ℝ) (1/8) := by
        constructor <;> linarith [hs.1,hs.2,hr.2]
      exact ⟨⟨hs.1,by linarith [hs.2,hr.2,hpout.1]⟩,(hgate s hsfull).mpr hs.2⟩
  refine ⟨α,hα,hfixed,r,hr,hzero,actual_terminal_strictAnti hp hc F,
    hroot,hactual,?_,?_⟩
  · ext s
    constructor
    · rintro ⟨hs,_,hg⟩
      rw [← hactual]
      exact ⟨hs,hg⟩
    · intro hs
      have hret : s ∈ Icc (1/16 : ℝ) (parentOuter p) ∩ {s | terminalGate F s} := by
        rwa [hactual]
      exact ⟨hret.1,hsource s ⟨hs.1,by linarith [hs.2,hr.2]⟩,hret.2⟩
  · rw [hactual]
    exact isPreconnected_Ico.connectedComponentIn
      (show (1/16 : ℝ) ∈ Ico (1/16 : ℝ) r by constructor <;> linarith [hr.1])

end
end GlobalCrestClassification
