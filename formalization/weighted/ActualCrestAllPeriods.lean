import ActualCrestGlobal
import ActualCrestArcCensus
import ActualCrestQuantitativeSupport

/-!+# The complete original-parent terminal collar at every return index at least seventeen

Effective complete-support control and the quantitative crossing comparison
remove the finite exceptional range from the earlier eventual endpoint
construction.  The terminal gate is tested at every upper-semicircle angle
on the complete original parent, with both actual cuts.
-/

namespace ActualCrestAllPeriods

open Set Function
open LimitingCrest NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn
open LoopsLimitingCrestParameter ActualCrestCrossingWindow ActualCrestEndpoint
open ActualCrestGlobal ActualCrestGlobalQuantitative ActualCrestQuantitativeSupport
open ActualCrestArcCensus

noncomputable section

/-- The literal third-return coordinate is injective on the whole
crossing window at every admissible return index. -/
theorem terminal_injective_all_periods {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (F : Family p c) :
    InjOn (terminal F) radiusInterval := by
  intro s hs t ht he
  let ss : Radius := ⟨s,hs⟩
  let tt : Radius := ⟨t,ht⟩
  have hthree : ((normalizedReturn c p)^[3]) (F.point ss) =
      ((normalizedReturn c p)^[3]) (F.point tt) := by
    apply Complex.ext
    · simpa only [terminal,point,radiusProjection_eq hs,radiusProjection_eq ht] using he
    · rw [F.third_real (by omega) ss,F.third_real (by omega) tt]
  have hfour := congrArg (normalizedReturn c p) hthree
  have hsangle : F.angle ss ∈ Icc (F.angle ss) 1 :=
    ⟨le_rfl,by linarith [(F.angle_mem ss).2]⟩
  have htangle : F.angle tt ∈ Icc (F.angle tt) 1 :=
    ⟨le_rfl,by linarith [(F.angle_mem tt).2]⟩
  have hst := (selected_closed_arc_collision_iff hp hc F
    (actual_complete_support_all_periods hp hc) ss tt hsangle htangle).mp hfour
  exact congrArg Subtype.val hst.1

private theorem terminal_as_crossing {p : ℕ} {c s : ℝ}
    (F : Family p c) (hs : s ∈ radiusInterval) :
    terminal F s =
      (((normalizedReturn c p)^[3]) (circlePoint s (F.angle ⟨s,hs⟩))).re := by
  simp only [terminal,point,radiusProjection_eq hs,Family.point]

private theorem model_critical_cast (κ : ℝ) (m : ℕ) :
    ((complexMap κ)^[m]) (0 : ℂ) = (((realMap κ)^[m]) (0 : ℝ) : ℂ) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [iterate_succ_apply',iterate_succ_apply',ih,complexMap_real]

/-- The actual selected terminal coordinate has an explicit error from
the model with its own quadratic coefficient, throughout the window. -/
theorem terminal_error_all_periods {p : ℕ} (hp : 17 ≤ p) {c s : ℝ}
    (hc : ActualTip p c) (F : Family p c) (hs : s ∈ radiusInterval) :
    |terminal F s-crestTerminal (kappa p c) s| ≤ (1609/10000000 : ℝ) := by
  let ss : Radius := ⟨s,hs⟩
  have ha : F.angle ss ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [(F.angle_mem ss).1,(F.angle_mem ss).2]
  have he := quantitative_crossing_error hc.2.2.2.1 (normalizedReturn c p)
    (actual_map_error_small hp hc)
    (show s ∈ Icc (1/16 : ℝ) (1/8) from ⟨hs.1,hs.2.trans (by norm_num)⟩)
    ha (F.crossing ss)
  have hr := (Complex.abs_re_le_norm
    (((normalizedReturn c p)^[3]) (circlePoint s (F.angle ss))-
      (crestTerminal (kappa p c) s : ℂ))).trans he
  rw [terminal_as_crossing F hs]
  simpa only [Complex.sub_re,Complex.ofReal_re] using hr

/-- The actual endpoint has opposite strict signs at the two explicit
bracketing radii for every admissible return index. -/
theorem terminal_endpoint_signs_all_periods {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (F : Family p c) :
    -1 < terminal F (663/10000) ∧ terminal F (133/2000) < -1 := by
  have hinner := model_inner_terminal_margin hc.2.2.2.1
  have herr := terminal_error_all_periods hp hc F
    (show (663/10000 : ℝ) ∈ radiusInterval by constructor <;> norm_num)
  refine ⟨by linarith [(abs_le.mp herr).1],?_⟩
  have hs : (133/2000 : ℝ) ∈ radiusInterval := by constructor <;> norm_num
  let ss : Radius := ⟨133/2000,hs⟩
  have ha : F.angle ss ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [(F.angle_mem ss).1,(F.angle_mem ss).2]
  have htail := all_actual_tips_no_reentry hp hc
    (show (133/2000 : ℝ) ∈ Icc (133/2000 : ℝ) (1/8) by constructor <;> norm_num)
    ha (F.crossing ss)
  rw [terminal_as_crossing F hs]
  exact htail.trans (by norm_num)

/-- Complete actual radial order holds at the explicit threshold
seventeen; no first-exit existence premise is used to orient it. -/
theorem terminal_strictAnti_all_periods {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (F : Family p c) :
    StrictAntiOn (terminal F) radiusInterval := by
  have hinj := terminal_injective_all_periods hp hc F
  rcases ContinuousOn.strictMonoOn_of_injOn_Icc'
    (by norm_num : (1/16 : ℝ) ≤ 133/2000)
    (terminal_continuous F).continuousOn hinj with hmono | hanti
  · obtain ⟨hlo,hhi⟩ := terminal_endpoint_signs_all_periods hp hc F
    have h := hmono
      (show (663/10000 : ℝ) ∈ radiusInterval by constructor <;> norm_num)
      (show (133/2000 : ℝ) ∈ radiusInterval by constructor <;> norm_num)
      (by norm_num : (663/10000 : ℝ) < 133/2000)
    linarith
  · exact hanti

/-- The opposite actual terminal cut is inactive on the complete
crossing window for every admissible return index at least seventeen. -/
theorem upper_gate_all_periods {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (F : Family p c) :
    ∀ s ∈ radiusInterval,
      terminal F s < -(((normalizedReturn c p)^[4]) 0).re := by
  have hk := hc.2.2.2.1
  have hclose := actual_map_error_small hp hc
  have hcutError := LimitingCrestPerturbation.quadratic_fourth_cut_error (kappa p c)
    (by linarith [hk.1]) (by linarith [hk.2]) (normalizedReturn c p)
    (1/10000000) (by norm_num) (by norm_num)
    (by
      intro w hw
      exact hclose w (hw.trans (by norm_num)))
  have hcutReal := (Complex.re_le_norm
    (((normalizedReturn c p)^[4]) 0-((complexMap (kappa p c))^[4]) 0)).trans hcutError.1
  rw [model_critical_cast] at hcutReal
  simp only [Complex.sub_re,Complex.ofReal_re] at hcutReal
  have hmodelCut := model_fourth_cut_margin hk
  intro s hs
  have hmodel := model_uniform_upper_margin hk
    (show s ∈ Icc (1/16 : ℝ) (1/8) from ⟨hs.1,hs.2.trans (by norm_num)⟩)
  have herr := terminal_error_all_periods hp hc F hs
  linarith [(abs_le.mp herr).2]

/-- Every admissible actual parameter has a unique terminal root in the
explicit bracket and one exact complete gate on the original parent.
All radii and all angular crossings are quantified; there is no finite
exceptional range beyond the declared threshold seventeen. -/
theorem complete_original_parent_all_periods {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (F : Family p c) :
    ∃ r ∈ Ioo (663/10000 : ℝ) (133/2000),
      InitialCollar F r ∧
      (∀ s ∈ radiusInterval, terminal F s = -1 ↔ s = r) ∧
      (∀ s ∈ Icc (1/16 : ℝ) (1/8), TerminalGate p c s ↔ s < r) ∧
      {s : ℝ | 1/16 < s ∧ s < ((p : ℝ)-1)/(8*(p : ℝ)) ∧
        TerminalGate p c s} = Ioo (1/16) r := by
  have hanti := terminal_strictAnti_all_periods hp hc F
  obtain ⟨hlo,hhi⟩ := terminal_endpoint_signs_all_periods hp hc F
  have hcont := (terminal_continuous F).neg
  obtain ⟨r,hr,hzero⟩ := intermediate_value_Icc
    (by norm_num : (663/10000 : ℝ) ≤ 133/2000) hcont.continuousOn
    (show (1 : ℝ) ∈ Icc (-terminal F (663/10000)) (-terminal F (133/2000)) by
      constructor <;> linarith)
  have hroot : terminal F r = -1 := by linarith
  have hrbracket : r ∈ Ioo (663/10000 : ℝ) (133/2000) := by
    constructor
    · by_contra h
      have he : r = 663/10000 := by linarith [hr.1]
      rw [he] at hroot
      linarith
    · by_contra h
      have he : r = 133/2000 := by linarith [hr.2]
      rw [he] at hroot
      linarith
  have hrfull : r ∈ Ioo (1/16 : ℝ) (133/2000) :=
    ⟨(by norm_num : (1/16 : ℝ) < 663/10000).trans hrbracket.1,hrbracket.2⟩
  have hprefix : ∀ s ∈ Ico (1/16 : ℝ) r, -1 < terminal F s := by
    intro s hs
    have hm := hanti ⟨hs.1,hs.2.le.trans hrfull.2.le⟩
      ⟨hrfull.1.le,hrfull.2.le⟩ hs.2
    rwa [hroot] at hm
  have hcollar : InitialCollar F r :=
    ⟨hrfull,hroot,hprefix,CrestFirstExit.first_exit_component (terminal F)
      hrfull hroot hprefix⟩
  have hupper := upper_gate_all_periods hp hc F
  have hunique :=
    (ActualCrestTheorem.complete_terminal_component F hcollar hanti hupper).1
  have hgate := terminalGate_iff_below_endpoint hp hc F hcollar hanti hupper (by
    intro s hs u hu hzero
    exact (all_actual_tips_no_reentry hp hc hs hu hzero).trans (by norm_num))
  exact ⟨r,hrbracket,hcollar,hunique,hgate,
    original_parent_gate_set hp hrfull.2 hgate⟩

/-- The actual parameters and angular families are constructed, so the
full-parent collar theorem is nonvacuous at each index at least seventeen. -/
theorem exists_complete_original_parent_each_period (p : ℕ) (hp : 17 ≤ p) :
    ∃ c : ℝ, ActualTip p c ∧ ∃ F : Family p c,
      ∃ r ∈ Ioo (663/10000 : ℝ) (133/2000), InitialCollar F r ∧
        (∀ s ∈ radiusInterval, terminal F s = -1 ↔ s = r) ∧
        (∀ s ∈ Icc (1/16 : ℝ) (1/8), TerminalGate p c s ↔ s < r) ∧
        {s : ℝ | 1/16 < s ∧ s < ((p : ℝ)-1)/(8*(p : ℝ)) ∧
          TerminalGate p c s} = Ioo (1/16) r := by
  obtain ⟨c,hc⟩ := exists_actual_tip p hp
  obtain ⟨F⟩ := exists_family hp hc
  exact ⟨c,hc,F,complete_original_parent_all_periods hp hc F⟩

end
end ActualCrestAllPeriods
