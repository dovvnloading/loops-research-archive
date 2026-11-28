import ThreeLevelTerminal
import ThreeLevelMiddle

/-!
# Three simultaneous physical return components

All three sources are components of complete pullbacks in one original
quadratic plane.  In particular the middle source is constructed from
its own full target disk, independently of the terminal tip normalization.
-/

namespace ThreeLevelPhysical

open Set Function Metric
open LimitingCrestQuadraticReturn NearTwoShooting TwoLevelOuterChart TwoLevelConjugacy
open ThreeLevelSelection ThreeReturnParent

noncomputable section

def middleRadius (c : ℝ) (p q : ℕ) : ℝ :=
  ThreeLevelMiddle.radius q/|returnCoefficient p c|

def middleSource (c : ℝ) (p q : ℕ) : Set ℂ :=
  ThreeLevelDomains.source c (q*p) (middleRadius c p q)

theorem middle_scaled_identity (c : ℝ) (p q : ℕ)
    (hA : returnCoefficient p c ≠ 0) (z : ℂ) :
    ThreeLevelDomains.scaledReturn c (q*p) (returnCoefficient p c) z =
      ((outerMap c p)^[q]) z :=
  (outerMap_iterate_scale c p hA q z).symm

theorem chart_middle_budget {p q r n : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) (hp : 20*(r*q)+100 ≤ p) (hn : n ≤ r*q) :
    error p*(5 : ℝ)^n ≤ scale q := by
  have hb := error_budget hr hqr hp (show n ≤ 12*(r*q) by omega)
  have hs : scale r ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hm := mul_le_mul_of_nonneg_left hs (scale_pos q).le
  nlinarith only [hb, hm, (scale_pos q).le]

theorem chart_middle_restriction {p q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) (hp : 20*(r*q)+100 ≤ p)
    {a b l u L U c : ℝ} (h : SharpChart r a b)
    (g : OuterChart q a b l u) (j : OuterChart p l u L U) (hc : c ∈ Icc L U) :
    ThreeLevelDomains.Restriction c (q*p) (middleRadius c p q) (middleRadius c p q/2) := by
  have hq : 17 ≤ q := by omega
  have hA := coefficient_negative (j.coefficient_lower c hc)
  have hqrN : q ≤ r*q := by
    have hh := Nat.mul_le_mul_right q (show 1 ≤ r by omega)
    simpa only [one_mul] using hh
  have hbudget := chart_middle_budget hr hqr hp hqrN
  have hclose := fun z hz => j.outerMap_error (by omega : 17 ≤ p) hc z hz
  have hid := middle_scaled_identity c p q hA.ne
  have hresult := ThreeLevelDomains.restriction_of_scaled_estimates c (q*p)
    (returnCoefficient p c) (ThreeLevelMiddle.radius q) (ThreeLevelMiddle.radius q/2)
    (Nat.mul_pos (by omega) (by omega)) hA.ne
    (by linarith [ThreeLevelMiddle.radius_pos q])
    (by linarith [ThreeLevelMiddle.radius_pos q])
    (by rw [hid]; exact (ThreeLevelMiddle.middle_critical_norm (outerMap c p) hq g
      (j.monic_range hc) (error p) (error_nonneg p) hbudget hclose).2)
    (by intro z hz; rw [hid]; exact ThreeLevelMiddle.middle_barrier (outerMap c p)
      hq g (j.monic_range hc) (error p) (error_nonneg p) hbudget hclose hz)
    (by
      intro z w hz hw
      rw [hid,hid]
      exact ThreeLevelMiddle.middle_collision (outerMap c p) hq g (j.monic_range hc)
        (error p) (error_nonneg p) hbudget hclose
        (fun hv hx => TwoLevelOuterChart.outerMap_collision_iff (by omega)
          (j.critical_orbit c hc) (j.coefficient_lower c hc) hv hx) hz hw)
  convert hresult using 1 <;> unfold middleRadius <;> ring

theorem chart_middle_small_disk {p q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) (hp : 20*(r*q)+100 ≤ p)
    {a b l u L U c : ℝ} (h : SharpChart r a b)
    (g : OuterChart q a b l u) (j : OuterChart p l u L U) (hc : c ∈ Icc L U)
    {z : ℂ} (hz : ‖z‖ ≤ 16*scale q) :
    z/(returnCoefficient p c : ℂ) ∈ middleSource c p q := by
  have hA := coefficient_negative (j.coefficient_lower c hc)
  apply ThreeLevelDomains.scaled_disk_in_source c (q*p) (returnCoefficient p c)
    (ThreeLevelMiddle.radius q) (16*scale q) hA.ne (by positivity) _ z hz
  intro w hw
  rw [middle_scaled_identity c p q hA.ne]
  exact ThreeLevelMiddle.middle_small_disk_image (outerMap c p) (by omega) g
    (j.monic_range hc) (error p) (error_nonneg p)
    (chart_middle_budget hr hqr hp (by
      simpa only [one_mul] using Nat.mul_le_mul_right q (show 1 ≤ r by omega)))
    (fun v hv => j.outerMap_error (by omega) hc v hv) hw

/-- Every phase of the entire middle source lies in the original outer source. -/
theorem chart_middle_phases_nested {p q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) (hp : 20*(r*q)+100 ≤ p)
    {a b l u L U c : ℝ} (h : SharpChart r a b)
    (g : OuterChart q a b l u) (j : OuterChart p l u L U) (hc : c ∈ Icc L U)
    (m : ℕ) (hm : m ≤ q) :
    ((quadraticMap c)^[m*p]) '' middleSource c p q ⊆ TwoLevelOuterDomain.source c p := by
  have hA := coefficient_negative (j.coefficient_lower c hc)
  have hAC : (returnCoefficient p c : ℂ) ≠ 0 := by exact_mod_cast hA.ne
  have hAa : 0 < |returnCoefficient p c| := abs_pos.mpr hA.ne
  have hrst := chart_middle_restriction hr hqr hp h g j hc
  rintro _ ⟨z,hz,rfl⟩
  have hzsmall : ‖z‖ < middleRadius c p q/2 := by
    simpa only [mem_ball_zero_iff] using hrst.closure_inside (subset_closure hz)
  have hinput : ‖(returnCoefficient p c : ℂ)*z‖ ≤ ThreeLevelMiddle.radius q/2 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    have hb : ‖z‖ *|returnCoefficient p c| < ThreeLevelMiddle.radius q/2 := by
      apply (lt_div_iff₀ hAa).mp
      convert hzsmall using 1 <;> unfold middleRadius <;> ring
    nlinarith only [hb]
  have hphase := (ThreeLevelMiddle.perturbed_half_disk (outerMap c p) (by omega) g
    (j.monic_range hc) (error p) (error_nonneg p)
    (chart_middle_budget hr hqr hp (by
      simpa only [one_mul] using Nat.mul_le_mul_right q (show 1 ≤ r by omega)))
    (fun v hv => j.outerMap_error (by omega) hc v hv) hinput m hm).2
  rw [outerMap_iterate_scale c p hA.ne] at hphase
  have hin : (returnCoefficient p c : ℂ)*z/(returnCoefficient p c : ℂ) = z := by
    field_simp [hAC]
  rw [hin] at hphase
  have hsource := TwoLevelOuterDomain.monic_disk_in_source (by omega)
    (j.critical_orbit c hc) (j.return_range c hc).1 (j.return_range c hc).2
    (j.coefficient_lower c hc) hphase
  have hout (v : ℂ) : (returnCoefficient p c : ℂ)*v/(returnCoefficient p c : ℂ) = v := by
    field_simp [hAC]
  simpa only [hout] using hsource

theorem chart_terminal_phase_identity {p q r : ℕ} {c : ℝ}
    (hA : returnCoefficient p c ≠ 0) (m : ℕ) (z : ℂ) :
    (returnCoefficient p c : ℂ)*
      ((quadraticMap c)^[m*p]) ((criticalValue c ((r*q)*p) : ℂ)*z) =
      ((outerMap c p)^[m]) ((secondScale c p (r*q) : ℂ)*z) := by
  have hAC : (returnCoefficient p c : ℂ) ≠ 0 := by exact_mod_cast hA
  have hin : (secondScale c p (r*q) : ℂ)*z/(returnCoefficient p c : ℂ) =
      (criticalValue c ((r*q)*p) : ℂ)*z := by
    unfold secondScale
    push_cast
    field_simp [hAC]
  rw [outerMap_iterate_scale c p hA, hin]

/-- Every middle checkpoint of the entire terminal source lies in the
same complete middle pullback component. -/
theorem chart_terminal_phases_nested {p q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) (hp : 20*(r*q)+100 ≤ p)
    {a b l u L U c : ℝ} (h : SharpChart r a b)
    (g : OuterChart q a b l u) (j : OuterChart p l u L U) (hc : c ∈ Icc L U)
    (m : ℕ) (hm : m ≤ r) :
    ((quadraticMap c)^[m*(q*p)]) '' physicalParentSource c ((r*q)*p) ⊆
      middleSource c p q := by
  have hA := coefficient_negative (j.coefficient_lower c hc)
  have hAC : (returnCoefficient p c : ℂ) ≠ 0 := by exact_mod_cast hA.ne
  have hcentral := ThreeLevelTerminal.chart_central_gate hr hqr hp h g j hc
  rintro _ ⟨_,⟨z,hz,rfl⟩,rfl⟩
  have hzR : ‖z‖ ≤ 23/20 := by
    exact (show ‖z‖ < 23/20 by simpa using hcentral.closure_inside (subset_closure hz)).le
  have hphase := ThreeLevelMiddle.terminal_block_bound (outerMap c p) hr hqr h g
    (j.monic_range hc) (error p) (error_nonneg p)
    (chart_middle_budget hr hqr hp le_rfl)
    (fun v hv => j.outerMap_error (by omega) hc v hv)
    (secondScale c p (r*q)) (chart_scale_relative hr hqr hp h g j hc) hzR m hm
  have hin := chart_middle_small_disk hr hqr hp h g j hc
    (hphase.trans (by linarith [scale_pos q] : 15*scale q ≤ 16*scale q))
  rw [← chart_terminal_phase_identity hA.ne (m*q) z] at hin
  have hcancel (v : ℂ) : (returnCoefficient p c : ℂ)*v/(returnCoefficient p c : ℂ) = v := by
    field_simp [hAC]
  simpa only [hcancel,Nat.mul_assoc] using hin

/-- All intermediate outer-return phases of the terminal source stay
in the original outer source, including phases between middle checkpoints. -/
theorem chart_terminal_outer_phases {p q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) (hp : 20*(r*q)+100 ≤ p)
    {a b l u L U c : ℝ} (h : SharpChart r a b)
    (g : OuterChart q a b l u) (j : OuterChart p l u L U) (hc : c ∈ Icc L U)
    (m : ℕ) (hm : m ≤ r*q) :
    ((quadraticMap c)^[m*p]) '' physicalParentSource c ((r*q)*p) ⊆
      TwoLevelOuterDomain.source c p := by
  have hA := coefficient_negative (j.coefficient_lower c hc)
  have hAC : (returnCoefficient p c : ℂ) ≠ 0 := by exact_mod_cast hA.ne
  have hcentral := ThreeLevelTerminal.chart_central_gate hr hqr hp h g j hc
  rintro _ ⟨_,⟨z,hz,rfl⟩,rfl⟩
  have hzR : ‖z‖ ≤ 23/20 := by
    exact (show ‖z‖ < 23/20 by simpa using hcentral.closure_inside (subset_closure hz)).le
  have hb := ThreeLevelTerminal.chart_phase_disk hr hqr hp h g j hc hzR m hm
  rw [← chart_terminal_phase_identity hA.ne m z] at hb
  have hout := TwoLevelOuterDomain.monic_disk_in_source (by omega)
    (j.critical_orbit c hc) (j.return_range c hc).1 (j.return_range c hc).2
    (j.coefficient_lower c hc) hb
  have hcancel (v : ℂ) : (returnCoefficient p c : ℂ)*v/(returnCoefficient p c : ℂ) = v := by
    field_simp [hAC]
  simpa only [hcancel] using hout

theorem chart_middle_first_return {p q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) (hp : 20*(r*q)+100 ≤ p)
    {a b l u L U c : ℝ} (h : SharpChart r a b)
    (g : OuterChart q a b l u) (j : OuterChart p l u L U) (hc : c ∈ Icc L U)
    (m : ℕ) (hm : 1 ≤ m) (hmq : m < q) :
    Disjoint (((quadraticMap c)^[m*p]) '' middleSource c p q)
      (ball 0 (middleRadius c p q)) := by
  have hA := coefficient_negative (j.coefficient_lower c hc)
  have hAC : (returnCoefficient p c : ℂ) ≠ 0 := by exact_mod_cast hA.ne
  have hAa : 0 < |returnCoefficient p c| := abs_pos.mpr hA.ne
  have hrst := chart_middle_restriction hr hqr hp h g j hc
  apply Set.disjoint_left.mpr
  rintro _ ⟨z,hz,rfl⟩ hy
  have hzsmall : ‖z‖ < middleRadius c p q/2 := by
    simpa only [mem_ball_zero_iff] using hrst.closure_inside (subset_closure hz)
  have hinput : ‖(returnCoefficient p c : ℂ)*z‖ ≤ ThreeLevelMiddle.radius q/2 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    have hb : ‖z‖ *|returnCoefficient p c| < ThreeLevelMiddle.radius q/2 := by
      apply (lt_div_iff₀ hAa).mp
      convert hzsmall using 1 <;> unfold middleRadius <;> ring
    nlinarith only [hb]
  have hphase := ThreeLevelMiddle.middle_noncentral_phase (outerMap c p) (by omega) g
    (j.monic_range hc) (error p) (error_nonneg p)
    (chart_middle_budget hr hqr hp (by
      simpa only [one_mul] using Nat.mul_le_mul_right q (show 1 ≤ r by omega)))
    (fun v hv => j.outerMap_error (by omega) hc v hv) hinput m hm hmq
  rw [outerMap_iterate_scale c p hA.ne] at hphase
  have hin : (returnCoefficient p c : ℂ)*z/(returnCoefficient p c : ℂ) = z := by
    field_simp [hAC]
  rw [hin,norm_mul,Complex.norm_real,Real.norm_eq_abs] at hphase
  have hy' : ‖((quadraticMap c)^[m*p]) z‖ <
      ThreeLevelMiddle.radius q/|returnCoefficient p c| := by simpa [middleRadius] using hy
  have hm' := (lt_div_iff₀ hAa).mp hy'
  nlinarith only [hphase,hm',ThreeLevelMiddle.radius_small (show 17 ≤ q by omega)]

theorem chart_terminal_scale_upper {p q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) (hp : 20*(r*q)+100 ≤ p)
    {a b l u L U c : ℝ} (h : SharpChart r a b)
    (g : OuterChart q a b l u) (j : OuterChart p l u L U) (hc : c ∈ Icc L U) :
    |secondScale c p (r*q)| < 82*scale q*scale r := by
  have href := ThreeLevelReference.terminal_scale_upper hr hqr h g (j.monic_range hc)
  have herr := chart_scale_relative hr hqr hp h g j hc
  have ht := abs_add_le
    (secondScale c p (r*q)-criticalValue (monicParameter p c) (r*q))
    (criticalValue (monicParameter p c) (r*q))
  rw [sub_add_cancel] at ht
  nlinarith only [href, herr, ht, mul_pos (scale_pos q) (scale_pos r)]

/-- The entire terminal source misses its own target at every
intermediate outer-return phase, not only at the middle checkpoints. -/
theorem chart_terminal_first_return {p q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) (hp : 20*(r*q)+100 ≤ p)
    {a b l u L U c : ℝ} (h : SharpChart r a b)
    (g : OuterChart q a b l u) (j : OuterChart p l u L U) (hc : c ∈ Icc L U)
    (m : ℕ) (hm : 1 ≤ m) (hmN : m < r*q) :
    Disjoint (((quadraticMap c)^[m*p]) '' physicalParentSource c ((r*q)*p))
      (TwoLevelPhysicalGate.physicalTarget c ((r*q)*p)) := by
  have hA := coefficient_negative (j.coefficient_lower c hc)
  have hAa : 0 < |returnCoefficient p c| := abs_pos.mpr hA.ne
  have hcentral := ThreeLevelTerminal.chart_central_gate hr hqr hp h g j hc
  apply Set.disjoint_left.mpr
  rintro _ ⟨_,⟨z,hz,rfl⟩,rfl⟩ hy
  have hzR : ‖z‖ ≤ 23/20 := by
    exact (show ‖z‖ < 23/20 by simpa using hcentral.closure_inside (subset_closure hz)).le
  have hphase := ThreeLevelMiddle.terminal_noncentral_phase (outerMap c p) hr hqr h g
    (j.monic_range hc) (error p) (error_nonneg p)
    (chart_middle_budget hr hqr hp le_rfl)
    (fun v hv => j.outerMap_error (by omega) hc v hv)
    (secondScale c p (r*q)) (chart_scale_relative hr hqr hp h g j hc) hzR m hm hmN
  rw [← chart_terminal_phase_identity hA.ne m z,
    norm_mul, Complex.norm_real, Real.norm_eq_abs] at hphase
  have hy' : ‖((quadraticMap c)^[m*p]) ((criticalValue c ((r*q)*p) : ℂ)*z)‖ <
      |criticalValue c ((r*q)*p)| *(23/20) := by
    simpa [TwoLevelPhysicalGate.physicalTarget] using hy
  have hscaled := mul_lt_mul_of_pos_left hy' hAa
  have hid : |returnCoefficient p c| * |criticalValue c ((r*q)*p)| =
      |secondScale c p (r*q)| := by rw [secondScale, abs_mul]
  rw [← mul_assoc, hid] at hscaled
  have hu := chart_terminal_scale_upper hr hqr hp h g j hc
  have hs := mul_le_mul_of_nonneg_left (scale_small hr) (scale_pos q).le
  nlinarith only [hphase, hscaled, hu, hs, scale_pos q]

theorem chart_outer_restriction {p : ℕ} (hp : 17 ≤ p)
    {a b l u c : ℝ} (j : OuterChart p a b l u) (hc : c ∈ Icc l u) :
    ThreeLevelDomains.Restriction c p (TwoLevelOuterDomain.targetRadius p)
      (TwoLevelOuterDomain.targetRadius p/2) := by
  have hR := TwoLevelOuterDomain.targetRadius_pos p
  apply ThreeLevelDomains.restriction_of_estimates c p
    (TwoLevelOuterDomain.targetRadius p) (TwoLevelOuterDomain.targetRadius p/2)
    (by omega) (by linarith) (by linarith)
  · have h0 := connectedComponentIn_subset
      (((quadraticMap c)^[p]) ⁻¹' ball 0 (TwoLevelOuterDomain.targetRadius p)) 0
      (TwoLevelOuterDomain.source_zero hp (j.return_range c hc).1 (j.return_range c hc).2)
    simpa only [mem_preimage, mem_ball_zero_iff] using h0
  · exact fun z hz => TwoLevelOuterDomain.outer_barrier hp (j.critical_orbit c hc)
      (j.return_range c hc).1 (j.return_range c hc).2 (j.coefficient_lower c hc) hz
  · intro z w hz hw
    exact TwoLevelOuterDomain.outer_collision_iff hp (j.critical_orbit c hc)
      (j.coefficient_lower c hc) (by linarith) (by linarith)

/-- Three simultaneous complete physical pullbacks for one quadratic map.
The terminal round gate is part of the conclusion, and every whole-source
phase uses the same outer and middle components. -/
structure PhysicalThreeLevelGate (p q r : ℕ) (c : ℝ) : Prop where
  parameter_band : c ∈ Icc (-2 : ℝ) (-2+20*scale p)
  signed_relation : criticalValue c (6*((r*q)*p))+criticalValue c (3*((r*q)*p)) = 0
  terminal_scale_pos : 0 < criticalValue c ((r*q)*p)
  outer : ThreeLevelDomains.Restriction c p (TwoLevelOuterDomain.targetRadius p)
    (TwoLevelOuterDomain.targetRadius p/2)
  middle : ThreeLevelDomains.Restriction c (q*p) (middleRadius c p q) (middleRadius c p q/2)
  terminal : TwoLevelPhysicalGate.PhysicalGate c ((r*q)*p)
  middle_phases : ∀ m : ℕ, m ≤ q →
    ((quadraticMap c)^[m*p]) '' middleSource c p q ⊆ TwoLevelOuterDomain.source c p
  terminal_phases : ∀ m : ℕ, m ≤ r →
    ((quadraticMap c)^[m*(q*p)]) '' physicalParentSource c ((r*q)*p) ⊆ middleSource c p q
  terminal_outer_phases : ∀ m : ℕ, m ≤ r*q →
    ((quadraticMap c)^[m*p]) '' physicalParentSource c ((r*q)*p) ⊆ TwoLevelOuterDomain.source c p
  outer_first : ∀ m : ℕ, 1 ≤ m → m < p → ∀ z : ℂ,
    ‖z‖ ≤ TwoLevelOuterDomain.targetRadius p →
      TwoLevelOuterDomain.targetRadius p < ‖((quadraticMap c)^[m]) z‖
  middle_first : ∀ m : ℕ, 1 ≤ m → m < q →
    Disjoint (((quadraticMap c)^[m*p]) '' middleSource c p q) (ball 0 (middleRadius c p q))
  terminal_first : ∀ m : ℕ, 1 ≤ m → m < r*q →
    Disjoint (((quadraticMap c)^[m*p]) '' physicalParentSource c ((r*q)*p))
      (TwoLevelPhysicalGate.physicalTarget c ((r*q)*p))

theorem chart_physical_three_level_gate {p q r : ℕ} (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) (hp : 20*(r*q)+100 ≤ p)
    {a b l u L U c : ℝ} (h : SharpChart r a b)
    (g : OuterChart q a b l u) (j : OuterChart p l u L U) (hc : c ∈ Icc L U)
    (hrel : criticalValue c (6*((r*q)*p))+criticalValue c (3*((r*q)*p)) = 0) :
    PhysicalThreeLevelGate p q r c := by
  refine ⟨j.parameter_range c hc, hrel, physical_scale_positive hr hqr hp h g j hc,
    chart_outer_restriction (by omega) j hc,
    chart_middle_restriction hr hqr hp h g j hc,
    TwoLevelPhysicalGate.physical_gate_of_central
      (ThreeLevelTerminal.chart_central_gate hr hqr hp h g j hc),
    chart_middle_phases_nested hr hqr hp h g j hc,
    chart_terminal_phases_nested hr hqr hp h g j hc,
    chart_terminal_outer_phases hr hqr hp h g j hc, ?_,
    chart_middle_first_return hr hqr hp h g j hc,
    chart_terminal_first_return hr hqr hp h g j hc⟩
  intro m hm hmp z hz
  exact TwoLevelOuterDomain.outer_first_return_exclusion (by omega)
    (j.parameter_range c hc) (j.critical_orbit c hc)
    (j.return_range c hc).1 (j.return_range c hc).2 (j.itinerary c hc)
    m hm hmp hz

/-- An unbounded three-parameter family of simultaneous physical
degree-two returns, with the terminal relation selected in the original
parameter rather than imposed on a quadratic approximation. -/
theorem exists_physical_three_level_gate (p q r : ℕ) (hr : 17 ≤ r)
    (hqr : 10*r+30 ≤ q) (hp : 20*(r*q)+100 ≤ p) :
    ∃ c : ℝ, PhysicalThreeLevelGate p q r c := by
  obtain ⟨a,b,l,u,L,U,c,h,g,j,hc,hrel,_⟩ :=
    exists_three_level_parameter p q r hr hqr hp
  exact ⟨c, chart_physical_three_level_gate hr hqr hp h g j hc hrel⟩

end
end ThreeLevelPhysical
