import DepthGatePrefix
import ThreeLevelMiddle

/-!
# Prefixing every ancestor of a finite physical return tower

The inherited disks are transported by the actual signed outer
coefficient. Complete-iterate estimates preserve their barriers, their
two-sheeted collision margins, and every descendant checkpoint. A new
outer disk is added with an explicit core and a positive nesting margin.
-/

namespace DepthGate.Ancestors

open Set Function Metric
open LimitingCrestQuadraticReturn LimitingCrest NearTwoShooting
open TwoLevelOuterChart TwoLevelConjugacy TwoLevelPerturbation
open TerminalChart

noncomputable section

private theorem scale_input {c : ℝ} {p : ℕ} {r : ℝ} {z : ℂ}
    (hA : returnCoefficient p c ≠ 0)
    (hz : ‖z‖ ≤ r/|returnCoefficient p c|) :
    ‖(returnCoefficient p c : ℂ)*z‖ ≤ r := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hh := (le_div_iff₀ (abs_pos.mpr hA)).mp hz
  nlinarith only [hh]

private theorem scale_circle {c : ℝ} {p : ℕ} {r : ℝ} {z : ℂ}
    (hA : returnCoefficient p c ≠ 0)
    (hz : ‖z‖ = r/|returnCoefficient p c|) :
    ‖(returnCoefficient p c : ℂ)*z‖ = r := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hz]
  field_simp [(abs_pos.mpr hA).ne']

private theorem scale_input_cancel {c : ℝ} {p : ℕ}
    (hA : returnCoefficient p c ≠ 0) (z : ℂ) :
    (returnCoefficient p c : ℂ)*z/(returnCoefficient p c : ℂ) = z := by
  have hAC : (returnCoefficient p c : ℂ) ≠ 0 := by exact_mod_cast hA
  field_simp [hAC]

private theorem coarse_norm {c : ℝ} {p : ℕ}
    (hA : returnCoefficient p c ≠ 0) (n : ℕ) (v : ℂ) :
    ‖((outerMap c p)^[n]) v‖ = |returnCoefficient p c| *
      ‖((quadraticMap c)^[n*p]) (v/(returnCoefficient p c : ℂ))‖ := by
  rw [outerMap_iterate_scale c p hA, norm_mul, Complex.norm_real, Real.norm_eq_abs]

private theorem margin_le_scale (C : TerminalChart) (p : ℕ) :
    C.prefixMargin p ≤ scale p/10000 := by
  have h := mul_le_mul_of_nonneg_right C.margin_le (scale_pos p).le
  unfold prefixMargin
  nlinarith only [h]

private theorem coefficient_ge_one (C : TerminalChart) {p : ℕ}
    (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U) :
    1 ≤ |returnCoefficient p c| := by
  have hlo := (ThreeLevelReference.coefficient_scale_bounds hp.1 j hc).1
  by_contra! hh
  have hm := mul_le_mul_of_nonneg_right hh.le (scale_pos p).le
  nlinarith only [hlo, hm, scale_small hp.1]

private theorem divide_upper (C : TerminalChart) {p : ℕ}
    (hp : C.AdmissiblePrefix p) {L U c x X : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U)
    (hx : |returnCoefficient p c| * x ≤ X-C.margin/2) :
    x ≤ X/|returnCoefficient p c| -C.prefixMargin p := by
  have ha := abs_pos.mpr (coefficient_negative (j.coefficient_lower c hc)).ne
  have hm := C.prefix_margin_weighted hp j hc
  have hs : x+C.prefixMargin p ≤ X/|returnCoefficient p c| := by
    apply (le_div_iff₀ ha).mpr
    nlinarith only [hx, hm, C.margin_pos]
  linarith only [hs]

private theorem divide_lower (C : TerminalChart) {p : ℕ}
    (hp : C.AdmissiblePrefix p) {L U c x X : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U)
    (hx : X+C.margin/2 ≤ |returnCoefficient p c| * x) :
    X/|returnCoefficient p c| +C.prefixMargin p ≤ x := by
  have ha := abs_pos.mpr (coefficient_negative (j.coefficient_lower c hc)).ne
  have hm := C.prefix_margin_weighted hp j hc
  have hs : X/|returnCoefficient p c| ≤ x-C.prefixMargin p := by
    apply (div_le_iff₀ ha).mpr
    nlinarith only [hx, hm, C.margin_pos]
  linarith only [hs]

private theorem outer_radii (C : TerminalChart) {p : ℕ}
    (hp : C.AdmissiblePrefix p) :
    C.prefixMargin p ≤ 15*scale p ∧
      15*scale p+C.prefixMargin p ≤ ThreeLevelMiddle.radius p/2 ∧
      ThreeLevelMiddle.radius p/2+C.prefixMargin p ≤ ThreeLevelMiddle.radius p ∧
      ThreeLevelMiddle.radius p ≤ 1/100 := by
  have hm := margin_le_scale C p
  have hs := ThreeLevelMiddle.scale_inside_radius hp.1
  have hsp := scale_pos p
  have hR := ThreeLevelMiddle.radius_small hp.1
  constructor
  · nlinarith only [hm, hsp]
  constructor
  · nlinarith only [hm, hs, hsp]
  constructor
  · nlinarith only [hm, hs, hsp]
  · linarith only [hR]

private theorem outer_critical (C : TerminalChart) {p : ℕ}
    (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U) :
    ‖((quadraticMap c)^[p]) 0‖ ≤ ThreeLevelMiddle.radius p-C.prefixMargin p := by
  rw [complex_criticalValue, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (j.return_range c hc).1]
  nlinarith only [(j.return_range c hc).2, margin_le_scale C p,
    ThreeLevelMiddle.scale_inside_radius hp.1, scale_pos p]

private theorem outer_circle (C : TerminalChart) {p : ℕ}
    (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U)
    {z : ℂ} (hz : ‖z‖ = ThreeLevelMiddle.radius p/2) :
    ThreeLevelMiddle.radius p+C.prefixMargin p ≤ ‖((quadraticMap c)^[p]) z‖ := by
  have h := ThreeLevelMiddle.reference_barrier_margin hp.1 j hc hz
  nlinarith only [h, ThreeLevelMiddle.radius_small hp.1,
    margin_le_scale C p, scale_small hp.1]

private theorem outer_core (C : TerminalChart) {p : ℕ}
    (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U)
    {z : ℂ} (hz : ‖z‖ ≤ 15*scale p) :
    ‖((quadraticMap c)^[p]) z‖ ≤ ThreeLevelMiddle.radius p-C.prefixMargin p := by
  have he := ThreeLevelReference.small_disk_displacement hp.1
    (ThreeLevelReference.chart_parameter_band hp.1 j hc) hz p
    (by have := hp.1; omega) le_rfl
  have ht := norm_le_norm_sub_add (((quadraticMap c)^[p]) z) (criticalValue c p : ℂ)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (j.return_range c hc).1] at ht
  nlinarith only [he, ht, (j.return_range c hc).2, margin_le_scale C p,
    ThreeLevelMiddle.scale_inside_radius hp.1, scale_pos p]

private theorem outer_phase_displacement (C : TerminalChart) {p : ℕ}
    (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U)
    {z : ℂ} (hz : ‖z‖ ≤ ThreeLevelMiddle.radius p/2)
    (n : ℕ) (hn : 1 ≤ n) (hnp : n < p) :
    ‖((quadraticMap c)^[n]) z-(criticalValue c n : ℂ)‖ ≤ 1/5 :=
  ThreeLevelMiddle.middle_phase_displacement (quadraticMap c) hp.1 j hc 0
    (by norm_num) (by simpa only [zero_mul] using (scale_pos p).le)
    (by intro v hv; simp) hz n hn hnp.le

private theorem outer_pair (C : TerminalChart) {p : ℕ}
    (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U)
    {z w : ℂ} (hz : ‖z‖ ≤ ThreeLevelMiddle.radius p/2)
    (hw : ‖w‖ ≤ ThreeLevelMiddle.radius p/2)
    (n : ℕ) (hn : 1 ≤ n) (hnp : n < p) :
    C.prefixMargin p ≤ ‖((quadraticMap c)^[n]) z+((quadraticMap c)^[n]) w‖ := by
  have h := ThreeLevelReference.pair_norm_lower
    (ThreeLevelReference.outer_phase_abs hp.1 j hc hn hnp)
    (outer_phase_displacement C hp j hc hz n hn hnp)
    (outer_phase_displacement C hp j hc hw n hn hnp)
  nlinarith only [h, margin_le_scale C p, scale_small hp.1]

private theorem outer_first (C : TerminalChart) {p : ℕ}
    (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U)
    {z : ℂ} (hz : ‖z‖ ≤ ThreeLevelMiddle.radius p/2)
    (n : ℕ) (hn : 1 ≤ n) (hnp : n < p) :
    ThreeLevelMiddle.radius p+C.prefixMargin p ≤ ‖((quadraticMap c)^[n]) z‖ := by
  have he := outer_phase_displacement C hp j hc hz n hn hnp
  have hl := ThreeLevelReference.outer_phase_abs hp.1 j hc hn hnp
  have ht := norm_le_norm_sub_add (criticalValue c n : ℂ) (((quadraticMap c)^[n]) z)
  rw [norm_sub_rev, Complex.norm_real, Real.norm_eq_abs] at ht
  nlinarith only [he, hl, ht, ThreeLevelMiddle.radius_small hp.1,
    margin_le_scale C p, scale_small hp.1]

private theorem lifted_radii {C : TerminalChart} {depth : ℕ}
    (A : Ancestors C depth) {p : ℕ} (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U) (i : Fin depth) :
    C.prefixMargin p ≤ A.core i (monicParameter p c)/|returnCoefficient p c| ∧
      A.core i (monicParameter p c)/|returnCoefficient p c| +C.prefixMargin p ≤
        A.barrier i (monicParameter p c)/|returnCoefficient p c| ∧
      A.barrier i (monicParameter p c)/|returnCoefficient p c| +C.prefixMargin p ≤
        A.target i (monicParameter p c)/|returnCoefficient p c| ∧
      A.target i (monicParameter p c)/|returnCoefficient p c| ≤ 1/100 := by
  obtain ⟨hcore, hbarrier, htarget, hmax⟩ := A.radii i _ (j.monic_range hc)
  have hA := coefficient_negative (j.coefficient_lower c hc)
  have ha := abs_pos.mpr hA.ne
  have hm := C.prefix_margin_weighted hp j hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (le_div_iff₀ ha).mpr
    nlinarith only [hm, hcore, C.margin_pos]
  · have hs : A.core i (monicParameter p c)/|returnCoefficient p c| ≤
        A.barrier i (monicParameter p c)/|returnCoefficient p c| -C.prefixMargin p := by
      apply divide_upper C hp j hc
      have he : |returnCoefficient p c| *
          (A.core i (monicParameter p c)/|returnCoefficient p c|) =
          A.core i (monicParameter p c) := by field_simp [ha.ne']
      rw [he]
      linarith only [hbarrier, C.margin_pos]
    linarith only [hs]
  · have hs : A.barrier i (monicParameter p c)/|returnCoefficient p c| ≤
        A.target i (monicParameter p c)/|returnCoefficient p c| -C.prefixMargin p := by
      apply divide_upper C hp j hc
      have he : |returnCoefficient p c| *
          (A.barrier i (monicParameter p c)/|returnCoefficient p c|) =
          A.barrier i (monicParameter p c) := by field_simp [ha.ne']
      rw [he]
      linarith only [htarget, C.margin_pos]
    linarith only [hs]
  · apply (div_le_iff₀ ha).mpr
    nlinarith only [hmax, coefficient_ge_one C hp j hc]

private theorem lifted_orbit {C : TerminalChart} {depth : ℕ}
    (A : Ancestors C depth) {p : ℕ} (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U) (i : Fin depth)
    {z : ℂ} (hz : ‖z‖ ≤ A.barrier i (monicParameter p c)/|returnCoefficient p c|)
    (n : ℕ) (hn : n ≤ A.period i*p) :
    ‖((quadraticMap c)^[n]) z‖ ≤ 21/10 := by
  have hA := coefficient_negative (j.coefficient_lower c hc)
  have hv := scale_input hA.ne hz
  have h := C.prefix_lifted_orbit hp j hc (A.period_lt i).le
    (A.orbit_bound i _ (j.monic_range hc) hv) n hn
  simpa only [scale_input_cancel hA.ne] using h

private theorem lifted_critical {C : TerminalChart} {depth : ℕ}
    (A : Ancestors C depth) {p : ℕ} (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U) (i : Fin depth) :
    ‖((quadraticMap c)^[A.period i*p]) 0‖ ≤
      A.target i (monicParameter p c)/|returnCoefficient p c| -C.prefixMargin p := by
  have hA := coefficient_negative (j.coefficient_lower c hc)
  obtain ⟨hcore, hbarrier, _, _⟩ := A.radii i _ (j.monic_range hc)
  have hz : ‖(0 : ℂ)‖ ≤ A.barrier i (monicParameter p c) := by
    simp only [norm_zero]
    linarith only [hcore, hbarrier, C.margin_pos]
  have he := C.prefix_iterate_error hp j hc (A.period_lt i).le
    (A.orbit_bound i _ (j.monic_range hc) hz) (A.period i) le_rfl
  have href := A.critical_inside i _ (j.monic_range hc)
  have ht := norm_le_norm_sub_add (((outerMap c p)^[A.period i]) 0)
    (((quadraticMap (monicParameter p c))^[A.period i]) 0)
  have hb : ‖((outerMap c p)^[A.period i]) 0‖ ≤
      A.target i (monicParameter p c)-C.margin/2 := by
    linarith [C.budget_le_margin, C.margin_pos]
  rw [coarse_norm hA.ne, zero_div] at hb
  exact divide_upper C hp j hc hb

private theorem lifted_circle {C : TerminalChart} {depth : ℕ}
    (A : Ancestors C depth) {p : ℕ} (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U) (i : Fin depth)
    {z : ℂ} (hz : ‖z‖ = A.barrier i (monicParameter p c)/|returnCoefficient p c|) :
    A.target i (monicParameter p c)/|returnCoefficient p c| +C.prefixMargin p ≤
      ‖((quadraticMap c)^[A.period i*p]) z‖ := by
  have hA := coefficient_negative (j.coefficient_lower c hc)
  have hv := scale_circle hA.ne hz
  have he := C.prefix_iterate_error hp j hc (A.period_lt i).le
    (A.orbit_bound i _ (j.monic_range hc) hv.le) (A.period i) le_rfl
  have href := A.circle_escape i _ (j.monic_range hc) _ hv
  have ht := norm_le_norm_sub_add
    (((quadraticMap (monicParameter p c))^[A.period i]) ((returnCoefficient p c : ℂ)*z))
    (((outerMap c p)^[A.period i]) ((returnCoefficient p c : ℂ)*z))
  rw [norm_sub_rev] at ht
  have hb : A.target i (monicParameter p c)+C.margin/2 ≤
      ‖((outerMap c p)^[A.period i]) ((returnCoefficient p c : ℂ)*z)‖ := by
    linarith [C.budget_le_margin, C.margin_pos]
  rw [coarse_norm hA.ne, scale_input_cancel hA.ne] at hb
  exact divide_lower C hp j hc hb

private theorem lifted_core {C : TerminalChart} {depth : ℕ}
    (A : Ancestors C depth) {p : ℕ} (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U) (i : Fin depth)
    {z : ℂ} (hz : ‖z‖ ≤ A.core i (monicParameter p c)/|returnCoefficient p c|) :
    ‖((quadraticMap c)^[A.period i*p]) z‖ ≤
      A.target i (monicParameter p c)/|returnCoefficient p c| -C.prefixMargin p := by
  have hA := coefficient_negative (j.coefficient_lower c hc)
  have hv := scale_input hA.ne hz
  have hbarrier := (A.radii i _ (j.monic_range hc)).2.1
  have hvb : ‖(returnCoefficient p c : ℂ)*z‖ ≤ A.barrier i (monicParameter p c) := by
    linarith only [hv, hbarrier, C.margin_pos]
  have he := C.prefix_iterate_error hp j hc (A.period_lt i).le
    (A.orbit_bound i _ (j.monic_range hc) hvb) (A.period i) le_rfl
  have href := A.core_inside i _ (j.monic_range hc) hv
  have ht := norm_le_norm_sub_add
    (((outerMap c p)^[A.period i]) ((returnCoefficient p c : ℂ)*z))
    (((quadraticMap (monicParameter p c))^[A.period i]) ((returnCoefficient p c : ℂ)*z))
  have hb : ‖((outerMap c p)^[A.period i]) ((returnCoefficient p c : ℂ)*z)‖ ≤
      A.target i (monicParameter p c)-C.margin/2 := by
    linarith [C.budget_le_margin, C.margin_pos]
  rw [coarse_norm hA.ne, scale_input_cancel hA.ne] at hb
  exact divide_upper C hp j hc hb

private theorem lifted_pair {C : TerminalChart} {depth : ℕ}
    (A : Ancestors C depth) {p : ℕ} (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U) (i : Fin depth)
    {z w : ℂ} (hz : ‖z‖ ≤ A.barrier i (monicParameter p c)/|returnCoefficient p c|)
    (hw : ‖w‖ ≤ A.barrier i (monicParameter p c)/|returnCoefficient p c|)
    (n : ℕ) (hn : 1 ≤ n) (hnp : n < A.period i*p) :
    C.prefixMargin p ≤ ‖((quadraticMap c)^[n]) z+((quadraticMap c)^[n]) w‖ := by
  have hA := coefficient_negative (j.coefficient_lower c hc)
  have hv := scale_input hA.ne hz
  have hu := scale_input hA.ne hw
  have hb := C.prefix_lifted_pair hp j hc (A.period_lt i).le
    (A.orbit_bound i _ (j.monic_range hc) hv)
    (A.orbit_bound i _ (j.monic_range hc) hu)
    (A.pair_bound i _ (j.monic_range hc) hv hu) n hn hnp
  simpa only [scale_input_cancel hA.ne] using hb

private theorem lifted_first {C : TerminalChart} {depth : ℕ}
    (A : Ancestors C depth) {p : ℕ} (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U) (i : Fin depth)
    {z : ℂ} (hz : ‖z‖ ≤ A.barrier i (monicParameter p c)/|returnCoefficient p c|)
    (n : ℕ) (hn : 1 ≤ n) (hnp : n < A.period i*p) :
    A.target i (monicParameter p c)/|returnCoefficient p c| +C.prefixMargin p ≤
      ‖((quadraticMap c)^[n]) z‖ := by
  have hA := coefficient_negative (j.coefficient_lower c hc)
  have hv := scale_input hA.ne hz
  obtain ⟨hc0, hb0, ht0, ht1⟩ := A.radii i _ (j.monic_range hc)
  have htarget : 0 ≤ A.target i (monicParameter p c) := by
    linarith only [hc0, hb0, ht0, C.margin_pos]
  have hfirst : ∀ k : ℕ, 1 ≤ k → k < A.period i →
      A.target i (monicParameter p c)+C.margin/2 ≤
        ‖((quadraticMap (monicParameter p c))^[k]) ((returnCoefficient p c : ℂ)*z)‖ := by
    intro k hk hki
    have hh := A.first_bound i _ (j.monic_range hc) hv k hk hki
    linarith only [hh, C.margin_pos]
  have hb := C.prefix_lifted_first hp j hc (A.period_lt i).le
    (A.orbit_bound i _ (j.monic_range hc) hv) htarget (by linarith only [ht1])
    hfirst n hn hnp
  simpa only [scale_input_cancel hA.ne] using hb

private theorem outer_target_nesting {C : TerminalChart} {depth : ℕ}
    (A : Ancestors C depth) {p : ℕ} (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U) (i : Fin depth) :
    A.target i (monicParameter p c)/|returnCoefficient p c| +C.prefixMargin p ≤
      15*scale p := by
  have ha := abs_pos.mpr (coefficient_negative (j.coefficient_lower c hc)).ne
  have hmax := (A.radii i _ (j.monic_range hc)).2.2.2
  have hlo := (ThreeLevelReference.coefficient_scale_bounds hp.1 j hc).1
  have hb : A.target i (monicParameter p c)/|returnCoefficient p c| ≤ scale p/15 := by
    apply (div_le_iff₀ ha).mpr
    nlinarith only [hmax, hlo]
  nlinarith only [hb, margin_le_scale C p, scale_pos p]

private theorem lifted_target_nesting {C : TerminalChart} {depth : ℕ}
    (A : Ancestors C depth) {p : ℕ} (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U)
    (i k : Fin depth) (hik : i.val < k.val) :
    A.target k (monicParameter p c)/|returnCoefficient p c| +C.prefixMargin p ≤
      A.core i (monicParameter p c)/|returnCoefficient p c| := by
  have ha := abs_pos.mpr (coefficient_negative (j.coefficient_lower c hc)).ne
  have hh := A.target_nesting i k hik _ (j.monic_range hc)
  apply divide_lower C hp j hc
  have he : |returnCoefficient p c| *
      (A.core i (monicParameter p c)/|returnCoefficient p c|) =
      A.core i (monicParameter p c) := by field_simp [ha.ne']
  rw [he]
  linarith only [hh, C.margin_pos]

private theorem outer_nesting {C : TerminalChart} {depth : ℕ}
    (A : Ancestors C depth) {p : ℕ} (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U) (i : Fin depth)
    {z : ℂ} (hz : ‖z‖ ≤ A.barrier i (monicParameter p c)/|returnCoefficient p c|)
    (m : ℕ) (hm : m ≤ A.period i) :
    ‖((quadraticMap c)^[m*p]) z‖ ≤ 15*scale p-C.prefixMargin p := by
  have hA := coefficient_negative (j.coefficient_lower c hc)
  have hv := scale_input hA.ne hz
  have hb := C.prefix_coarse_bound hp j hc (A.period_lt i).le
    (A.orbit_bound i _ (j.monic_range hc) hv) m hm
  rw [scale_input_cancel hA.ne] at hb
  nlinarith only [hb, margin_le_scale C p, scale_pos p]

private theorem lifted_nesting {C : TerminalChart} {depth : ℕ}
    (A : Ancestors C depth) {p : ℕ} (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U)
    (i k : Fin depth) (hik : i.val < k.val)
    {z : ℂ} (hz : ‖z‖ ≤ A.barrier k (monicParameter p c)/|returnCoefficient p c|)
    (m : ℕ) (hm : m*A.period i ≤ A.period k) :
    ‖((quadraticMap c)^[m*(A.period i*p)]) z‖ ≤
      A.core i (monicParameter p c)/|returnCoefficient p c| -C.prefixMargin p := by
  have hA := coefficient_negative (j.coefficient_lower c hc)
  have hv := scale_input hA.ne hz
  have he := C.prefix_iterate_error hp j hc (A.period_lt k).le
    (A.orbit_bound k _ (j.monic_range hc) hv) (m*A.period i) hm
  have href := A.nesting i k hik _ (j.monic_range hc) hv m hm
  have ht := norm_le_norm_sub_add
    (((outerMap c p)^[m*A.period i]) ((returnCoefficient p c : ℂ)*z))
    (((quadraticMap (monicParameter p c))^[m*A.period i]) ((returnCoefficient p c : ℂ)*z))
  have hb : ‖((outerMap c p)^[m*A.period i]) ((returnCoefficient p c : ℂ)*z)‖ ≤
      A.core i (monicParameter p c)-C.margin/2 := by
    linarith [C.budget_le_margin, C.margin_pos]
  rw [coarse_norm hA.ne, scale_input_cancel hA.ne] at hb
  have hphys := divide_upper C hp j hc hb
  simpa only [Nat.mul_assoc] using hphys

private theorem outer_terminal_nesting (C : TerminalChart) {p : ℕ}
    (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U)
    {z : ℂ} (hz : ‖z‖ ≤ 23/20+C.buffer/2) (m : ℕ) (hm : m ≤ C.period) :
    ‖((quadraticMap c)^[m*p]) ((criticalValue c (C.period*p) : ℂ)*z)‖ ≤
      15*scale p-C.prefixMargin p := by
  have hb := C.prefix_coarse_bound hp j hc le_rfl
    (C.prefix_moving_model hp j hc hz) m hm
  rw [C.prefix_input_identity j hc] at hb
  nlinarith only [hb, margin_le_scale C p, scale_pos p]

private theorem lifted_terminal_nesting {C : TerminalChart} {depth : ℕ}
    (A : Ancestors C depth) {p : ℕ} (hp : C.AdmissiblePrefix p) {L U c : ℝ}
    (j : OuterChart p C.left C.right L U) (hc : c ∈ Icc L U) (i : Fin depth)
    {z : ℂ} (hz : ‖z‖ ≤ 23/20+C.buffer/2) (m : ℕ) (hm : m*A.period i ≤ C.period) :
    ‖((quadraticMap c)^[m*(A.period i*p)]) ((criticalValue c (C.period*p) : ℂ)*z)‖ ≤
      A.core i (monicParameter p c)/|returnCoefficient p c| -C.prefixMargin p := by
  have hA := coefficient_negative (j.coefficient_lower c hc)
  obtain ⟨hw, hid⟩ := C.prefix_moving_input hp j hc hz
  have href := A.terminal_nesting i _ (j.monic_range hc) hw m hm
  rw [hid] at href
  have he := C.prefix_iterate_error hp j hc le_rfl
    (C.prefix_moving_model hp j hc hz) (m*A.period i) hm
  have ht := norm_le_norm_sub_add
    (((outerMap c p)^[m*A.period i]) ((secondScale c p C.period : ℂ)*z))
    (((quadraticMap (monicParameter p c))^[m*A.period i]) ((secondScale c p C.period : ℂ)*z))
  have hb : ‖((outerMap c p)^[m*A.period i]) ((secondScale c p C.period : ℂ)*z)‖ ≤
      A.core i (monicParameter p c)-C.margin/2 := by
    linarith [C.budget_le_margin, C.margin_pos]
  rw [coarse_norm hA.ne, C.prefix_input_identity j hc] at hb
  have hphys := divide_upper C hp j hc hb
  simpa only [Nat.mul_assoc] using hphys

private theorem cancel_period {p m n : ℕ} (hp : 0 < p)
    (h : m*p ≤ n*p) : m ≤ n := by
  by_contra! hh
  have hm := Nat.mul_lt_mul_of_pos_right hh hp
  omega

/-- Prefixing a sufficiently long actual outer return preserves every
ancestor estimate and adds a new outer level. No domain or collision
conclusion is assumed: only the numerical chart data is transported. -/
def prepend {C : TerminalChart} {depth : ℕ} (A : Ancestors C depth)
    (p : ℕ) (hp : C.AdmissiblePrefix p) {L U : ℝ}
    (j : OuterChart p C.left C.right L U) :
    Ancestors (C.prepend p hp j) (depth+1) := by
  have hp0 : 0 < p := by have := hp.1; omega
  refine {
    period := Fin.cases p (fun i => A.period i*p)
    target := Fin.cases (fun _ => ThreeLevelMiddle.radius p)
      (fun i c => A.target i (monicParameter p c)/|returnCoefficient p c|)
    barrier := Fin.cases (fun _ => ThreeLevelMiddle.radius p/2)
      (fun i c => A.barrier i (monicParameter p c)/|returnCoefficient p c|)
    core := Fin.cases (fun _ => 15*scale p)
      (fun i c => A.core i (monicParameter p c)/|returnCoefficient p c|)
    period_ge := ?_
    period_divides := ?_
    period_lt := ?_
    period_order := ?_
    barrier_eq_half := ?_
    radii := ?_
    orbit_bound := ?_
    critical_inside := ?_
    circle_escape := ?_
    core_inside := ?_
    pair_bound := ?_
    first_bound := ?_
    target_nesting := ?_
    nesting := ?_
    terminal_nesting := ?_ }
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact hp.1
    · change 17 ≤ A.period i*p
      have hm := Nat.mul_le_mul_right p (A.period_ge i)
      nlinarith only [hm, hp.1]
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · change p ∣ C.period*p
      exact ⟨C.period, by ring⟩
    · change A.period i*p ∣ C.period*p
      obtain ⟨m, hm⟩ := A.period_divides i
      exact ⟨m, by rw [hm]; ring⟩
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · change p < C.period*p
      have hm := Nat.mul_lt_mul_of_pos_right
        (show 1 < C.period by have := C.period_ge; omega) hp0
      simpa only [one_mul] using hm
    · exact Nat.mul_lt_mul_of_pos_right (A.period_lt i) hp0
  · intro i k
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun k => ?_) k
      · intro hik
        have hh : (0 : ℕ) < 0 := hik
        omega
      · intro _
        have hm := Nat.mul_lt_mul_of_pos_right
          (show 1 < A.period k by have := A.period_ge k; omega) hp0
        simpa only [one_mul] using hm
    · refine Fin.cases ?_ (fun k => ?_) k
      · intro hik
        have hh : i.val+1 < 0 := hik
        omega
      · intro hik
        exact Nat.mul_lt_mul_of_pos_right (A.period_order i k (by omega)) hp0
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro c
      rfl
    · intro c
      change A.barrier i (monicParameter p c)/|returnCoefficient p c| =
        (A.target i (monicParameter p c)/|returnCoefficient p c|)/2
      rw [A.barrier_eq_half]
      ring
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro c hc
      exact outer_radii C hp
    · intro c hc
      exact lifted_radii A hp j hc i
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro c hc z hz n hn
      exact ThreeLevelMiddle.reference_half_disk hp.1 j hc hz n hn
    · intro c hc z hz n hn
      exact lifted_orbit A hp j hc i hz n hn
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro c hc
      exact outer_critical C hp j hc
    · intro c hc
      exact lifted_critical A hp j hc i
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro c hc z hz
      exact outer_circle C hp j hc hz
    · intro c hc z hz
      exact lifted_circle A hp j hc i hz
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro c hc z hz
      exact outer_core C hp j hc hz
    · intro c hc z hz
      exact lifted_core A hp j hc i hz
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro c hc z w hz hw n hn hnp
      exact outer_pair C hp j hc hz hw n hn hnp
    · intro c hc z w hz hw n hn hnp
      exact lifted_pair A hp j hc i hz hw n hn hnp
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro c hc z hz n hn hnp
      exact outer_first C hp j hc hz n hn hnp
    · intro c hc z hz n hn hnp
      exact lifted_first A hp j hc i hz n hn hnp
  · intro i k
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun k => ?_) k
      · intro hik
        have hh : (0 : ℕ) < 0 := hik
        omega
      · intro _ c hc
        exact outer_target_nesting A hp j hc k
    · refine Fin.cases ?_ (fun k => ?_) k
      · intro hik
        have hh : i.val+1 < 0 := hik
        omega
      · intro hik c hc
        exact lifted_target_nesting A hp j hc i k (by omega)
  · intro i k
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun k => ?_) k
      · intro hik
        have hh : (0 : ℕ) < 0 := hik
        omega
      · intro _ c hc z hz m hm
        exact outer_nesting A hp j hc k hz m (cancel_period hp0 hm)
    · refine Fin.cases ?_ (fun k => ?_) k
      · intro hik
        have hh : i.val+1 < 0 := hik
        omega
      · intro hik c hc z hz m hm
        have hm' : m*A.period i ≤ A.period k := by
          apply cancel_period hp0
          simpa only [Nat.mul_assoc] using hm
        exact lifted_nesting A hp j hc i k (by omega) hz m hm'
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro c hc z hz m hm
      exact outer_terminal_nesting C hp j hc hz m (cancel_period hp0 hm)
    · intro c hc z hz m hm
      have hm' : m*A.period i ≤ C.period := by
        apply cancel_period hp0
        simpa only [Nat.mul_assoc] using hm
      exact lifted_terminal_nesting A hp j hc i hz m hm'

/-- The explicit prefix construction supplies the complete enlarged
ancestor invariant, with no additional geometric hypotheses. -/
theorem exists_prefix {C : TerminalChart} {depth : ℕ} (A : Ancestors C depth)
    (p : ℕ) (hp : C.AdmissiblePrefix p) {L U : ℝ}
    (j : OuterChart p C.left C.right L U) :
    Nonempty (Ancestors (C.prepend p hp j) (depth+1)) :=
  ⟨A.prepend p hp j⟩

end
end DepthGate.Ancestors
