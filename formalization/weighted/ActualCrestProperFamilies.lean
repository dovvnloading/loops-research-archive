import ActualCrestWidth
import ActualCrestParentPaths

/-!
# Every curve counted by the actual descendant modulus

Membership in the metric family is related in both directions to its
actual radius and literal polynomial path.  At the classified terminal
radius, every counted curve has real endpoints on the actual slit, its
whole open interior lies above that slit, and it is simple.  Its complete
upper-semicircle ancestors survive the first three restrictions, and the
fourth source restriction removes exactly the designated crossing.

These are statements about physical planar slit domains.  No ideal-boundary
marking, Hubbard-tree identification or native immersion rule is assumed.
-/

namespace ActualCrestProperFamilies

open Set Function Filter
open scoped Topology
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn LimitingCrest
open GlobalCrestCrossing GlobalCrestClassification GlobalCrestSourceGates
open GlobalCrestFinalCut ActualCrestPaths ActualCrestConformalChart
open ActualCrestParentPaths ActualCrestWidth ThreeReturnParent
open CrestConformalModulus CircularCrestModulus

noncomputable section

/-- A complete simple proper arc in the literal physical slit target,
with both endpoint cuts retained in the original dynamical coordinates. -/
structure SlitDescendant (c : ℝ) (p : ℕ) (α : ℝ) (γ : SmoothArc) : Prop where
  initial_mem : γ 0 ∈ physicalTargetSlit c p
  terminal_mem : γ γ.duration ∈ physicalTargetSlit c p
  initial_real : (γ 0).im = 0
  initial_cut : (γ 0).re ∈ Ioo (criticalValue c (6*p)) (criticalValue c p*α)
  terminal_real : (γ γ.duration).im = 0
  terminal_cut : (γ γ.duration).re ∈
    Ioo (criticalValue c (2*p)) (criticalValue c (5*p))
  interior : ∀ t ∈ Ioo 0 γ.duration,
    γ t ∈ physicalSlitTarget c p ∧ 0 < (γ t).im
  simple : InjOn γ (Icc 0 γ.duration)

/-- The predicate quantifies over every curve used in the modulus. -/
def ProperDescendantFamily (c : ℝ) (p : ℕ) (α : ℝ) (Γ : Set SmoothArc) : Prop :=
  ∀ γ ∈ Γ, SlitDescendant c p α γ

private theorem scale_critical_return (c : ℝ) (p n : ℕ)
    (hd : criticalValue c p ≠ 0) :
    criticalValue c p * (((normalizedReturn c p)^[n]) 0).re =
      criticalValue c (n*p) := by
  have h := congrArg Complex.re (normalized_iterate_scale c p hd n 0)
  simpa only [mul_zero, quadratic_iterate_zero, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using h

private theorem scale_actualOrbit_zero (c : ℝ) (p n : ℕ)
    (hd : 0 < criticalValue c p) :
    criticalValue c p * actualOrbit c p 0 n = criticalValue c (n*p) := by
  have h := congrArg Complex.re (actualOrbit_physical c 0 p n hd)
  simpa only [Complex.ofReal_zero, mul_zero, quadratic_iterate_zero,
    Complex.ofReal_re] using h.symm

private theorem angular_initial (F : Family p c) (s : ℝ) :
    CircularCrestEnergy.point center s 0 = qArc F s 0 := by
  rw [qArc_zero]
  simp [CircularCrestEnergy.point, Complex.polarCoord_symm_apply, ActualCrestWidth.center,
    qEndpoint]

private theorem angular_terminal (F : Family p c) {s : ℝ} (hs : s ∈ Radius) :
    CircularCrestEnergy.point center s (angle F s) = qArc F s 1 := by
  rw [angular_point_eq_circlePoint s
    ⟨(angle_bounds F s).1.le, (angle_bounds F s).2⟩, qArc_one F hs]
  have ha := realAngle_mem F s
  have he : Real.cos (angle F s) = realAngle F s :=
    Real.cos_arccos (by linarith [ha.1]) (by linarith [ha.2])
  rw [he]
  simp only [GlobalCrestCrossing.point, Family.point, realAngle, radiusProjection_eq hs]

/-- Every radius strictly below the unique terminal root satisfies the
actual two-sided terminal gate. -/
theorem retained_radius_gate {p : ℕ} (hp : 17 ≤ p) {c r s : ℝ}
    (hc : ActualTip p c) (F : Family p c)
    (hr : r ∈ Ioo (663/10000 : ℝ) (133/2000))
    (hzero : terminal F r = -1) (hs : s ∈ Ioo (1/16 : ℝ) r) :
    terminalGate F s := by
  have hsR : s ∈ Radius := ⟨hs.1.le, by linarith [hs.2, hr.2]⟩
  have hrR : r ∈ Radius := by constructor <;> linarith [hr.1, hr.2]
  have h := actual_terminal_strictAnti hp hc F hsR hrR hs.2
  rw [hzero] at h
  exact ⟨h, actual_upper_gate hp hc F s hsR⟩

/-- Conversely to `every_radius_occurs`, every counted curve has an
actual retained radius and exactly the prescribed original-plane map. -/
theorem descendant_radius {p : ℕ} (hp : 17 ≤ p) {c r : ℝ}
    (hc : ActualTip p c) (F : Family p c) {γ : SmoothArc}
    (hγ : γ ∈ descendants hp hc F r) :
    ∃ s ∈ Ioo (1/16 : ℝ) r, γ.duration = angle F s ∧
      ∀ t : ℝ, γ t = ((quadraticMap c)^[4*p])
        ((criticalValue c p : ℂ)*CircularCrestEnergy.point center s t) := by
  rcases hγ with ⟨δ, hδ, hmem, rfl⟩
  rcases hmem with ⟨s, hs, hT, rfl⟩
  exact ⟨s, hs, rfl, fun t => physicalChart_apply hp hc _⟩

private theorem mapped_circle_proper {p : ℕ} (hp : 17 ≤ p) {c s α : ℝ}
    (hc : ActualTip p c) (hS : StrictSupport c p) (F : Family p c)
    (hs : s ∈ Icc (1/16 : ℝ) (133/2000))
    (hα : α ∈ Ioo (518/1000 : ℝ) (519/1000)) (hg : terminalGate F s)
    (hT : 0 < angle F s)
    (hδ : (circleArc center s (angle F s) hT).LiesIn
      (physicalChart hp hc).homeomorph.source) :
    SlitDescendant c p α
      ((physicalChart hp hc).mapArc (circleArc center s (angle F s) hT) hδ) := by
  let δ := circleArc center s (angle F s) hT
  let γ := (physicalChart hp hc).mapArc δ hδ
  have hsR : s ∈ Radius := ⟨hs.1, by linarith [hs.2]⟩
  have hends := qArc_fourth_endpoints hp hc F hs hα hg
  have hzero : γ 0 = (criticalValue c p : ℂ)*
      ((normalizedReturn c p)^[4]) (qArc F s 0) := by
    change (criticalValue c p : ℂ)*
      ((normalizedReturn c p)^[4]) (CircularCrestEnergy.point center s 0) = _
    rw [angular_initial F s]
  have hend : γ γ.duration = (criticalValue c p : ℂ)*
      ((normalizedReturn c p)^[4]) (qArc F s 1) := by
    change (criticalValue c p : ℂ)*
      ((normalizedReturn c p)^[4]) (CircularCrestEnergy.point center s (angle F s)) = _
    rw [angular_terminal F hsR]
  have hfirst_mem : ((normalizedReturn c p)^[4]) (qArc F s 0) ∈ targetSlit c p := by
    have he : qArc F s 0 = circlePoint s 1 := by simp [qArc]
    rw [he]
    exact (full_arc_endpoint_slits hp hc hs (Or.inr rfl)).2 4 (by omega)
  have hlast_mem : ((normalizedReturn c p)^[4]) (qArc F s 1) ∈ targetSlit c p := by
    have hcrit := sourceSlit_positive_iterate_target hp hc
      (show (0 : ℂ) ∈ sourceSlit by norm_num [sourceSlit]) (m := 5) (by omega)
    exact ⟨hends.2.2.1, hends.2.2.2.1.le, hends.2.2.2.2.le.trans hcrit.2.2⟩
  change SlitDescendant c p α γ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hzero]
    exact ⟨_, hfirst_mem, rfl⟩
  · rw [hend]
    exact ⟨_, hlast_mem, rfl⟩
  · rw [hzero]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      hends.1, mul_zero, zero_mul, add_zero]
  · rw [hzero]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hl := mul_lt_mul_of_pos_left hends.2.1.1 hc.2.1
    have hu := mul_lt_mul_of_pos_left hends.2.1.2 hc.2.1
    rw [scale_actualOrbit_zero c p 6 hc.2.1] at hl
    exact ⟨hl, hu⟩
  · rw [hend]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      hends.2.2.1, mul_zero, zero_mul, add_zero]
  · rw [hend]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    have hl := mul_lt_mul_of_pos_left hends.2.2.2.1 hc.2.1
    have hu := mul_lt_mul_of_pos_left hends.2.2.2.2 hc.2.1
    rw [scale_critical_return c p 2 hc.2.1.ne'] at hl
    rw [scale_critical_return c p 5 hc.2.1.ne'] at hu
    exact ⟨hl, hu⟩
  · intro t ht
    have htπ : t ∈ Icc (0 : ℝ) Real.pi :=
      ⟨ht.1.le, ht.2.le.trans (angle_bounds F s).2⟩
    have hu := cos_mem_open_q_side F ht
    have hu0 : Real.cos t ∈ Icc (-1 : ℝ) 1 :=
      ⟨by linarith [(realAngle_mem F s).1, hu.1], hu.2.le⟩
    have hz := circlePoint_initialDisk hs hu0
    have hi := (q_side_fourfold_signs hp hc hS F hs hu).2.2.2.2
    have hn := (hS (circlePoint s (Real.cos t)) hz).1 4 (by omega)
    have htarget : ((normalizedReturn c p)^[4]) (circlePoint s (Real.cos t)) ∈
        slitTarget c p := by
      refine ⟨by simpa only [Metric.mem_ball, dist_zero_right] using hn, ?_⟩
      intro he
      exact (ne_of_gt hi) he.1
    have he : γ t = (criticalValue c p : ℂ)*
        ((normalizedReturn c p)^[4]) (circlePoint s (Real.cos t)) := by
      change (criticalValue c p : ℂ)*
        ((normalizedReturn c p)^[4]) (CircularCrestEnergy.point center s t) = _
      rw [angular_point_eq_circlePoint s htπ]
    rw [he]
    refine ⟨⟨_, htarget, rfl⟩, ?_⟩
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero] using mul_pos hc.2.1 hi
  · intro t ht u hu he
    have he' : δ t = δ u := (physicalChart hp hc).homeomorph.injOn
      (hδ t ht) (hδ u hu) he
    have htπ : t ∈ Icc (0 : ℝ) Real.pi :=
      ⟨ht.1, ht.2.trans (angle_bounds F s).2⟩
    have huπ : u ∈ Icc (0 : ℝ) Real.pi :=
      ⟨hu.1, hu.2.trans (angle_bounds F s).2⟩
    change CircularCrestEnergy.point center s t = CircularCrestEnergy.point center s u at he'
    rw [angular_point_eq_circlePoint s htπ, angular_point_eq_circlePoint s huπ] at he'
    have hcos := circlePoint_injective (by linarith [hs.1] : 0 < s) he'
    exact Real.strictAntiOn_cos.injOn htπ huπ hcos

/-- Every counted descendant, not merely one selected representative,
has the actual endpoint cuts and a complete simple upper-half-plane
interior in the physical slit domain. -/
theorem descendants_proper {p : ℕ} (hp : 17 ≤ p) {c r α : ℝ}
    (hc : ActualTip p c) (hS : StrictSupport c p) (F : Family p c)
    (hα : α ∈ Ioo (518/1000 : ℝ) (519/1000))
    (hr : r ∈ Ioo (663/10000 : ℝ) (133/2000)) (hzero : terminal F r = -1) :
    ProperDescendantFamily c p α (descendants hp hc F r) := by
  rintro γ ⟨δ, hδ, hmem, rfl⟩
  rcases hmem with ⟨s, hs, hT, rfl⟩
  exact mapped_circle_proper hp hc hS F ⟨hs.1.le, hs.2.le.trans hr.2.le⟩ hα
    (retained_radius_gate hp hc F hr hzero hs) hT hδ

private theorem scale_mem_image_iff {c : ℝ} {p : ℕ}
    (hd : criticalValue c p ≠ 0) (S : Set ℂ) (z : ℂ) :
    (criticalValue c p : ℂ)*z ∈ (fun w : ℂ => (criticalValue c p : ℂ)*w) '' S ↔
      z ∈ S := by
  have hdC : (criticalValue c p : ℂ) ≠ 0 := by exact_mod_cast hd
  constructor
  · rintro ⟨w, hw, he⟩
    exact (mul_left_cancel₀ hdC he) ▸ hw
  · intro hz
    exact ⟨z, hz, rfl⟩

/-- The full physical semicircle associated with any counted curve has
all its source and target memberships accounted for.  The fourth source
deletes one crossing and no additional point of the open semicircle. -/
theorem descendant_full_ancestry {p : ℕ} (hp : 17 ≤ p) {c r : ℝ}
    (hc : ActualTip p c) (hS : StrictSupport c p) (F : Family p c)
    (hr : r ∈ Ioo (663/10000 : ℝ) (133/2000)) (hzero : terminal F r = -1)
    {γ : SmoothArc} (hγ : γ ∈ descendants hp hc F r) :
    ∃ s ∈ Ioo (1/16 : ℝ) r, γ.duration = angle F s ∧
      (∀ t : ℝ, γ t = ((quadraticMap c)^[4*p])
        ((criticalValue c p : ℂ)*CircularCrestEnergy.point center s t)) ∧
      ∀ u ∈ Ioo (-1 : ℝ) 1,
        (∀ m ≤ 2, ((quadraticMap c)^[m*p])
          ((criticalValue c p : ℂ)*circlePoint s u) ∈ physicalSlitSource c p) ∧
        (((quadraticMap c)^[3*p]) ((criticalValue c p : ℂ)*circlePoint s u) ∈
          physicalSlitSource c p ↔ u ≠ realAngle F s) ∧
        (∀ m ∈ Icc (1 : ℕ) 3, ((quadraticMap c)^[m*p])
          ((criticalValue c p : ℂ)*circlePoint s u) ∈ physicalSlitTarget c p) := by
  obtain ⟨s, hs, hduration, hrepresentation⟩ := descendant_radius hp hc F hγ
  have hs' : s ∈ Icc (1/16 : ℝ) (133/2000) := ⟨hs.1.le, hs.2.le.trans hr.2.le⟩
  have hg := retained_radius_gate hp hc F hr hzero hs
  refine ⟨s, hs, hduration, hrepresentation, ?_⟩
  intro u hu
  have hsource := full_arc_source_membership hp hc hS F hs' hg hu
  have htarget := full_arc_target_membership hp hc hS F hs' hg hu
  refine ⟨?_, ?_, ?_⟩
  · intro m hm
    rw [← normalized_iterate_scale c p hc.2.1.ne']
    exact ⟨_, hsource.1 m hm, rfl⟩
  · rw [← normalized_iterate_scale c p hc.2.1.ne', physicalSlitSource,
      scale_mem_image_iff hc.2.1.ne']
    exact hsource.2
  · intro m hm
    rw [← normalized_iterate_scale c p hc.2.1.ne']
    exact ⟨_, htarget m hm, rfl⟩

/-- The same actual family simultaneously has the full geometric
endpoint/interior properties and the proved positive modulus ratio. -/
theorem proper_descendants_and_width {p : ℕ} (hp : 17 ≤ p) {c r α : ℝ}
    (hc : ActualTip p c) (hS : StrictSupport c p) (F : Family p c)
    (hα : α ∈ Ioo (518/1000 : ℝ) (519/1000))
    (hr : r ∈ Ioo (663/10000 : ℝ) (133/2000)) (hzero : terminal F r = -1) :
    ProperDescendantFamily c p α (descendants hp hc F r) ∧
      (1/3 : ℝ) < widthRatio hp hc F r :=
  ⟨descendants_proper hp hc hS F hα hr hzero,
    actual_widthRatio_gt_third hp hc hS F ⟨hr.1.le, hr.2.le⟩⟩

/-- The geometric hypotheses are discharged uniformly over all actual
parameters and all classified endpoint choices after one period threshold. -/
theorem eventually_all_proper_descendants :
    ∀ᶠ n : ℕ in atTop, ∀ c : ℝ, ∀ hc : ActualTip (n+17) c,
      ∀ F : Family (n+17) c, ∀ α ∈ Ioo (518/1000 : ℝ) (519/1000),
        ∀ r ∈ Ioo (663/10000 : ℝ) (133/2000), terminal F r = -1 →
          ProperDescendantFamily c (n+17) α (descendants (by omega) hc F r) ∧
            (1/3 : ℝ) < widthRatio (by omega) hc F r := by
  filter_upwards [eventually_all_strict_support] with n hn
  intro c hc F α hα r hr hzero
  exact proper_descendants_and_width (by omega) hc (hn c hc) F hα hr hzero

end
end ActualCrestProperFamilies
