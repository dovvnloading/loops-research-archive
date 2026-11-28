import ActualCrestConformalChart
import CircularCrestModulus
import CircularParentEnergy
import CircularParentModulus
import GlobalCrestLimit

/-!
# The actual four-return descendant modulus

The family is the image of every selected circular q-side arc under the
literal fourth normalized return, followed by its original complex scale.
The source chart, complete path survival, and all-density conformal
transport are proved separately and combined here. The parent denominator
is independently the full physical circular-family modulus.
-/

namespace ActualCrestWidth

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn LimitingCrest
open GlobalCrestCrossing GlobalCrestClassification GlobalCrestFinalCut
open ActualCrestPaths ActualCrestConformalChart
open CrestConformalModulus CircularCrestModulus

noncomputable section

def center : ℂ := -(3/4 : ℂ)

def angle {p : ℕ} {c : ℝ} (F : Family p c) (s : ℝ) : ℝ :=
  Real.arccos (realAngle F s)

theorem angle_bounds {p : ℕ} {c : ℝ} (F : Family p c) (s : ℝ) :
    0 < angle F s ∧ angle F s ≤ Real.pi :=
  ⟨Real.arccos_pos.mpr (by linarith [(realAngle_mem F s).2]),Real.arccos_le_pi _⟩

theorem angle_continuous {p : ℕ} {c : ℝ} (F : Family p c) : Continuous (angle F) :=
  (realAngle_continuous F).arccos

theorem angular_point_eq_circlePoint (s : ℝ) {t : ℝ} (ht : t ∈ Icc 0 Real.pi) :
    CircularCrestEnergy.point center s t = circlePoint s (Real.cos t) := by
  rw [circlePoint_cos s ht]
  simp [CircularCrestEnergy.point,Complex.polarCoord_symm_apply,center]
  ring

def physicalChart {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) : ConformalChart :=
  (chart hp hc).postScale (criticalValue c p : ℂ) (by exact_mod_cast hc.2.1.ne')

theorem physicalChart_apply {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) (z : ℂ) :
    (physicalChart hp hc).homeomorph z =
      ((quadraticMap c)^[4*p]) ((criticalValue c p : ℂ)*z) :=
  normalized_iterate_scale c p hc.2.1.ne' 4 z

def baseFamily {p : ℕ} {c : ℝ} (F : Family p c) (r : ℝ) : Set SmoothArc :=
  circleFamily center (Ioo (1/16 : ℝ) r) (angle F)

def descendants {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (F : Family p c) (r : ℝ) : Set SmoothArc :=
  (physicalChart hp hc).transportFamily (baseFamily F r)

theorem circular_leaf_in_chart {p : ℕ} (hp : 17 ≤ p) {c s : ℝ}
    (hc : ActualTip p c) (hS : StrictSupport c p) (F : Family p c)
    (hs : s ∈ Icc (1/16 : ℝ) (133/2000)) (hT : 0 < angle F s) :
    (circleArc center s (angle F s) hT).LiesIn (physicalChart hp hc).homeomorph.source := by
  intro t ht
  change CircularCrestEnergy.point center s t ∈ chartSource c p
  rw [angular_point_eq_circlePoint s ⟨ht.1,ht.2.trans (angle_bounds F s).2⟩]
  exact circlePoint_mem_chartSource hp hc hS F hs (cos_mem_closed_q_side F ht)

theorem baseFamily_in_chart {p : ℕ} (hp : 17 ≤ p) {c r : ℝ}
    (hc : ActualTip p c) (hS : StrictSupport c p) (F : Family p c)
    (hr : r ≤ (133/2000 : ℝ)) :
    ∀ γ ∈ baseFamily F r, γ.LiesIn (physicalChart hp hc).homeomorph.source := by
  rintro γ ⟨s,hs,hT,rfl⟩
  exact circular_leaf_in_chart hp hc hS F ⟨hs.1.le,hs.2.le.trans hr⟩ hT

/-- No circle is silently lost by the chart: every retained radius has
its complete literal polynomial image in the descendant family. -/
theorem every_radius_occurs {p : ℕ} (hp : 17 ≤ p) {c r s : ℝ}
    (hc : ActualTip p c) (hS : StrictSupport c p) (F : Family p c)
    (hr : r ≤ (133/2000 : ℝ)) (hs : s ∈ Ioo (1/16 : ℝ) r) :
    ∃ γ ∈ descendants hp hc F r, γ.duration = angle F s ∧
      ∀ t : ℝ, γ t = ((quadraticMap c)^[4*p])
        ((criticalValue c p : ℂ)*CircularCrestEnergy.point center s t) := by
  let γ := circleArc center s (angle F s) (angle_bounds F s).1
  have hγ : γ ∈ baseFamily F r := circleArc_mem_circleFamily hs (angle_bounds F s).1
  have hsource := baseFamily_in_chart hp hc hS F hr γ hγ
  refine ⟨(physicalChart hp hc).mapArc γ hsource,⟨γ,hsource,hγ,rfl⟩,rfl,?_⟩
  intro t
  exact physicalChart_apply hp hc (γ t)

/-- Exact all-density modulus of the actual original-plane images. The
integral appears as a conclusion, not as the definition of their width. -/
theorem descendants_modulus {p : ℕ} (hp : 17 ≤ p) {c r : ℝ}
    (hc : ActualTip p c) (hS : StrictSupport c p) (F : Family p c)
    (hr : r ≤ (133/2000 : ℝ)) :
    modulus (descendants hp hc F r) =
      ∫⁻ s in Ioo (1/16 : ℝ) r, ENNReal.ofReal (1/(s*angle F s)) := by
  exact transport_modulus_eq_radial_integral (physicalChart hp hc)
    measurableSet_Ioo (angle_continuous F).measurable
    (fun s hs => (show (0 : ℝ) < 1/16 by norm_num).trans hs.1)
    (fun s _ => angle_bounds F s) (baseFamily_in_chart hp hc hS F hr)

/-- The denominator is the metric modulus of the original, untrimmed
physical circular parent, not the retained collar. -/
def parentWidth (c : ℝ) (p : ℕ) : ℝ :=
  (CircularParentEnergy.modulus (-((3*criticalValue c p/4 : ℝ) : ℂ))
    (Ioo (criticalValue c p/16) (criticalValue c p*parentOuter p))).toReal

/-- Full physical circles parametrized from q to q through angle 2π.
The boundary point is now at the parameter ends, as required for the
proper parent in the real-slit target. -/
def parentFamily (c : ℝ) (p : ℕ) : Set SmoothArc :=
  circleFamily (-((3*criticalValue c p/4 : ℝ) : ℂ))
    (Ioo (criticalValue c p/16) (criticalValue c p*parentOuter p))
    (fun _ => 2*Real.pi)

theorem parentWidth_eq_modulus {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    parentWidth c p = (modulus (parentFamily c p)).toReal := by
  have h := CircularParentModulus.modulus_eq_parentEnergy
    (m := -((3*criticalValue c p/4 : ℝ) : ℂ))
    (I := Ioo (criticalValue c p/16) (criticalValue c p*parentOuter p))
    (fun ρ hρ => (div_pos hc.2.1 (by norm_num)).trans hρ.1)
  exact (congrArg ENNReal.toReal h).symm

theorem parentWidth_eq {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    parentWidth c p = Real.log (2-2/(p : ℝ))/(2*Real.pi) := by
  have hd := hc.2.1
  have hpR : (17 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hrad : criticalValue c p/16 ≤ criticalValue c p*parentOuter p := by
    have hout := (parentOuter_bounds hp).1
    have h := mul_le_mul_of_nonneg_left (show (1/16 : ℝ) ≤ parentOuter p by linarith) hd.le
    simpa only [div_eq_mul_inv,one_mul] using h
  unfold parentWidth
  rw [CircularParentEnergy.modulus_Ioo_toReal _ (by positivity) hrad]
  congr 2
  unfold parentOuter
  field_simp [hd.ne',hp0.ne']
  ring

theorem parentWidth_pos {p : ℕ} (hp : 17 ≤ p) {c : ℝ} (hc : ActualTip p c) :
    0 < parentWidth c p := by
  rw [parentWidth_eq hp hc]
  exact div_pos (GlobalCrestCoefficient.parent_log_bounds hp).1 (by positivity)

/-- Every full parent circle is in the actual physical central return
and in the archived original component. -/
theorem physical_parent_circle_mem {p : ℕ} (hp : 17 ≤ p) {c ρ : ℝ}
    (hc : ActualTip p c)
    (hρ : ρ ∈ Ioo (criticalValue c p/16) (criticalValue c p*parentOuter p)) (t : ℝ) :
    CircularCrestEnergy.point (-((3*criticalValue c p/4 : ℝ) : ℂ)) ρ t ∈
      ThreeReturnParent.physicalParentSource c p ∩ ThreeReturnParent.archivedParentSource c p := by
  apply GlobalCrestPhysical.physical_fullParentDisk_subset hp hc
  have hρ0 : 0 < ρ := (div_pos hc.2.1 (by norm_num)).trans hρ.1
  have hb := mul_le_mul_of_nonneg_left (parentOuter_bounds hp).2 hc.2.1.le
  change ‖CircularCrestEnergy.point (-((3*criticalValue c p/4 : ℝ) : ℂ)) ρ t +
    ((3*criticalValue c p/4 : ℝ) : ℂ)‖ ≤ criticalValue c p/8
  have he : CircularCrestEnergy.point (-((3*criticalValue c p/4 : ℝ) : ℂ)) ρ t +
      ((3*criticalValue c p/4 : ℝ) : ℂ) = Complex.polarCoord.symm (ρ,t) := by
    unfold CircularCrestEnergy.point
    ring
  rw [he,Complex.norm_polarCoord_symm,abs_of_pos hρ0]
  linarith [hρ.2]

/-- The literal descendant-family modulus, divided by the full physical
circular-parent modulus. This is not a scalar integral definition. -/
def widthRatio {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (F : Family p c) (r : ℝ) : ℝ :=
  (modulus (descendants hp hc F r)).toReal / parentWidth c p

theorem descendants_width_eq_integral {p : ℕ} (hp : 17 ≤ p) {c r : ℝ}
    (hc : ActualTip p c) (hS : StrictSupport c p) (F : Family p c)
    (hr : r ∈ Icc (1/16 : ℝ) (133/2000)) :
    (modulus (descendants hp hc F r)).toReal =
      ∫ s in (1/16 : ℝ)..r, CrestIntegralLimit.radialIntegrand (realAngle F) s := by
  exact toReal_transport_modulus_eq_integral (physicalChart hp hc)
    (by norm_num) hr.1 (angle_continuous F)
    (fun s _ => angle_bounds F s) (baseFamily_in_chart hp hc hS F hr.2)

/-- The archived scalar is now identified with the modulus ratio of the
actual selected physical families. Its physical interpretation is proved. -/
theorem widthRatio_eq_radialCoefficient {p : ℕ} (hp : 17 ≤ p) {c r : ℝ}
    (hc : ActualTip p c) (hS : StrictSupport c p) (F : Family p c)
    (hr : r ∈ Icc (1/16 : ℝ) (133/2000)) :
    widthRatio hp hc F r = CrestIntegralLimit.radialCoefficient p (realAngle F) r := by
  unfold widthRatio
  rw [descendants_width_eq_integral hp hc hS F hr,parentWidth_eq hp hc]
  unfold CrestIntegralLimit.radialCoefficient
  field_simp [(GlobalCrestCoefficient.parent_log_bounds hp).1.ne',Real.pi_pos.ne']

theorem actual_widthRatio_gt_third {p : ℕ} (hp : 17 ≤ p) {c r : ℝ}
    (hc : ActualTip p c) (hS : StrictSupport c p) (F : Family p c)
    (hr : r ∈ Icc (663/10000 : ℝ) (133/2000)) :
    (1/3 : ℝ) < widthRatio hp hc F r := by
  rw [widthRatio_eq_radialCoefficient hp hc hS F ⟨by linarith [hr.1],hr.2⟩]
  exact GlobalCrestCoefficient.actual_radialCoefficient_gt_third hp hc F hr

/-- A single large-period threshold works for every admissible actual
parameter and every classified endpoint; no geometric premise remains. -/
theorem eventually_all_actual_widthRatio_gt_third :
    ∀ᶠ n : ℕ in atTop, ∀ c : ℝ, ∀ hc : ActualTip (n+17) c,
      ∀ F : Family (n+17) c, ∀ r ∈ Icc (663/10000 : ℝ) (133/2000),
        (1/3 : ℝ) < widthRatio (by omega) hc F r := by
  filter_upwards [eventually_all_strict_support] with n hn
  intro c hc F r hr
  exact actual_widthRatio_gt_third (by omega) hc (hn c hc) F hr

/-- The positive limiting coefficient is the limit of actual original-
plane descendant/parent modulus ratios for any sequence of the constructed
parameters and their globally classified terminal endpoints. -/
theorem actual_widthRatios_converge {k₀ : ℝ}
    (hk₀ : k₀ ∈ LoopsLimitingCrestParameter.parameterInterval)
    (hroot : LoopsLimitingCrestParameter.relation k₀ = 0)
    (c : ℕ → ℝ) (hc : ∀ n, ActualTip (n+17) (c n))
    (F : ∀ n, Family (n+17) (c n)) (radii : ℕ → ℝ)
    (hr : ∀ n, radii n ∈ Ioo (663/10000 : ℝ) (133/2000))
    (he : ∀ n, terminal (F n) (radii n) = -1) :
    ∃ r ∈ Ioo (663/10000 : ℝ) (133/2000), crestTerminal k₀ r = -1 ∧
      Tendsto radii atTop (𝓝 r) ∧
      Tendsto (fun n => widthRatio (by omega) (hc n) (F n) (radii n))
        atTop (𝓝 (fullModelCoefficient k₀ r)) ∧
      (1/3 : ℝ) < fullModelCoefficient k₀ r := by
  obtain ⟨r,hr₀,he₀,hrlim,hclim,hpositive⟩ :=
    GlobalCrestLimit.actual_global_coefficients_converge hk₀ hroot c hc F radii hr he
  have heq : (fun n => widthRatio (by omega) (hc n) (F n) (radii n)) =ᶠ[atTop]
      (fun n => CrestIntegralLimit.radialCoefficient (n+17) (realAngle (F n)) (radii n)) := by
    filter_upwards [actual_strict_support c hc] with n hn
    exact widthRatio_eq_radialCoefficient (by omega) (hc n) hn (F n)
      ⟨by linarith [(hr n).1],(hr n).2.le⟩
  exact ⟨r,hr₀,he₀,hrlim,(tendsto_congr' heq).mpr hclim,hpositive⟩

/-- All parameter, crossing-family and terminal-endpoint data exist.
Thus the physical positive modulus limit has no unconstructed dynamical
or analytic inputs. -/
theorem exists_actual_positive_width_limit :
    ∃ c : ℕ → ℝ, ∃ hc : ∀ n, ActualTip (n+17) (c n),
      ∃ F : ∀ n, Family (n+17) (c n), ∃ radii : ℕ → ℝ,
        (∀ n, radii n ∈ Ioo (663/10000 : ℝ) (133/2000) ∧
          terminal (F n) (radii n) = -1) ∧
        (∀ᶠ n in atTop, (1/3 : ℝ) < widthRatio (by omega) (hc n) (F n) (radii n)) ∧
        ∃ k₀ ∈ LoopsLimitingCrestParameter.parameterInterval,
          LoopsLimitingCrestParameter.relation k₀ = 0 ∧
          ∃ r ∈ Ioo (663/10000 : ℝ) (133/2000), crestTerminal k₀ r = -1 ∧
            Tendsto radii atTop (𝓝 r) ∧
            Tendsto (fun n => widthRatio (by omega) (hc n) (F n) (radii n))
              atTop (𝓝 (fullModelCoefficient k₀ r)) ∧
            (1/3 : ℝ) < fullModelCoefficient k₀ r := by
  classical
  choose c hc using fun n : ℕ => exists_actual_tip (n+17) (by omega)
  let F (n : ℕ) : Family (n+17) (c n) :=
    Classical.choice (exists_family (by omega) (hc n))
  choose α hα hfixed radii hr he hanti hunique hcomplete using
    fun n => actual_complete_cut_classification (by omega) (hc n) (F n)
  obtain ⟨k₀,⟨hk₀,hroot⟩,_⟩ := LoopsLimitingCrestParameter.exists_unique_limiting_parameter
  refine ⟨c,hc,F,radii,fun n => ⟨hr n,he n⟩,?_,k₀,hk₀,hroot,?_⟩
  · filter_upwards [eventually_all_actual_widthRatio_gt_third] with n hn
    exact hn (c n) (hc n) (F n) (radii n) ⟨(hr n).1.le,(hr n).2.le⟩
  · exact actual_widthRatios_converge hk₀ hroot c hc F radii hr he

end
end ActualCrestWidth
