import ActualCrestCrossingWindow
import ActualCrestLimit
import LimitingCrestArcGates
import CrestFirstExit
import CrestIterateLimit

/-!
# Maximal initial terminal collars for actual quadratic returns

The radius-dependent crossing is evaluated in the literal polynomial
return. Its terminal gate has a first exit whose whole initial connected
component is identified exactly. The endpoint converges to the previously
constructed model endpoint. No radial monotonicity of the actual return
is postulated.
-/

namespace ActualCrestEndpoint

open Set Function Filter
open scoped Topology
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn LimitingCrest
open LoopsLimitingCrestParameter ActualCrestCrossingWindow

noncomputable section

def radiusProjection (s : ℝ) : Radius :=
  projIcc (1/16 : ℝ) (133/2000) (by norm_num) s

theorem radiusProjection_eq {s : ℝ}
    (hs : s ∈ Icc (1/16 : ℝ) (133/2000)) :
    radiusProjection s = ⟨s, hs⟩ := projIcc_of_mem (by norm_num) hs

def realAngle {p : ℕ} {c : ℝ} (F : Family p c) (s : ℝ) : ℝ :=
  F.angle (radiusProjection s)

def point {p : ℕ} {c : ℝ} (F : Family p c) (s : ℝ) : ℂ :=
  F.point (radiusProjection s)

def terminal {p : ℕ} {c : ℝ} (F : Family p c) (s : ℝ) : ℝ :=
  (((normalizedReturn c p)^[3]) (point F s)).re

theorem realAngle_continuous {p : ℕ} {c : ℝ} (F : Family p c) :
    Continuous (realAngle F) :=
  F.lipschitz.continuous.comp (continuous_projIcc (h := by norm_num))

theorem terminal_continuous {p : ℕ} {c : ℝ} (F : Family p c) :
    Continuous (terminal F) :=
  Complex.continuous_re.comp
    ((normalizedReturn_continuous c p).iterate 3 |>.comp
      (F.point_continuous.comp (continuous_projIcc (h := by norm_num))))

theorem scale_tendsto_zero (C : ℝ) :
    Tendsto (fun n : ℕ => C*scale (n+17)) atTop (𝓝 0) := by
  have hbase : Tendsto (fun n : ℕ => (1/4 : ℝ)^n) atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa only [scale, pow_add, mul_zero, zero_mul] using
    (hbase.mul_const ((1/4 : ℝ)^17)).const_mul C

/-- Every choice of the actual signed-tip parameters has the same
uniform normalized-map limit on the common approximation disk. -/
theorem actual_maps_tendsto {k₀ : ℝ} (hk₀ : k₀ ∈ parameterInterval)
    (hroot : relation k₀ = 0) (c : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n)) :
    TendstoUniformlyOn (fun n => normalizedReturn (c n) (n+17))
      (complexMap k₀) atTop {z : ℂ | ‖z‖ ≤ 23/20} := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have he : ∀ᶠ n : ℕ in atTop, 23646*scale (n+17) < ε :=
    (tendsto_order.mp (scale_tendsto_zero 23646)).2 ε hε
  filter_upwards [he] with n hn
  intro z hz
  rw [dist_comm, dist_eq_norm]
  exact (ActualCrestLimit.actual_tip_limit_map_error (by omega) (hc n)
    hk₀ hroot hz).trans_lt hn

/-- The complete extended radial crossing window converges uniformly
to the explicit radical curve of the limiting polynomial. -/
theorem actual_points_tendsto {k₀ : ℝ} (hk₀ : k₀ ∈ parameterInterval)
    (hroot : relation k₀ = 0) (c : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n))
    (F : ∀ n, Family (n+17) (c n)) :
    TendstoUniformly (fun n s => (F n).point s)
      (fun s : Radius => radialPoint k₀ s) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have he : ∀ᶠ n : ℕ in atTop, 33000*scale (n+17) < ε :=
    (tendsto_order.mp (scale_tendsto_zero 33000)).2 ε hε
  filter_upwards [he] with n hn
  intro s
  rw [dist_comm, dist_eq_norm]
  exact ((F n).point_error (by omega) (hc n) hk₀ hroot s).trans_lt hn

theorem actual_angles_tendsto {k₀ : ℝ} (hk₀ : k₀ ∈ parameterInterval)
    (hroot : relation k₀ = 0) (c : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n))
    (F : ∀ n, Family (n+17) (c n)) :
    TendstoUniformlyOn (fun n => realAngle (F n)) (crossingCos k₀)
      atTop (Icc (1/16 : ℝ) (133/2000)) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have he : ∀ᶠ n : ℕ in atTop, 236460*scale (n+17) < ε :=
    (tendsto_order.mp (scale_tendsto_zero 236460)).2 ε hε
  filter_upwards [he] with n hn
  intro s hs
  let q : Radius := ⟨s, hs⟩
  have hb := ActualCrestCrossingWindow.actual_tip_angle_error (by omega) (hc n)
    hk₀ hroot hs ⟨((F n).angle_mem q).1.le, ((F n).angle_mem q).2.le⟩
    ((F n).crossing q)
  rw [Real.dist_eq, abs_sub_comm]
  simpa only [realAngle, radiusProjection_eq hs] using hb.trans_lt hn

/-- Uniform convergence of all four actual images, with the actual
intermediate domain checks supplied by compactness of the model support. -/
theorem actual_images_tendsto {k₀ : ℝ} (hk₀ : k₀ ∈ parameterInterval)
    (hroot : relation k₀ = 0) (c : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n))
    (F : ∀ n, Family (n+17) (c n)) :
    ∀ m ≤ 4,
      TendstoUniformly
        (fun n s => ((normalizedReturn (c n) (n+17))^[m]) ((F n).point s))
        (fun s : Radius => ((complexMap k₀)^[m]) (radialPoint k₀ s)) atTop ∧
      ∀ᶠ n in atTop, ∀ s : Radius,
        ‖((normalizedReturn (c n) (n+17))^[m]) ((F n).point s)‖ ≤ 23/20 := by
  letI : Nonempty Radius := ⟨⟨1/16, by constructor <;> norm_num⟩⟩
  have hz : Continuous (fun s : Radius => radialPoint k₀ s) := by
    unfold radialPoint radialOrdinateSq radialAbscissa radialDiscriminant
    fun_prop
  have hQ : Continuous (complexMap k₀) := by unfold complexMap; fun_prop
  have hmem (s : Radius) : radialPoint k₀ s ∈ initialDisk := by
    have hs : (s : ℝ) ∈ Icc (1/16 : ℝ) (1/8) :=
      ⟨s.property.1, s.property.2.trans (by norm_num)⟩
    change ‖radialPoint k₀ s+(3/4 : ℂ)‖ ≤ 133/2000
    rw [(radial_model_realization hk₀ hs).1]
    exact s.property.2
  have hR (m : ℕ) (hm : m ≤ 4) (s : Radius) :
      ‖((complexMap k₀)^[m]) (radialPoint k₀ s)‖ < 23/20 :=
    (whole_support_bounds hk₀ (hmem s)).1 m hm
  have hlip (v w : ℂ) (hv : ‖v‖ ≤ 23/20) (hw : ‖w‖ ≤ 23/20) :
      ‖complexMap k₀ v-complexMap k₀ w‖ ≤ 5*‖v-w‖ :=
    LimitingCrestPerturbation.quadratic_disk_lipschitz k₀
      (by linarith [hk₀.1]) (by linarith [hk₀.2]) v w hv hw
  exact CrestIterateLimit.finite_iterates_uniformly 4 hz hQ hR
    (actual_points_tendsto hk₀ hroot c hc F)
    (actual_maps_tendsto hk₀ hroot c hc) hlip

/-- The entire actual terminal function converges uniformly on the
extended interval containing the moving endpoint. -/
theorem actual_terminal_tendsto {k₀ : ℝ} (hk₀ : k₀ ∈ parameterInterval)
    (hroot : relation k₀ = 0) (c : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n))
    (F : ∀ n, Family (n+17) (c n)) :
    TendstoUniformlyOn (fun n => terminal (F n))
      (crestTerminal k₀) atTop (Icc (1/16 : ℝ) (133/2000)) := by
  have h := (actual_images_tendsto hk₀ hroot c hc F 3 (by omega)).1
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp h ε hε] with n hn
  intro s hs
  let q : Radius := ⟨s, hs⟩
  have he := hn q
  have hmodel := (radial_model_realization hk₀
    (show s ∈ Icc (1/16 : ℝ) (1/8) from ⟨hs.1, hs.2.trans (by norm_num)⟩)).2.2.2
  change (complexMap k₀)^[3] (radialPoint k₀ q) = (crestTerminal k₀ s : ℂ) at hmodel
  rw [hmodel, dist_eq_norm] at he
  have hre := (Complex.abs_re_le_norm
    ((crestTerminal k₀ s : ℂ)-((normalizedReturn (c n) (n+17))^[3]) ((F n).point q))).trans_lt he
  simpa only [Real.dist_eq, terminal, point, radiusProjection_eq hs,
    Complex.sub_re, Complex.ofReal_re] using hre

/-- This is the initial connected component of the actual strict gate.
The definition records the literal terminal equality and every earlier
radius, so it cannot be satisfied by an arbitrary later root. -/
def InitialCollar {p : ℕ} {c : ℝ} (F : Family p c) (r : ℝ) : Prop :=
  r ∈ Ioo (1/16 : ℝ) (133/2000) ∧ terminal F r = -1 ∧
  (∀ s ∈ Ico (1/16 : ℝ) r, -1 < terminal F s) ∧
  connectedComponentIn
    (Icc (1/16 : ℝ) (133/2000) ∩ {s | -1 < terminal F s}) (1/16) = Ico (1/16) r

/-- Every actual parameter/curve choice has a convergent sequence of
maximal initial connected collars. Only the limiting radial coordinate
is required to be strictly decreasing. -/
theorem actual_initial_collars_converge {k₀ : ℝ} (hk₀ : k₀ ∈ parameterInterval)
    (hroot : relation k₀ = 0) (c : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n))
    (F : ∀ n, Family (n+17) (c n)) :
    ∃ r ∈ Ioo (663/10000 : ℝ) (133/2000), crestTerminal k₀ r = -1 ∧
      ∃ radii : ℕ → ℝ,
        (∀ n, radii n ∈ Icc (1/16 : ℝ) (133/2000)) ∧
        Tendsto radii atTop (𝓝 r) ∧
        ∀ᶠ n in atTop, InitialCollar (F n) (radii n) := by
  obtain ⟨r, hr, he, _, _⟩ := unique_model_endpoint hk₀
  have hrfull : r ∈ Ioo (1/16 : ℝ) (133/2000) :=
    ⟨(by norm_num : (1/16 : ℝ) < 663/10000).trans hr.1, hr.2⟩
  have hanti : StrictAntiOn (crestTerminal k₀) (Icc (1/16 : ℝ) (133/2000)) :=
    (crestTerminal_strictAnti hk₀).mono (Icc_subset_Icc_right (by norm_num))
  obtain ⟨radii, hlimit, hcollars⟩ := CrestFirstExit.exists_first_exits_converging
    (fun n => terminal (F n)) (crestTerminal k₀)
    (actual_terminal_tendsto hk₀ hroot c hc F) hanti hrfull he
    (Eventually.of_forall (fun n => (terminal_continuous (F n)).continuousOn))
  let ρ : ℕ → ℝ := fun n => radiusProjection (radii n)
  have hρmem (n : ℕ) : ρ n ∈ Icc (1/16 : ℝ) (133/2000) :=
    (radiusProjection (radii n)).property
  have hρlimit : Tendsto ρ atTop (𝓝 r) := by
    have hproj : Continuous (fun s : ℝ => (radiusProjection s : ℝ)) :=
      continuous_subtype_val.comp (continuous_projIcc (h := by norm_num))
    have hh := (hproj.tendsto r).comp hlimit
    simpa only [ρ, Function.comp_def, radiusProjection_eq ⟨hrfull.1.le, hrfull.2.le⟩] using hh
  refine ⟨r, hr, he, ρ, hρmem, hρlimit, ?_⟩
  filter_upwards [hcollars] with n hn
  have hρeq : ρ n = radii n := by
    exact congrArg Subtype.val (radiusProjection_eq ⟨hn.1.1.le, hn.1.2.le⟩)
  simpa only [InitialCollar, hρeq] using hn

/-- The terminal equality is an exact complex equality for the actual
return; it does not merely constrain the real part of an arbitrary point. -/
theorem endpoint_complex_equality {p : ℕ} {c r : ℝ}
    (hp : 0 < p) (F : Family p c) (hr : terminal F r = -1) :
    ((normalizedReturn c p)^[3]) (point F r) = (-1 : ℂ) := by
  apply Complex.ext
  · simpa only [terminal, Complex.neg_re, Complex.one_re] using hr
  · simpa only [point, Complex.neg_im, Complex.one_im, neg_zero] using
      F.third_real hp (radiusProjection r)

/-- A first-exit endpoint gives a literal original-plane polynomial
point on the declared circle whose third return is the negative critical
return value. No identification with a symbolic or model orbit is used. -/
theorem unscaled_endpoint {p : ℕ} {c r : ℝ} (hp : 17 ≤ p)
    (hc : ActualTip p c) (F : Family p c) (hr : InitialCollar F r) :
    ∃ z : ℂ,
      ‖z+((3*criticalValue c p/4 : ℝ) : ℂ)‖ = criticalValue c p*r ∧
      (((quadraticMap c)^[p]) z).re = 0 ∧
      0 < (((quadraticMap c)^[p]) z).im ∧
      ((quadraticMap c)^[3*p]) z = -(criticalValue c p : ℂ) := by
  let d := criticalValue c p
  let q : Radius := ⟨r, hr.1.1.le, hr.1.2.le⟩
  let z : ℂ := (d : ℂ)*F.point q
  have hd : 0 < d := hc.2.1
  have hq : radiusProjection r = q := radiusProjection_eq ⟨hr.1.1.le, hr.1.2.le⟩
  have hnorm := F.point_radius q
  have hscale (m : ℕ) : ((quadraticMap c)^[m*p]) z =
      (d : ℂ)*((normalizedReturn c p)^[m]) (F.point q) :=
    (normalized_iterate_scale c p hd.ne' m (F.point q)).symm
  have hfirst : ((quadraticMap c)^[p]) z = (d : ℂ)*normalizedReturn c p (F.point q) := by
    simpa only [one_mul, iterate_one] using hscale 1
  have hthird : ((normalizedReturn c p)^[3]) (F.point q) = (-1 : ℂ) := by
    simpa only [point, hq] using endpoint_complex_equality (by omega) F hr.2.1
  refine ⟨z, ?_, ?_, ?_, ?_⟩
  · calc
      ‖z+((3*criticalValue c p/4 : ℝ) : ℂ)‖ = ‖(d : ℂ)*(F.point q+(3/4 : ℂ))‖ := by
        congr 1
        dsimp [z, d]
        push_cast
        ring
      _ = d*‖F.point q+(3/4 : ℂ)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
      _ = criticalValue c p*r := by rw [hnorm]
  · rw [hfirst]
    have hz := F.crossing q
    change (normalizedReturn c p (F.point q)).re = 0 at hz
    simpa using congrArg (fun t : ℝ => d*t) hz
  · rw [hfirst]
    have hz := F.positive q
    change 0 < (normalizedReturn c p (F.point q)).im at hz
    simpa using mul_pos hd hz
  · rw [hscale, hthird]
    simp [d]

end
end ActualCrestEndpoint
