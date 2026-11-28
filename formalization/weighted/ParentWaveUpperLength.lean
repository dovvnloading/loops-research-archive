import ParentWaveUpperBoundary
import ParentWaveLocalLength
import ParentWaveTraceLength
import ParentWaveTraceEndpoints

/-!
# The physical elliptic length on arbitrary closed-upper traces

The local holomorphic boundary continuations control Hausdorff length.
Only the three branch points are removed inside the proof; their source
and image sets are finite and therefore have zero one-dimensional measure.
No rectifiability, simplicity, or avoidance of the real axis is assumed.
-/

namespace ParentWaveUpperLength

open Set Complex Metric MeasureTheory Measure Filter
open MarkedSlitTransport SlitWaveModulus ParentWaveElliptic
open ParentWaveUpperBoundary ParentWaveLocalLength ParentWaveTraceLength
open ParentWaveTraceEndpoints
open scoped ENNReal NNReal Topology

noncomputable section

theorem measurable_upperDensity (a b c : ℝ) :
    Measurable (fun z => ENNReal.ofReal ‖upperDifferential a b c z‖) := by
  have hm : Measurable (fun z : ℂ => ENNReal.ofReal
      (Real.sqrt ‖((z-(a:ℂ))*(z-(b:ℂ))*(z-(c:ℂ)))⁻¹‖)) := by
    fun_prop
  convert hm using 1
  funext z
  rw [← upperDifferential_norm_sq a b c z, Real.sqrt_sq (norm_nonneg _)]

theorem local_bound_closed_upper (a b c : ℝ) {F E : ℂ → ℂ}
    (hF : ∀ z ∈ upperHalfPlane, HasDerivAt F (upperDifferential a b c z) z)
    (hE : ContinuousOn E (closure upperHalfPlane))
    (hFE : EqOn F E upperHalfPlane)
    (k : ℝ≥0) (hk : 1 < k) {z : ℂ} (hz : z ∈ closure upperHalfPlane)
    (hn : (z-(a:ℂ))*(z-(b:ℂ))*(z-(c:ℂ)) ≠ 0) :
    ∃ V : Set ℂ, ∃ K : ℝ≥0, IsOpen V ∧ z ∈ V ∧
      LipschitzOnWith K E (V ∩ closure upperHalfPlane) ∧
      ∀ w ∈ V ∩ closure upperHalfPlane,
        (K : ℝ≥0∞) ≤ (k : ℝ≥0∞) * ENNReal.ofReal ‖upperDifferential a b c w‖ := by
  obtain ⟨r,hr,H,hH,hEH,hder⟩ := exists_local_extension a b c hF hE hFE hn
  have hdz : deriv H z ≠ 0 := (hder z ⟨hz,mem_ball_self hr⟩).2.2
  have hc : ContinuousOn (deriv H) (ball z r) := (hH.deriv isOpen_ball).continuousOn
  have hevent : {w | w ∈ ball z r ∧ deriv H w ≠ 0} ∈ 𝓝 z :=
    inter_mem (isOpen_ball.mem_nhds (mem_ball_self hr))
      ((hc.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hr))).eventually_ne hdz)
  obtain ⟨s,hs,hsub⟩ := Metric.mem_nhds_iff.mp hevent
  have hsr : ball z s ⊆ ball z r := fun w hw => (hsub hw).1
  obtain ⟨V,K,hVo,hzV,hLip,hbound⟩ := local_bound_of_hasDeriv isOpen_ball
    (fun w hw => ((hH w (hsr hw)).differentiableAt
      (isOpen_ball.mem_nhds (hsr hw))).hasDerivAt)
    (hc.mono hsr) (fun w hw => (hsub hw).2) k hk (mem_ball_self hs)
  refine ⟨V ∩ ball z r,K,hVo.inter isOpen_ball,⟨hzV,mem_ball_self hr⟩,?_,?_⟩
  · intro x hx y hy
    rw [hEH ⟨hx.2,hx.1.2⟩,hEH ⟨hy.2,hy.1.2⟩]
    exact hLip hx.1.1 hy.1.1
  · intro w hw
    simpa only [(hder w ⟨hw.2,hw.1.2⟩).2.1] using hbound w hw.1.1

theorem hausdorff_image_le_upperLength (a b c : ℝ) {F E : ℂ → ℂ}
    (hF : ∀ z ∈ upperHalfPlane, HasDerivAt F (upperDifferential a b c z) z)
    (hE : ContinuousOn E (closure upperHalfPlane))
    (hFE : EqOn F E upperHalfPlane) {S : Set ℂ}
    (hS : S ⊆ closure upperHalfPlane) :
    μH[1] (E '' S) ≤
      lineLength (fun z => ENNReal.ofReal ‖upperDifferential a b c z‖) S := by
  let A : Set ℂ := {(a:ℂ),(b:ℂ),(c:ℂ)}
  have himage : E '' (S \ A) ⊆ E '' S := image_mono sdiff_subset
  have hfinite : (E '' S \ E '' (S \ A)).Finite := by
    apply ((Set.toFinite A).image E).subset
    rintro w ⟨⟨z,hz,rfl⟩,hnot⟩
    have hzA : z ∈ A := by
      by_contra h
      exact hnot ⟨z,⟨hz,h⟩,rfl⟩
    exact ⟨z,hzA,rfl⟩
  have heq : μH[1] (E '' S) = μH[1] (E '' (S \ A)) := by
    simpa [lineLength] using lineLength_eq_of_finite_diff (fun _ => 1) himage hfinite
  rw [heq]
  have hlocal := hausdorff_image_le_integral_of_localOn
    isClosed_closure.measurableSet (sdiff_subset.trans hS) (measurable_upperDensity a b c)
    (f := E) (S := S \ A)
  apply (hlocal ?_).trans
    (lintegral_mono_set (f := fun z => ENNReal.ofReal ‖upperDifferential a b c z‖)
      sdiff_subset)
  intro k hk z hz
  have hza : z ≠ (a:ℂ) := by
    intro h
    exact hz.2 (by simp [A,h])
  have hzb : z ≠ (b:ℂ) := by
    intro h
    exact hz.2 (by simp [A,h])
  have hzc : z ≠ (c:ℂ) := by
    intro h
    exact hz.2 (by simp [A,h])
  exact local_bound_closed_upper a b c hF hE hFE k hk (hS hz.1)
    (mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hza) (sub_ne_zero.mpr hzb))
      (sub_ne_zero.mpr hzc))

/-- Endpoint displacement is controlled by the literal canonical trace
length for every continuous curve in the closed upper half-plane. -/
theorem canonical_endpoint_distance_le_upperLength (a b c : ℝ) {F E : ℂ → ℂ}
    (hF : ∀ z ∈ upperHalfPlane, HasDerivAt F (upperDifferential a b c z) z)
    (hE : ContinuousOn E (closure upperHalfPlane))
    (hFE : EqOn F E upperHalfPlane) (γ : Curve)
    (hγ : trace γ ⊆ closure upperHalfPlane) :
    ENNReal.ofReal ‖E (γ terminal)-E (γ initial)‖ ≤
      lineLength (fun z => ENNReal.ofReal ‖upperDifferential a b c z‖) (trace γ) := by
  have hc : IsPreconnected (E '' trace γ) :=
    (trace_isPreconnected γ).image E (hE.mono hγ)
  have hd := edist_le_hausdorff_of_isPreconnected hc
    (mem_image_of_mem E (show γ terminal ∈ trace γ from ⟨terminal,rfl⟩))
    (mem_image_of_mem E (show γ initial ∈ trace γ from ⟨initial,rfl⟩))
  have hd' : ENNReal.ofReal ‖E (γ terminal)-E (γ initial)‖ ≤ μH[1] (E '' trace γ) := by
    simpa only [edist_dist,dist_eq_norm] using hd
  exact hd'.trans (hausdorff_image_le_upperLength a b c hF hE hFE hγ)

theorem upperMap_endpoint_distance_le_upperLength (a b c : ℝ) {G E : ℂ → ℂ}
    (hG : ∀ t ∈ quadrant, HasDerivAt G (differential (b-a) (c-a) t) t)
    (hE : ContinuousOn E (closure upperHalfPlane))
    (hGE : EqOn (upperMap a G) E upperHalfPlane) (γ : Curve)
    (hγ : trace γ ⊆ closure upperHalfPlane) :
    ENNReal.ofReal ‖E (γ terminal)-E (γ initial)‖ ≤
      lineLength (fun z => ENNReal.ofReal ‖upperDifferential a b c z‖) (trace γ) :=
  canonical_endpoint_distance_le_upperLength a b c
    (fun _ hz => upperMap_hasDeriv a b c hG hz) hE hGE γ hγ

end
end ParentWaveUpperLength

