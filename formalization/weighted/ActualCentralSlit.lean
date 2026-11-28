import ActualThreeReturnNormalization
import ParabolicSegment

/-!
# Exact inverse slit for the complete actual three-return

The slit is the orbit-defined central interval.  Its image, every inverse
point in the complete control disk, and membership in the canonical source
are proved directly for the actual polynomial.
-/

namespace ActualCentralSlit

open Set Function Metric
open LimitingCrestQuadraticReturn NearTwoTip GlobalCrestSourceGates
open ActualThreeReturnNormalization ThreeReturnDomain ThreeReturnDegree
open ThreeReturnCollar ThreeReturnRealization LoopsParabolic

noncomputable section

theorem third_zero {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    threeReturn c p 0 = -(centralRadius c p : ℂ) := by
  simpa only [centralRadius, Complex.ofReal_neg, neg_neg, threeReturn,
    Complex.ofReal_zero] using (actualOrbit_cast c 0 p 3).symm

theorem third_endpoint {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    threeReturn c p (centralRadius c p : ℂ) = (centralRadius c p : ℂ) := by
  have h := (critical_signed_orbit c p (by omega) hc.2.1.ne'
    hc.2.2.2.2.1).2
  rw [third_zero hp hc] at h
  simpa only [neg_neg] using h

theorem slit_norm_le {p : ℕ} {c : ℝ} {z : ℂ}
    (hz : z ∈ realSegment (centralRadius c p)) :
    ‖z‖ ≤ centralRadius c p := by
  obtain ⟨x, hx, rfl⟩ := hz
  simpa only [Complex.norm_real, Real.norm_eq_abs] using abs_le.mpr hx

/-- The actual return preserves the whole orbit interval. -/
theorem slit_invariant {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    MapsTo (threeReturn c p) (realSegment (centralRadius c p))
      (realSegment (centralRadius c p)) := by
  rintro z ⟨x, hx, rfl⟩
  have ht := centralRadius_pos hp hc
  have hunit : x / centralRadius c p ∈ Icc (-1 : ℝ) 1 := by
    constructor
    · apply (le_div_iff₀ ht).mpr
      nlinarith only [hx.1]
    · apply (div_le_iff₀ ht).mpr
      nlinarith only [hx.2]
  have hv := (centralMap_square_bounds hp hc).mapsTo hunit
  have hin : centralRadius c p * (x / centralRadius c p) = x := by
    field_simp [ht.ne']
  change -1 ≤ -actualOrbit c p
      (centralRadius c p * (x / centralRadius c p)) 3 / centralRadius c p ∧
    -actualOrbit c p (centralRadius c p * (x / centralRadius c p)) 3 /
      centralRadius c p ≤ 1 at hv
  rw [hin] at hv
  have hl := (le_div_iff₀ ht).mp hv.1
  have hu := (div_le_iff₀ ht).mp hv.2
  refine ⟨actualOrbit c p x 3, ⟨?_, ?_⟩, actualOrbit_cast c x p 3⟩
  · nlinarith only [hu]
  · nlinarith only [hl]

/-- Every point of the orbit interval has a positive real inverse point
for the literal complete return. -/
theorem slit_positive_preimage {p : ℕ} (hp : 17 ≤ p) {c y : ℝ}
    (hc : ActualTip p c) (hy : y ∈ Icc (-centralRadius c p) (centralRadius c p)) :
    ∃ x ∈ Icc (0 : ℝ) (centralRadius c p),
      threeReturn c p (x : ℂ) = (y : ℂ) := by
  have ht := centralRadius_pos hp hc
  have hzero : actualOrbit c p 0 3 = -centralRadius c p := by
    simp only [centralRadius, neg_neg]
  have hend : actualOrbit c p (centralRadius c p) 3 = centralRadius c p := by
    apply Complex.ofReal_injective
    rw [actualOrbit_cast]
    exact third_endpoint hp hc
  have hy' : y ∈ Icc (actualOrbit c p 0 3)
      (actualOrbit c p (centralRadius c p) 3) := by
    rwa [hzero, hend]
  obtain ⟨x, hx, hxy⟩ :=
    (isPreconnected_Icc : IsPreconnected (Icc (0 : ℝ) (centralRadius c p))).intermediate_value
      (show (0 : ℝ) ∈ Icc 0 (centralRadius c p) from ⟨le_rfl, ht.le⟩)
      (show centralRadius c p ∈ Icc (0 : ℝ) (centralRadius c p) from ⟨ht.le, le_rfl⟩)
      (actualOrbit_differentiable c p 3).continuous.continuousOn hy'
  refine ⟨x, hx, ?_⟩
  change ((normalizedReturn c p)^[3]) (x : ℂ) = (y : ℂ)
  rw [← actualOrbit_cast]
  exact congrArg (fun r : ℝ => (r : ℂ)) hxy

/-- No additional complex inverse slit occurs anywhere in the full
control disk, including points outside the selected source component. -/
theorem inverse_slit_iff {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : ‖z‖ ≤ 1/6) :
    threeReturn c p z ∈ realSegment (centralRadius c p) ↔
      z ∈ realSegment (centralRadius c p) := by
  constructor
  · rintro ⟨y, hy, hye⟩
    obtain ⟨x, hx, hxy⟩ := slit_positive_preimage hp hc hy
    have hxn : ‖(x : ℂ)‖ ≤ 1/6 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1]
      linarith [hx.2, (centralRadius_bounds hp hc).2]
    have he : threeReturn c p z = threeReturn c p (x : ℂ) :=
      hye.symm.trans hxy.symm
    rcases (actual_three_return_collision_iff hp hc hz hxn).mp he with h | h
    · rw [h]
      exact ⟨x, ⟨by linarith [hx.1, (centralRadius_pos hp hc)], hx.2⟩, rfl⟩
    · rw [h]
      refine ⟨-x, ⟨by linarith [hx.2], ?_⟩, by simp⟩
      linarith [hx.1, (centralRadius_pos hp hc)]
  · intro hz'
    exact slit_invariant hp hc hz'

/-- The interval is contained in the complete canonical source, not
merely in a surrogate ambient disk. -/
theorem slit_subset_source {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    realSegment (centralRadius c p) ⊆ source c p := by
  intro z hz
  have hzn := slit_norm_le hz
  have him := slit_norm_le (slit_invariant hp hc hz)
  have ht := (centralRadius_bounds hp hc).2
  exact canonical_source_exhaustion c p (by omega) (actual_canonical_collar hp hc)
    (fun hz hw => actual_three_return_collision_iff hp hc hz hw)
    (by linarith) (by linarith)

/-- Every iterate of every point of the actual central slit remains
inside the same canonical source component. -/
theorem slit_orbit_in_source {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : z ∈ realSegment (centralRadius c p))
    (n : ℕ) : ((threeReturn c p)^[n]) z ∈ source c p := by
  apply slit_subset_source hp hc
  induction n with
  | zero => exact hz
  | succ n ih =>
    rw [iterate_succ_apply']
    exact slit_invariant hp hc ih

/-- The exact canonical filled set of the selected three-return
restriction, defined using its actual source component. -/
def filledSource (c : ℝ) (p : ℕ) : Set ℂ :=
  {z | ∀ n : ℕ, ((threeReturn c p)^[n]) z ∈ source c p}

theorem slit_subset_filledSource {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    realSegment (centralRadius c p) ⊆ filledSource c p := by
  intro z hz n
  exact slit_orbit_in_source hp hc hz n

end
end ActualCentralSlit
