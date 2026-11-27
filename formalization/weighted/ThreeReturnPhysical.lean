import ThreeReturnCollar

/-!
# The physical map and its three separated phase domains

The fixed normalized component is transported to the original dynamical
plane.  The map in the physical conclusions is the complete iterate of
`z ↦ z²+c`; its fibers, image, and gap are proved directly.  The phase
separation estimates hold on the entire outer disk before restriction.
-/

namespace ThreeReturnPhysical

open Set Function Metric Topology
open LimitingCrestQuadraticReturn LoopsQuadraticCylinderCensus
open ThreeReturnDomain ThreeReturnDegree ThreeReturnCollar
open ThreeReturnEstimates NearTwoTip NearTwoShooting

noncomputable section

theorem physical_zero {c : ℝ} {p : ℕ} (hc : CanonicalCollar c p) :
    (0 : ℂ) ∈ physicalSource c p :=
  ⟨0, hc.zero_mem, mul_zero _⟩

theorem collar_critical_value {c : ℝ} {p : ℕ} (hc : CanonicalCollar c p) :
    ‖threeReturn c p 0‖ < 1/6 := by
  simpa using connectedComponentIn_subset
    (threeReturn c p ⁻¹' ball 0 (1/6)) 0 hc.zero_mem

/-- The complete physical iterate covers exactly the prescribed physical
disk, on the canonically selected component. -/
theorem physical_return_image {c : ℝ} {p : ℕ} (hc : CanonicalCollar c p) :
    ((quadraticMap c)^[3*p]) '' physicalSource c p = physicalTarget c p := by
  rw [physicalSource_eq_component c p hc.scale_pos (collar_critical_value hc)]
  let H := (quadraticMap c)^[3*p]
  have hproper : IsProperMap H := quadratic_iterate_proper (c : ℂ) (3*p)
  have hopen : IsOpenMap H := quadratic_iterate_open (c : ℂ) (3*p)
  have h0 : (0 : ℂ) ∈ H ⁻¹' physicalTarget c p := by
    have hz := physical_zero hc
    rw [physicalSource_eq_component c p hc.scale_pos (collar_critical_value hc)] at hz
    exact connectedComponentIn_subset _ _ hz
  exact localized_component_image H (H ⁻¹' physicalTarget c p) (physicalTarget c p)
    hopen hproper.isClosedMap (isOpen_ball.preimage hproper.continuous)
    (convex_ball (0 : ℂ) (criticalValue c p / 6)).isPreconnected
    (fun _ hz => hz) (fun _ hz => hz.2) 0 h0

theorem physical_source_open {c : ℝ} {p : ℕ} (hc : CanonicalCollar c p) :
    IsOpen (physicalSource c p) := by
  have hdC : (criticalValue c p : ℂ) ≠ 0 := by exact_mod_cast hc.scale_pos.ne'
  exact (Homeomorph.mulLeft₀ (criticalValue c p : ℂ) hdC).isOpenMap _ hc.isOpen_source

theorem physical_source_connected {c : ℝ} {p : ℕ} (hc : CanonicalCollar c p) :
    IsConnected (physicalSource c p) :=
  hc.isConnected_source.image _ (continuous_const.mul continuous_id).continuousOn

theorem physical_compact_closure {c : ℝ} {p : ℕ} (hc : CanonicalCollar c p) :
    IsCompact (closure (physicalSource c p)) :=
  (isCompact_closedBall (0 : ℂ) (3 * criticalValue c p / 20)).of_isClosed_subset
    isClosed_closure (hc.physical_closure_inside.trans ball_subset_closedBall)

/-- The strict physical gap is a fixed fraction of the actual critical
value scale; it is not an unspecified smaller neighborhood. -/
theorem physical_gap {c : ℝ} {p : ℕ} (hc : CanonicalCollar c p)
    {u v : ℂ} (hu : u ∈ closure (physicalSource c p))
    (hv : v ∉ physicalTarget c p) :
    criticalValue c p / 60 < dist u v := by
  have hu' : ‖u‖ < 3 * criticalValue c p / 20 := by
    simpa using hc.physical_closure_inside hu
  have hv' : criticalValue c p / 6 ≤ ‖v‖ := by simpa [physicalTarget] using hv
  have hnorm := norm_sub_norm_le v u
  rw [dist_eq_norm, norm_sub_rev]
  linarith

/-- Scaling transports the signed sheets without changing the complete
physical iterate or assigning it a degree. -/
theorem physical_collision_iff (c : ℝ) (p : ℕ)
    (hd : 0 < criticalValue c p)
    (hcollision : ∀ {z w : ℂ}, z ∈ source c p → w ∈ source c p →
      (threeReturn c p z = threeReturn c p w ↔ z = w ∨ z = -w))
    {z w : ℂ} (hz : z ∈ physicalSource c p) (hw : w ∈ physicalSource c p) :
    ((quadraticMap c)^[3*p]) z = ((quadraticMap c)^[3*p]) w ↔ z = w ∨ z = -w := by
  obtain ⟨u, hu, rfl⟩ := hz
  obtain ⟨v, hv, rfl⟩ := hw
  have hdC : (criticalValue c p : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [← normalized_iterate_scale c p hd.ne' 3 u,
    ← normalized_iterate_scale c p hd.ne' 3 v]
  constructor
  · intro he
    have hsame : threeReturn c p u = threeReturn c p v := mul_left_cancel₀ hdC he
    rcases (hcollision hu hv).mp hsame with heq | heq
    · exact Or.inl (congrArg (fun t : ℂ => (criticalValue c p : ℂ) * t) heq)
    · right
      simp only [heq, mul_neg]
  · rintro (he | he)
    · have huv : u = v := mul_left_cancel₀ hdC he
      rw [huv]
    · have huv : u = -v := mul_left_cancel₀ hdC (by simpa only [mul_neg] using he)
      have hsame := (hcollision hu hv).mpr (Or.inr huv)
      exact congrArg (fun t : ℂ => (criticalValue c p : ℂ) * t) hsame

theorem physical_source_symmetric (c : ℝ) (p : ℕ) (hp : 0 < p)
    (hc : CanonicalCollar c p) : ∀ z ∈ physicalSource c p, -z ∈ physicalSource c p := by
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨-z, source_symmetric c p hp (collar_critical_value hc) z hz, mul_neg _ _⟩

/-- Exact physical fiber cardinality, with the critical value separated
from all regular target values. -/
theorem physical_fiber_ncard (c : ℝ) (p : ℕ) (hp : 0 < p)
    (hc : CanonicalCollar c p)
    (hcollision : ∀ {z w : ℂ}, z ∈ source c p → w ∈ source c p →
      (threeReturn c p z = threeReturn c p w ↔ z = w ∨ z = -w))
    {y : ℂ} (hy : y ∈ physicalTarget c p) :
    {z : ℂ | z ∈ physicalSource c p ∧ ((quadraticMap c)^[3*p]) z = y}.ncard =
      if y = ((quadraticMap c)^[3*p]) 0 then 1 else 2 := by
  exact fiber_ncard ((quadraticMap c)^[3*p]) (physicalSource c p) (physicalTarget c p)
    (physical_zero hc) (physical_collision_iff c p hc.scale_pos hcollision)
    (physical_source_symmetric c p hp hc)
    (by simp only [SurjOn, physical_return_image hc, Subset.refl]) hy

/-- Whole-disk phase bounds give three pairwise disjoint domains. -/
theorem separated_phase_images (F : ℂ → ℂ) (a : ℝ)
    (ha : a ∈ Icc (-4/5 : ℝ) (-3/4))
    (hphase : ∀ z : ℂ, ‖z‖ ≤ 1/6 →
      ‖F z - 1‖ < 3/50 ∧ ‖F (F z) - (a : ℂ)‖ < 19/100) :
    Disjoint (ball (0 : ℂ) (1/6)) (F '' ball 0 (1/6)) ∧
    Disjoint (ball (0 : ℂ) (1/6)) ((F^[2]) '' ball 0 (1/6)) ∧
    Disjoint (F '' ball (0 : ℂ) (1/6)) ((F^[2]) '' ball 0 (1/6)) := by
  have hfirst {z : ℂ} (hz : z ∈ ball (0 : ℂ) (1/6)) : 47/50 < (F z).re := by
    have hn : ‖z‖ ≤ 1/6 := (mem_ball_zero_iff.mp hz).le
    have hbound := (hphase z hn).1
    have hre := (abs_le.mp (Complex.abs_re_le_norm (F z - 1))).1
    simp only [Complex.sub_re, Complex.one_re] at hre
    linarith
  have hsecond {z : ℂ} (hz : z ∈ ball (0 : ℂ) (1/6)) : (F (F z)).re < -14/25 := by
    have hn : ‖z‖ ≤ 1/6 := (mem_ball_zero_iff.mp hz).le
    have hbound := (hphase z hn).2
    have hre := (abs_le.mp (Complex.abs_re_le_norm (F (F z) - (a : ℂ)))).2
    simp only [Complex.sub_re, Complex.ofReal_re] at hre
    linarith [ha.2]
  refine ⟨disjoint_left.mpr ?_, disjoint_left.mpr ?_, disjoint_left.mpr ?_⟩
  · rintro z hz ⟨w, hw, rfl⟩
    have hn : ‖F w‖ < 1/6 := mem_ball_zero_iff.mp hz
    have hre := (abs_le.mp (Complex.abs_re_le_norm (F w))).2
    linarith [hfirst hw]
  · rintro z hz ⟨w, hw, rfl⟩
    have hn : ‖F (F w)‖ < 1/6 := mem_ball_zero_iff.mp hz
    have hre := (abs_le.mp (Complex.abs_re_le_norm (F (F w)))).1
    linarith [hsecond hw]
  · rintro z ⟨u, hu, rfl⟩ ⟨v, hv, he⟩
    have he' : F (F v) = F u := he
    have hlow := hfirst hu
    have hhigh := hsecond hv
    rw [he'] at hhigh
    linarith

/-- The canonical source and its two later phase domains are already
disjoint at the fixed chosen scale. -/
theorem actual_phase_domains_disjoint {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    Disjoint (source c p) (normalizedReturn c p '' source c p) ∧
    Disjoint (source c p) ((normalizedReturn c p)^[2] '' source c p) ∧
    Disjoint (normalizedReturn c p '' source c p)
      ((normalizedReturn c p)^[2] '' source c p) := by
  have hcanonical := actual_canonical_collar hp hc
  have hsub : source c p ⊆ ball (0 : ℂ) (1/6) := by
    intro z hz
    have hn : ‖z‖ < 3/20 := by simpa using hcanonical.closure_inside (subset_closure hz)
    rw [mem_ball_zero_iff]
    linarith
  have hphases := separated_phase_images (normalizedReturn c p) (1 - kappa p c)
    (by
      have hk := hc.2.2.2.1
      change 17903/10000 ≤ kappa p c ∧ kappa p c ≤ 17904/10000 at hk
      constructor <;> linarith)
    (by
      intro z hz
      have hb := actual_phase_bounds hp hc hz
      exact ⟨by linarith [hb.1], hb.2.1⟩)
  exact ⟨hphases.1.mono hsub (image_mono hsub),
    hphases.2.1.mono hsub (image_mono hsub),
    hphases.2.2.mono (image_mono hsub) (image_mono hsub)⟩

end
end ThreeReturnPhysical
