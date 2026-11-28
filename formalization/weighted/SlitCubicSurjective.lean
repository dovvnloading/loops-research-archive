import SlitCubicUnivalence
import SlitCubicRectangle
import Mathlib.Analysis.Calculus.Deriv.Inverse
import SlitCubicBoundaryRange
import SlitCubicImaginaryBoundary
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Connected.Clopen

/-!
# Surjectivity of the cubic primitive onto its period rectangle

Uniform decay at infinity and the exact boundary values prevent preimages
of interior rectangle points from escaping. The image is open and relatively
closed in the connected rectangle.
-/

namespace SlitCubicSurjective

open Set Filter Function MeasureTheory
open SlitCubicCalibration SlitCubicUnivalence SlitCubicBoundary SlitCubicBoundaryRange
open scoped Topology
noncomputable section

theorem tail_image_isOpen_of_subset {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {s : Set ℂ} (hs : s ⊆ upper) (hsopen : IsOpen s) :
    IsOpen (tail a b c '' s) := by
  have hd : DifferentiableOn ℂ (tail a b c) upper := fun z hz =>
    (tail_hasDerivAt (realDensity_integrable hab hbc) hz).differentiableAt.differentiableWithinAt
  rcases (hd.analyticOnNhd upper_open).is_constant_or_isOpen upper_convex.isPreconnected with h | h
  · obtain ⟨w,hw⟩ := h
    have hI : Complex.I ∈ upper := by simp [upper]
    have h2I : 2*Complex.I ∈ upper := by simp [upper]
    have heq := tail_injOn_upper hab hbc hI h2I ((hw _ hI).trans (hw _ h2I).symm)
    have him := congrArg Complex.im heq
    norm_num at him
  · exact h s hs hsopen

theorem tail_image_isOpen {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    IsOpen (tail a b c '' upper) :=
  tail_image_isOpen_of_subset hab hbc subset_rfl upper_open

/-- Every limiting image value with positive real part, distinct from all
real boundary values, has a preimage in the open upper half-plane. -/
theorem mem_image_of_closure_of_boundary_avoidance {a b c : ℝ}
    (hab : a < b) (hbc : b < c) {w : ℂ} (hwre : 0 < w.re)
    (hboundary : ∀ x : ℝ, tail a b c (x:ℂ) ≠ w)
    (hcl : w ∈ closure (tail a b c '' upper)) :
    w ∈ tail a b c '' upper := by
  have hi := realDensity_integrable hab hbc
  obtain ⟨v,hv,hvconv⟩ := mem_closure_iff_seq_limit.mp hcl
  choose z hz hzv using hv
  have hδ : 0 < w.re/2 := half_pos hwre
  obtain ⟨R,hR,hdecay⟩ := tail_uniform_decay hi hδ
  have hvre : ∀ᶠ n in atTop, w.re/2 < (v n).re :=
    (Complex.continuous_re.tendsto w |>.comp hvconv).eventually
      (Ioi_mem_nhds (by linarith))
  have hzb : ∀ᶠ n in atTop, z n ∈ Metric.closedBall (0:ℂ) R := by
    filter_upwards [hvre] with n hn
    have hnot : ¬R ≤ ‖z n‖ := by
      intro hlarge
      have hb := hdecay (z n) (by simpa [closedUpper] using (show 0 < (z n).im from hz n).le) hlarge
      rw [hzv n] at hb
      have hr := Complex.re_le_norm (v n)
      linarith
    simpa only [Metric.mem_closedBall, dist_zero_right] using (lt_of_not_ge hnot).le
  obtain ⟨z₀,hz₀,φ,hφ,hconv⟩ := (isCompact_closedBall (0:ℂ) R).tendsto_subseq' hzb.frequently
  have hclosed : IsClosed closedUpper := isClosed_le continuous_const Complex.continuous_im
  have hseq : ∀ᶠ n in atTop, (z ∘ φ) n ∈ closedUpper :=
    Eventually.of_forall (fun n => by
      simpa [closedUpper] using (show 0 < (z (φ n)).im from hz (φ n)).le)
  have hz₀upper : z₀ ∈ closedUpper := hclosed.mem_of_tendsto hconv hseq
  have hwithin : Tendsto (z ∘ φ) atTop (𝓝[closedUpper] z₀) :=
    tendsto_nhdsWithin_iff.mpr ⟨hconv,hseq⟩
  have hfconv := Filter.Tendsto.comp (tail_continuousOn_closedUpper hi z₀ hz₀upper) hwithin
  have hvconv' : Tendsto (fun n => tail a b c ((z ∘ φ) n)) atTop (𝓝 w) := by
    simpa only [Function.comp_def, hzv] using hvconv.comp hφ.tendsto_atTop
  have heq : tail a b c z₀ = w := tendsto_nhds_unique hfconv hvconv'
  have hz₀pos : z₀ ∈ upper := by
    change 0 < z₀.im
    have hn : 0 ≤ z₀.im := hz₀upper
    by_contra hnot
    have him : z₀.im = 0 := le_antisymm (le_of_not_gt hnot) hn
    have he : z₀ = (z₀.re:ℂ) := by apply Complex.ext <;> simp [him]
    rw [he] at heq
    exact hboundary z₀.re heq
  exact ⟨z₀,hz₀pos,heq⟩


private theorem boundary_avoidance {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {w : ℂ} (hw : 0 < w.re ∧ w.re < period a b c ∧ -height a b c < w.im ∧ w.im < 0) :
    ∀ x : ℝ, tail a b c (x:ℂ) ≠ w := by
  intro x heq
  have hre := congrArg Complex.re heq
  have him := congrArg Complex.im heq
  by_cases hxa : x ≤ a
  · rw [tail_re_left hab hbc hxa] at hre
    linarith [hw.1]
  have hax : a < x := lt_of_not_ge hxa
  by_cases hxb : x ≤ b
  · rw [tail_im_first hab hbc hax.le hxb] at him
    linarith [hw.2.2.1]
  have hbx : b < x := lt_of_not_ge hxb
  by_cases hxc : x ≤ c
  · rw [tail_re_gap hab hbc hbx.le hxc] at hre
    linarith [hw.2.1]
  · rw [tail_im_right hab hbc (le_of_not_ge hxc)] at him
    linarith [hw.2.2.2]

private theorem surjOn_of_mapsTo_rectangle {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {R : Set ℂ} (hR : Convex ℝ R) (hmap : MapsTo (tail a b c) upper R)
    (hrect : ∀ w ∈ R,
      0 < w.re ∧ w.re < period a b c ∧ -height a b c < w.im ∧ w.im < 0) :
    SurjOn (tail a b c) upper R := by
  have hclosure : closure (tail a b c '' upper) ∩ R ⊆ tail a b c '' upper := by
    intro w hw
    exact mem_image_of_closure_of_boundary_avoidance hab hbc (hrect w hw.2).1
      (boundary_avoidance hab hbc (hrect w hw.2)) hw.1
  have hdisj : Disjoint (tail a b c '' upper) (closure (tail a b c '' upper))ᶜ := by
    exact disjoint_left.mpr (fun w hw hc => hc (subset_closure hw))
  have hcover : R ⊆ (tail a b c '' upper) ∪ (closure (tail a b c '' upper))ᶜ := by
    intro w hw
    by_cases hc : w ∈ closure (tail a b c '' upper)
    · exact Or.inl (hclosure ⟨hc,hw⟩)
    · exact Or.inr hc
  have hI : Complex.I ∈ upper := by simp [upper]
  have hnonempty : (R ∩ (tail a b c '' upper)).Nonempty :=
    ⟨tail a b c Complex.I,hmap hI,Complex.I,hI,rfl⟩
  exact hR.isPreconnected.subset_left_of_subset_union (tail_image_isOpen hab hbc)
    isClosed_closure.isOpen_compl hdisj hcover hnonempty


/-- The actual cubic tail covers every point of its exact period rectangle. -/
theorem tail_surjOn_openRectangle {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    SurjOn (tail a b c) upper
      (SlitCubicRectangle.openRectangle (period a b c) (height a b c)) := by
  apply surjOn_of_mapsTo_rectangle hab hbc (SlitCubicRectangle.openRectangle_convex _ _)
    (fun z hz => SlitCubicRectangle.tail_mem_openRectangle hab hbc hz)
  intro w hw
  exact hw

/-- Exact image identification, including both inclusion and surjectivity. -/
theorem tail_image_eq_openRectangle {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    tail a b c '' upper =
      SlitCubicRectangle.openRectangle (period a b c) (height a b c) := by
  apply Subset.antisymm
  · rintro w ⟨z,hz,rfl⟩
    exact SlitCubicRectangle.tail_mem_openRectangle hab hbc hz
  · exact tail_surjOn_openRectangle hab hbc

private theorem tail_restrict_isOpenMap {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    IsOpenMap (upper.restrict (tail a b c)) := by
  intro s hs
  have hopen : IsOpen (Subtype.val '' s : Set ℂ) :=
    upper_open.isOpenEmbedding_subtypeVal.isOpenMap s hs
  have hsub : (Subtype.val '' s : Set ℂ) ⊆ upper := by
    rintro z ⟨w,hw,rfl⟩
    exact w.property
  change IsOpen ((fun x : upper => tail a b c (x:ℂ)) '' s)
  simpa only [image_image, Function.comp_def] using tail_image_isOpen_of_subset hab hbc hsub hopen

/-- The explicitly integrated tail, bundled with its actual inverse as
an open partial homeomorphism of the complex plane. -/
def rectangleChart {a b c : ℝ} (hab : a < b) (hbc : b < c) : OpenPartialHomeomorph ℂ ℂ :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict
    ((show BijOn (tail a b c) upper
      (SlitCubicRectangle.openRectangle (period a b c) (height a b c)) from
        ⟨(fun z hz => SlitCubicRectangle.tail_mem_openRectangle hab hbc hz),
          tail_injOn_upper hab hbc, tail_surjOn_openRectangle hab hbc⟩).toPartialEquiv
      (tail a b c) upper (SlitCubicRectangle.openRectangle (period a b c) (height a b c)))
    ((tail_continuousOn_closedUpper (realDensity_integrable hab hbc)).mono
      (fun z hz => by simpa [closedUpper] using (show 0 < z.im from hz).le))
    (tail_restrict_isOpenMap hab hbc) upper_open

@[simp] theorem rectangleChart_source {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    (rectangleChart hab hbc).source = upper := rfl

@[simp] theorem rectangleChart_target {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    (rectangleChart hab hbc).target =
      SlitCubicRectangle.openRectangle (period a b c) (height a b c) := rfl

@[simp] theorem rectangleChart_apply {a b c : ℝ} (hab : a < b) (hbc : b < c) (z : ℂ) :
    rectangleChart hab hbc z = tail a b c z := rfl

private theorem differential_ne_zero {a b c : ℝ} {z : ℂ} (hz : z ∈ upper) :
    differential a b c z ≠ 0 := by
  have hn (t : ℝ) : z ≠ (t:ℂ) := by
    intro he
    have hm := congrArg Complex.im he
    have hy : 0 < z.im := hz
    simp only [Complex.ofReal_im] at hm
    linarith
  have hy : 0 ≤ z.im := (show 0 < z.im from hz).le
  exact inv_ne_zero (mul_ne_zero (mul_ne_zero (upperRoot_ne_zero hy (hn a))
    (upperRoot_ne_zero hy (hn b))) (upperRoot_ne_zero hy (hn c)))

/-- The inverse chart has the reciprocal of the actual cubic derivative. -/
theorem rectangleChart_symm_hasDerivAt {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {w : ℂ} (hw : w ∈ SlitCubicRectangle.openRectangle (period a b c) (height a b c)) :
    HasDerivAt (rectangleChart hab hbc).symm
      (-(upperRoot a ((rectangleChart hab hbc).symm w) *
        upperRoot b ((rectangleChart hab hbc).symm w) *
        upperRoot c ((rectangleChart hab hbc).symm w))) w := by
  have hz : (rectangleChart hab hbc).symm w ∈ upper :=
    (rectangleChart hab hbc).map_target hw
  have hd := (rectangleChart hab hbc).hasDerivAt_symm hw
    (neg_ne_zero.mpr (differential_ne_zero hz))
    (tail_hasDerivAt (realDensity_integrable hab hbc) hz)
  simpa only [differential, inv_neg, inv_inv] using hd

end
end SlitCubicSurjective
