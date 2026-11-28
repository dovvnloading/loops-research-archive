import SlitCubicSurjective
import SlitCubicEdges
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Compactness.Compact

/-!
# The cubic inverse on closed horizontal segments

The two vertical edges of the actual period rectangle have unique real
preimages. Uniform decay prevents inverse images of points away from the
horizontal edges from escaping to infinity, so the interior inverse extends
continuously across both vertical edges.
-/

namespace SlitCubicClosedChart

open Set Filter Function
open SlitCubicCalibration SlitCubicBoundary SlitCubicBoundaryRange
open SlitCubicRectangle SlitCubicSurjective SlitCubicEdges SlitCubicUnivalence
open scoped Topology
noncomputable section

def closedHorizontalBand (B A : ℝ) : Set ℂ :=
  {w | 0 ≤ w.re ∧ w.re ≤ B ∧ -A < w.im ∧ w.im < 0}

def closedSource (a b c : ℝ) : Set ℂ :=
  closedUpper ∩ tail a b c ⁻¹' closedHorizontalBand (period a b c) (height a b c)

def closedInverse (a b c : ℝ) : ℂ → ℂ :=
  invFunOn (tail a b c) (closedSource a b c)

theorem openRectangle_subset_closedHorizontalBand (B A : ℝ) :
    openRectangle B A ⊆ closedHorizontalBand B A :=
  fun _ hw => ⟨hw.1.le, hw.2.1.le, hw.2.2⟩

theorem upper_subset_closedSource {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    upper ⊆ closedSource a b c := by
  intro z hz
  exact ⟨(show 0 < z.im from hz).le,
    openRectangle_subset_closedHorizontalBand _ _ (tail_mem_openRectangle hab hbc hz)⟩

theorem real_left_mem_closedSource {a b c x : ℝ} (hab : a < b) (hbc : b < c)
    (hx : x < a) : (x : ℂ) ∈ closedSource a b c := by
  refine ⟨by simp [closedUpper], ?_⟩
  have him := tail_im_mem_Ioo_left hab hbc hx
  change 0 ≤ (tail a b c (x : ℂ)).re ∧ (tail a b c (x : ℂ)).re ≤ period a b c ∧ _
  rw [tail_re_left hab hbc hx.le]
  exact ⟨le_rfl, (period_pos hab hbc).le, him⟩

theorem real_gap_mem_closedSource {a b c x : ℝ} (hab : a < b) (hbc : b < c)
    (hx : x ∈ Ioo b c) : (x : ℂ) ∈ closedSource a b c := by
  refine ⟨by simp [closedUpper], ?_⟩
  have him := tail_im_mem_Ioo_gap hab hbc hx
  change 0 ≤ (tail a b c (x : ℂ)).re ∧ (tail a b c (x : ℂ)).re ≤ period a b c ∧ _
  rw [tail_re_gap hab hbc hx.1.le hx.2.le]
  exact ⟨(period_pos hab hbc).le, le_rfl, him⟩

theorem real_closedSource_cases {a b c x : ℝ} (hab : a < b) (hbc : b < c)
    (hx : (x : ℂ) ∈ closedSource a b c) : x < a ∨ x ∈ Ioo b c := by
  by_cases hxa : x < a
  · exact Or.inl hxa
  have hax : a ≤ x := le_of_not_gt hxa
  by_cases hxb : x ≤ b
  · have him := tail_im_first hab hbc hax hxb
    have hh := hx.2.2.2.1
    rw [him] at hh
    exact (lt_irrefl _ hh).elim
  have hbx : b < x := lt_of_not_ge hxb
  by_cases hxc : x < c
  · exact Or.inr ⟨hbx, hxc⟩
  · have him := tail_im_right hab hbc (le_of_not_gt hxc)
    have hh := hx.2.2.2.2
    rw [him] at hh
    exact (lt_irrefl _ hh).elim

private theorem real_tail_injOn_edges {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    InjOn (fun x : ℝ => tail a b c (x : ℂ)) (Iio a ∪ Ioo b c) := by
  intro x hx y hy heq
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact (tail_im_strictAntiOn_left hab hbc).injOn hx hy (congrArg Complex.im heq)
  · have hr := congrArg Complex.re heq
    rw [tail_re_left hab hbc hx.le, tail_re_gap hab hbc hy.1.le hy.2.le] at hr
    exact ((period_pos hab hbc).ne hr).elim
  · have hr := congrArg Complex.re heq
    rw [tail_re_gap hab hbc hx.1.le hx.2.le, tail_re_left hab hbc hy.le] at hr
    exact ((period_pos hab hbc).ne' hr).elim
  · exact (tail_im_strictMonoOn_gap hab hbc).injOn hx hy (congrArg Complex.im heq)

private theorem real_source_re_cases {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {z : ℂ} (hz : z ∈ closedSource a b c) (him : z.im = 0) :
    (tail a b c z).re = 0 ∨ (tail a b c z).re = period a b c := by
  have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [him]
  rw [he] at hz ⊢
  rcases real_closedSource_cases hab hbc hz with hx | hx
  · exact Or.inl (tail_re_left hab hbc hx.le)
  · exact Or.inr (tail_re_gap hab hbc hx.1.le hx.2.le)

theorem tail_injOn_closedSource {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    InjOn (tail a b c) (closedSource a b c) := by
  intro z hz w hw heq
  by_cases hzpos : 0 < z.im
  · by_cases hwpos : 0 < w.im
    · exact tail_injOn_upper hab hbc hzpos hwpos heq
    · have hwzero : w.im = 0 := le_antisymm (le_of_not_gt hwpos) hw.1
      have hr := congrArg Complex.re heq
      rcases real_source_re_cases hab hbc hw hwzero with hzero | hperiod
      · have hp := tail_re_pos hab hbc hzpos
        rw [hr, hzero] at hp
        exact (lt_irrefl _ hp).elim
      · have hp := tail_re_lt_period hab hbc hzpos
        rw [hr, hperiod] at hp
        exact (lt_irrefl _ hp).elim
  · have hzzero : z.im = 0 := le_antisymm (le_of_not_gt hzpos) hz.1
    by_cases hwpos : 0 < w.im
    · have hr := congrArg Complex.re heq
      rcases real_source_re_cases hab hbc hz hzzero with hzero | hperiod
      · have hp := tail_re_pos hab hbc hwpos
        rw [← hr, hzero] at hp
        exact (lt_irrefl _ hp).elim
      · have hp := tail_re_lt_period hab hbc hwpos
        rw [← hr, hperiod] at hp
        exact (lt_irrefl _ hp).elim
    · have hwzero : w.im = 0 := le_antisymm (le_of_not_gt hwpos) hw.1
      have hez : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hzzero]
      have hew : w = (w.re : ℂ) := by apply Complex.ext <;> simp [hwzero]
      rw [hez] at hz
      rw [hew] at hw
      rw [hez, hew] at heq ⊢
      exact congrArg (fun x : ℝ => (x : ℂ))
        (real_tail_injOn_edges hab hbc (real_closedSource_cases hab hbc hz)
          (real_closedSource_cases hab hbc hw) heq)

theorem tail_surjOn_closedHorizontalBand {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    SurjOn (tail a b c) (closedSource a b c)
      (closedHorizontalBand (period a b c) (height a b c)) := by
  intro w hw
  by_cases hzero : w.re = 0
  · obtain ⟨x, hx, hfx⟩ := exists_left_edge_preimage hab hbc hw.2.2
    have heq : tail a b c (x : ℂ) = w := by
      rw [hfx]
      apply Complex.ext <;> simp [hzero]
    exact ⟨(x : ℂ), ⟨by simp [closedUpper], by simpa only [mem_preimage, heq] using hw⟩, heq⟩
  by_cases hperiod : w.re = period a b c
  · obtain ⟨x, hx, hfx⟩ := exists_gap_edge_preimage hab hbc hw.2.2
    have heq : tail a b c (x : ℂ) = w := by
      rw [hfx]
      apply Complex.ext <;> simp [hperiod]
    exact ⟨(x : ℂ), ⟨by simp [closedUpper], by simpa only [mem_preimage, heq] using hw⟩, heq⟩
  have hwopen : w ∈ openRectangle (period a b c) (height a b c) :=
    ⟨lt_of_le_of_ne hw.1 (Ne.symm hzero), lt_of_le_of_ne hw.2.1 hperiod, hw.2.2⟩
  obtain ⟨z, hz, heq⟩ := tail_surjOn_openRectangle hab hbc hwopen
  exact ⟨z, upper_subset_closedSource hab hbc hz, heq⟩

theorem closedInverse_mem_source {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {w : ℂ} (hw : w ∈ closedHorizontalBand (period a b c) (height a b c)) :
    closedInverse a b c w ∈ closedSource a b c :=
  (tail_surjOn_closedHorizontalBand hab hbc).mapsTo_invFunOn hw

theorem tail_closedInverse {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {w : ℂ} (hw : w ∈ closedHorizontalBand (period a b c) (height a b c)) :
    tail a b c (closedInverse a b c w) = w :=
  (tail_surjOn_closedHorizontalBand hab hbc).rightInvOn_invFunOn hw

theorem closedInverse_tail {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {z : ℂ} (hz : z ∈ closedSource a b c) :
    closedInverse a b c (tail a b c z) = z :=
  (tail_injOn_closedSource hab hbc).leftInvOn_invFunOn hz

theorem closedInverse_injOn {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    InjOn (closedInverse a b c) (closedHorizontalBand (period a b c) (height a b c)) := by
  intro w hw v hv heq
  have h := congrArg (tail a b c) heq
  simpa only [tail_closedInverse hab hbc hw, tail_closedInverse hab hbc hv] using h

/-- Inverse images of a neighborhood of each point in the band remain in
a compact part of the closed upper half-plane. -/
private theorem closedInverse_eventually_bounded {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {w : ℂ} (hw : w ∈ closedHorizontalBand (period a b c) (height a b c)) :
    ∃ R : ℝ, ∀ᶠ v in 𝓝[closedHorizontalBand (period a b c) (height a b c)] w,
      closedInverse a b c v ∈ Metric.closedBall (0 : ℂ) R := by
  have hε : 0 < -w.im / 2 := by linarith [hw.2.2.2]
  obtain ⟨R, hR, hdecay⟩ := tail_uniform_decay (realDensity_integrable hab hbc) hε
  refine ⟨R, ?_⟩
  have him : ∀ᶠ v in 𝓝[closedHorizontalBand (period a b c) (height a b c)] w,
      v.im < w.im / 2 :=
    (Complex.continuous_im.continuousWithinAt.tendsto).eventually
      (Iio_mem_nhds (by linarith [hw.2.2.2]))
  filter_upwards [self_mem_nhdsWithin, him] with v hv hvim
  have hnot : ¬ R ≤ ‖closedInverse a b c v‖ := by
    intro hlarge
    have hb := hdecay _ (closedInverse_mem_source hab hbc hv).1 hlarge
    rw [tail_closedInverse hab hbc hv] at hb
    have hnorm := Complex.abs_im_le_norm v
    have habs : -v.im ≤ |v.im| := neg_le_abs v.im
    linarith
  simpa only [Metric.mem_closedBall, dist_zero_right] using (lt_of_not_ge hnot).le

/-- The actual inverse extends continuously through the interiors of both
vertical sides. No boundary extension at a corner is used. -/
theorem closedInverse_continuousOn {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    ContinuousOn (closedInverse a b c)
      (closedHorizontalBand (period a b c) (height a b c)) := by
  intro w hw
  obtain ⟨R, hbounded⟩ := closedInverse_eventually_bounded hab hbc hw
  apply (isCompact_closedBall (0 : ℂ) R).tendsto_nhds_of_unique_mapClusterPt hbounded
  intro z hz hcluster
  obtain ⟨v, hgv, hv⟩ := hcluster.exists_seq_tendsto
  have hvmem : ∀ᶠ n in atTop,
      v n ∈ closedHorizontalBand (period a b c) (height a b c) :=
    hv.eventually self_mem_nhdsWithin
  have hgmem : ∀ᶠ n in atTop, (closedInverse a b c ∘ v) n ∈ closedUpper := by
    filter_upwards [hvmem] with n hn
    exact (closedInverse_mem_source hab hbc hn).1
  have hclosed : IsClosed closedUpper := isClosed_le continuous_const Complex.continuous_im
  have hzupper : z ∈ closedUpper := hclosed.mem_of_tendsto hgv hgmem
  have hgwithin : Tendsto (closedInverse a b c ∘ v) atTop (𝓝[closedUpper] z) :=
    tendsto_nhdsWithin_iff.mpr ⟨hgv, hgmem⟩
  have htc : Tendsto (tail a b c) (𝓝[closedUpper] z) (𝓝 (tail a b c z)) :=
    tail_continuousOn_closedUpper (realDensity_integrable hab hbc) z hzupper
  have hfz := htc.comp hgwithin
  have hfw : Tendsto (tail a b c ∘ (closedInverse a b c ∘ v)) atTop (𝓝 w) := by
    apply (hv.mono_right nhdsWithin_le_nhds).congr'
    filter_upwards [hvmem] with n hn
    exact (tail_closedInverse hab hbc hn).symm
  have hf : tail a b c z = w := tendsto_nhds_unique hfz hfw
  have hzsource : z ∈ closedSource a b c := ⟨hzupper, by simpa only [mem_preimage, hf] using hw⟩
  exact tail_injOn_closedSource hab hbc hzsource (closedInverse_mem_source hab hbc hw)
    (hf.trans (tail_closedInverse hab hbc hw).symm)

theorem closedInverse_mem_upper {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {w : ℂ} (hw : w ∈ openRectangle (period a b c) (height a b c)) :
    closedInverse a b c w ∈ upper := by
  have hwband := openRectangle_subset_closedHorizontalBand _ _ hw
  have hz := closedInverse_mem_source hab hbc hwband
  have hf := congrArg Complex.re (tail_closedInverse hab hbc hwband)
  change 0 < (closedInverse a b c w).im
  by_contra hnot
  have him : (closedInverse a b c w).im = 0 := le_antisymm (le_of_not_gt hnot) hz.1
  rcases real_source_re_cases hab hbc hz him with hzero | hperiod
  · rw [hzero] at hf
    linarith [hw.1]
  · rw [hperiod] at hf
    linarith [hw.2.1]

theorem closedInverse_left_edge {a b c y : ℝ} (hab : a < b) (hbc : b < c)
    (hy : y ∈ Ioo (-height a b c) 0) :
    (closedInverse a b c ((y : ℂ) * Complex.I)).im = 0 ∧
      (closedInverse a b c ((y : ℂ) * Complex.I)).re < a := by
  obtain ⟨x, hx, heq⟩ := exists_left_edge_preimage hab hbc hy
  have hw : (y : ℂ) * Complex.I ∈ closedHorizontalBand (period a b c) (height a b c) := by
    simp only [closedHorizontalBand, mem_setOf_eq, Complex.mul_re, Complex.ofReal_re,
      Complex.I_re, Complex.ofReal_im, Complex.I_im, mul_zero, sub_zero,
      Complex.mul_im, mul_one, add_zero]
    exact ⟨le_rfl, (period_pos hab hbc).le, hy⟩
  have hxsource : (x : ℂ) ∈ closedSource a b c :=
    ⟨by simp [closedUpper], by simpa only [mem_preimage, heq] using hw⟩
  have hg : closedInverse a b c ((y : ℂ) * Complex.I) = (x : ℂ) := by
    rw [← heq]
    exact closedInverse_tail hab hbc hxsource
  simpa only [hg, Complex.ofReal_im, Complex.ofReal_re, true_and, mem_Iio] using hx

theorem closedInverse_right_edge {a b c y : ℝ} (hab : a < b) (hbc : b < c)
    (hy : y ∈ Ioo (-height a b c) 0) :
    (closedInverse a b c ((period a b c : ℂ) + (y : ℂ) * Complex.I)).im = 0 ∧
      b < (closedInverse a b c ((period a b c : ℂ) + (y : ℂ) * Complex.I)).re ∧
      (closedInverse a b c ((period a b c : ℂ) + (y : ℂ) * Complex.I)).re < c := by
  obtain ⟨x, hx, heq⟩ := exists_gap_edge_preimage hab hbc hy
  have hw : (period a b c : ℂ) + (y : ℂ) * Complex.I ∈
      closedHorizontalBand (period a b c) (height a b c) := by
    simp only [closedHorizontalBand, mem_setOf_eq, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.ofReal_im,
      Complex.I_im, mul_zero, sub_zero, Complex.mul_im, mul_one, add_zero, zero_add]
    exact ⟨(period_pos hab hbc).le, le_rfl, hy⟩
  have hxsource : (x : ℂ) ∈ closedSource a b c :=
    ⟨by simp [closedUpper], by simpa only [mem_preimage, heq] using hw⟩
  have hg : closedInverse a b c ((period a b c : ℂ) + (y : ℂ) * Complex.I) = (x : ℂ) := by
    rw [← heq]
    exact closedInverse_tail hab hbc hxsource
  simpa only [hg, Complex.ofReal_im, Complex.ofReal_re, true_and, mem_Ioo] using hx

theorem closedInverse_eq_rectangleChart_symm {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {w : ℂ} (hw : w ∈ openRectangle (period a b c) (height a b c)) :
    closedInverse a b c w = (rectangleChart hab hbc).symm w := by
  apply tail_injOn_upper hab hbc (closedInverse_mem_upper hab hbc hw)
    ((rectangleChart hab hbc).map_target hw)
  exact (tail_closedInverse hab hbc (openRectangle_subset_closedHorizontalBand _ _ hw)).trans
    ((rectangleChart hab hbc).right_inv hw).symm

/-- The continuous extension has the reciprocal cubic derivative at every
interior rectangle point. -/
theorem closedInverse_hasDerivAt {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {w : ℂ} (hw : w ∈ openRectangle (period a b c) (height a b c)) :
    HasDerivAt (closedInverse a b c)
      (-(upperRoot a (closedInverse a b c w) * upperRoot b (closedInverse a b c w) *
        upperRoot c (closedInverse a b c w))) w := by
  have heq : closedInverse a b c =ᶠ[𝓝 w] (rectangleChart hab hbc).symm := by
    filter_upwards [(openRectangle_isOpen _ _).mem_nhds hw] with v hv
    exact closedInverse_eq_rectangleChart_symm hab hbc hv
  have hd := (rectangleChart_symm_hasDerivAt hab hbc hw).congr_of_eventuallyEq heq
  simpa only [closedInverse_eq_rectangleChart_symm hab hbc hw] using hd

end
end SlitCubicClosedChart
