import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Tactic

/-!
# Geometric length is bounded by parametrized length

A continuously differentiable parametrization may retrace its image.  Its
pushforward speed measure still dominates one-dimensional Hausdorff measure
on that image.  The resulting weighted inequality includes arbitrary
measurable extended nonnegative densities, without injectivity.
-/

namespace SlitParametricLength

open Set MeasureTheory Measure Filter Metric Function
open scoped Topology ENNReal NNReal

noncomputable section

private theorem image_bound_from_cover {f : ℝ → ℂ} {g : ℝ → ℝ≥0∞} {S : Set ℝ}
    (hS : MeasurableSet S) (U : ℕ → Set ℝ) (hU : ∀ n, MeasurableSet (U n))
    (hcover : S ⊆ ⋃ n, U n) (K : ℕ → ℝ≥0)
    (hLip : ∀ n, LipschitzOnWith (K n) f (U n))
    (hbound : ∀ n, ∀ x ∈ S ∩ U n, (K n : ℝ≥0∞) ≤ g x) :
    μH[1] (f '' S) ≤ ∫⁻ x in S, g x := by
  let V : ℕ → Set ℝ := fun n => S ∩ disjointed U n
  have hV : ∀ n, MeasurableSet (V n) :=
    fun n => hS.inter (MeasurableSet.disjointed hU n)
  have hsub : ∀ n, V n ⊆ U n := fun n x hx => disjointed_subset U n hx.2
  have hUnion : (⋃ n, V n) = S := by
    rw [← inter_iUnion, iUnion_disjointed]
    exact inter_eq_left.mpr hcover
  have hdisj : Pairwise (Disjoint on V) := by
    intro i j hij
    exact (disjoint_disjointed U hij).mono inter_subset_right inter_subset_right
  calc
    μH[1] (f '' S) = μH[1] (⋃ n, f '' V n) := by rw [← image_iUnion, hUnion]
    _ ≤ ∑' n, μH[1] (f '' V n) := measure_iUnion_le _
    _ ≤ ∑' n, (K n : ℝ≥0∞) * volume (V n) := by
      apply ENNReal.tsum_le_tsum
      intro n
      simpa only [ENNReal.rpow_one, hausdorffMeasure_real] using
        ((hLip n).mono (hsub n)).hausdorffMeasure_image_le (d := 1) (by norm_num)
    _ ≤ ∑' n, ∫⁻ x in V n, g x := by
      apply ENNReal.tsum_le_tsum
      intro n
      rw [← setLIntegral_const]
      exact setLIntegral_mono' (hV n) fun x hx => hbound n x ⟨hx.1, hsub n hx⟩
    _ = ∫⁻ x in S, g x := by rw [← lintegral_iUnion hV hdisj, hUnion]

private theorem local_lipschitz {a b : ℝ} {f v : ℝ → ℂ}
    (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hv : ContinuousOn v (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (v t) t)
    (x : Icc a b) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧
      LipschitzOnWith (Real.toNNReal (‖v x‖ + ε)) f (ball (x:ℝ) r ∩ Icc a b) ∧
      ∀ y ∈ ball (x:ℝ) r ∩ Icc a b, ‖v x‖ + ε ≤ ‖v y‖ + 2*ε := by
  have hcont := (hv x x.property).norm
  have hn₁ : ∀ᶠ y in 𝓝[Icc a b] (x:ℝ), ‖v y‖ < ‖v x‖ + ε :=
    hcont.eventually (gt_mem_nhds (by linarith))
  have hn₂ : ∀ᶠ y in 𝓝[Icc a b] (x:ℝ), ‖v x‖ - ε < ‖v y‖ :=
    hcont.eventually (lt_mem_nhds (by linarith))
  obtain ⟨r, hr, hnear⟩ := Metric.mem_nhdsWithin_iff.mp (hn₁.and hn₂)
  refine ⟨r, hr, ?_, ?_⟩
  · let U : Set ℝ := ball (x:ℝ) r ∩ Ioo a b
    have hU : Convex ℝ U := (convex_ball _ _).inter (convex_Ioo _ _)
    have hLip : LipschitzOnWith (Real.toNNReal (‖v x‖ + ε)) f U := by
      apply hU.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
        (fun y hy => (hd y hy.2).hasDerivWithinAt)
      intro y hy
      change ‖v y‖ ≤ (Real.toNNReal (‖v x‖ + ε) : ℝ)
      rw [Real.coe_toNNReal _ (by positivity)]
      exact (hnear ⟨hy.1, Ioo_subset_Icc_self hy.2⟩).1.le
    have hcl : closure U ⊆ Icc a b := by
      simpa only [closure_Ioo hab.ne] using
        (closure_mono (inter_subset_right : U ⊆ Ioo a b))
    have hsub : ball (x:ℝ) r ∩ Icc a b ⊆ closure U := by
      have hh : ball (x:ℝ) r ∩ closure (Ioo a b) ⊆ closure U :=
        isOpen_ball.inter_closure
      simpa only [closure_Ioo hab.ne] using hh
    exact (hLip.closure (hf.mono hcl)).mono hsub
  · intro y hy
    have h := (hnear hy).2
    linarith

private theorem image_bound_with_slack {a b : ℝ} {f v : ℝ → ℂ}
    (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hv : ContinuousOn v (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (v t) t)
    {S : Set ℝ} (hS : MeasurableSet S) (hSI : S ⊆ Icc a b)
    {ε : ℝ} (hε : 0 < ε) :
    μH[1] (f '' S) ≤ ∫⁻ x in S, ENNReal.ofReal (‖v x‖ + 2*ε) := by
  classical
  haveI : Nonempty (Icc a b) := ⟨⟨a, left_mem_Icc.mpr hab.le⟩⟩
  choose r hr hLip hbound using fun x : Icc a b => local_lipschitz hab hf hv hd x hε
  obtain ⟨j, hj⟩ := isCompact_Icc.isLindelof.indexed_countable_subcover
    (fun x : Icc a b => ball (x:ℝ) (r x)) (fun _ => isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hr ⟨x, hx⟩)⟩)
  apply image_bound_from_cover hS
    (fun n => ball (j n : ℝ) (r (j n)) ∩ Icc a b)
    (fun _ => isOpen_ball.measurableSet.inter measurableSet_Icc)
    (K := fun n => Real.toNNReal (‖v (j n)‖ + ε))
  · intro x hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hj (hSI hx))
    exact mem_iUnion.mpr ⟨n, hn, hSI hx⟩
  · exact fun n => hLip (j n)
  · intro n x hx
    change ENNReal.ofReal (‖v (j n)‖ + ε) ≤ _
    exact ENNReal.ofReal_le_ofReal (hbound (j n) x hx.2)

/-- A continuous speed bounds the Hausdorff measure of the image of every
measurable subset of the parameter interval. Endpoint differentiability is
not required. -/
theorem hausdorff_image_le_lintegral_speed {a b : ℝ} {f v : ℝ → ℂ}
    (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hv : ContinuousOn v (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (v t) t)
    {S : Set ℝ} (hS : MeasurableSet S) (hSI : S ⊆ Icc a b) :
    μH[1] (f '' S) ≤ ∫⁻ t in S, ENNReal.ofReal ‖v t‖ := by
  let B := ∫⁻ t in S, ENNReal.ofReal ‖v t‖
  have hfin : volume S ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono hSI)
      (show volume (Icc a b) < ⊤ by simp [Real.volume_Icc])).ne
  have hlim : Tendsto (fun ε : ℝ => B + ENNReal.ofReal (2*ε) * volume S)
      (𝓝[>] 0) (𝓝 B) := by
    have hc : Continuous (fun ε : ℝ => B + ENNReal.ofReal (2*ε) * volume S) :=
      continuous_const.add ((ENNReal.continuous_mul_const hfin).comp
        (ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_id)))
    simpa using (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hε
  change 0 < ε at hε
  have h := image_bound_with_slack hab hf hv hd hS hSI hε
  have he (t : ℝ) : ENNReal.ofReal (‖v t‖ + 2*ε) =
      ENNReal.ofReal ‖v t‖ + ENNReal.ofReal (2*ε) :=
    ENNReal.ofReal_add (norm_nonneg _) (by positivity)
  simpa only [he, lintegral_add_right _ measurable_const, setLIntegral_const, B] using h

private theorem restricted_hausdorff_le_map_speed {a b : ℝ} {f v : ℝ → ℂ}
    (hab : a < b) (hfm : Measurable f) (hf : ContinuousOn f (Icc a b))
    (hv : ContinuousOn v (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (v t) t) :
    (μH[1] : Measure ℂ).restrict (f '' Icc a b) ≤
      Measure.map f ((volume.restrict (Icc a b)).withDensity
        (fun t => ENNReal.ofReal ‖v t‖)) := by
  apply Measure.le_iff.mpr
  intro T hT
  rw [Measure.restrict_apply hT, Measure.map_apply hfm hT,
    withDensity_apply _ (hfm hT), Measure.restrict_restrict (hfm hT)]
  have he : T ∩ f '' Icc a b = f '' (f ⁻¹' T ∩ Icc a b) := by
    ext z
    constructor
    · rintro ⟨hz, t, ht, rfl⟩
      exact ⟨t, ⟨hz, ht⟩, rfl⟩
    · rintro ⟨t, ⟨htT, htI⟩, rfl⟩
      exact ⟨htT, t, htI, rfl⟩
  rw [he]
  exact hausdorff_image_le_lintegral_speed hab hf hv hd
    ((hfm hT).inter measurableSet_Icc) inter_subset_right

private theorem weighted_bound_of_measurable {a b : ℝ} {f v : ℝ → ℂ}
    {ρ : ℂ → ℝ≥0∞} (hab : a < b) (hfm : Measurable f)
    (hf : ContinuousOn f (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (v t) t) (hρ : Measurable ρ) :
    (∫⁻ z in f '' Icc a b, ρ z ∂μH[1]) ≤
      ∫⁻ t in Icc a b, ρ (f t) * ENNReal.ofReal ‖v t‖ := by
  have hμ := restricted_hausdorff_le_map_speed hab hfm hf hv hd
  calc
    _ ≤ ∫⁻ z, ρ z ∂Measure.map f ((volume.restrict (Icc a b)).withDensity
        (fun t => ENNReal.ofReal ‖v t‖)) := lintegral_mono' hμ le_rfl
    _ = ∫⁻ t in Icc a b, ρ (f t) * ENNReal.ofReal ‖v t‖ := by
      rw [lintegral_map hρ hfm]
      have hvm : AEMeasurable (fun t => ENNReal.ofReal ‖v t‖)
          (volume.restrict (Icc a b)) :=
        (hv.norm.aemeasurable measurableSet_Icc).ennreal_ofReal
      have hρfm : AEMeasurable (fun t => ρ (f t)) (volume.restrict (Icc a b)) :=
        (hρ.comp hfm).aemeasurable
      simpa only [Pi.mul_apply, mul_comm] using
        lintegral_withDensity_eq_lintegral_mul₀ hvm hρfm

/-- Weighted geometric Hausdorff length is at most parametrized weighted
length.  This includes infinite densities and repeated traversal, and
requires derivatives only in the open parameter interval. -/
theorem lintegral_image_le_lintegral_speed {a b : ℝ} {f v : ℝ → ℂ}
    {ρ : ℂ → ℝ≥0∞} (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hv : ContinuousOn v (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (v t) t) (hρ : Measurable ρ) :
    (∫⁻ z in f '' Icc a b, ρ z ∂μH[1]) ≤
      ∫⁻ t in Icc a b, ρ (f t) * ENNReal.ofReal ‖v t‖ := by
  classical
  let F : ℝ → ℂ := (Icc a b).piecewise f (fun _ => 0)
  have hF : ∀ t ∈ Icc a b, F t = f t := fun t ht => piecewise_eq_of_mem _ _ _ ht
  have hFm : Measurable F :=
    hf.measurable_piecewise continuous_const.continuousOn measurableSet_Icc
  have hFc : ContinuousOn F (Icc a b) := hf.congr hF
  have hFd : ∀ t ∈ Ioo a b, HasDerivAt F (v t) t := by
    intro t ht
    apply (hd t ht).congr_of_eventuallyEq
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    exact hF s hs
  have h := weighted_bound_of_measurable hab hFm hFc hv hFd hρ
  rw [image_congr hF] at h
  calc
    _ ≤ ∫⁻ t in Icc a b, ρ (F t) * ENNReal.ofReal ‖v t‖ := h
    _ = _ := setLIntegral_congr_fun measurableSet_Icc fun t ht => by rw [hF t ht]

end
end SlitParametricLength
