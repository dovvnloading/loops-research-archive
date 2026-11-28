import CollarExtremalLength
import SlitWaveModulus
import MarkedSlitTransport
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Tactic

/-!
# Hausdorff trace length and the actual arclength parameter

This module connects the geometric line integral used by `SlitWaveModulus`
to integration in the natural arclength parameter.  Rectifiability is derived
from finite Hausdorff measure for a simple continuous arc.
-/

namespace ParentWaveTraceLength

open Set MeasureTheory Measure CollarExtremalLength
open scoped ENNReal NNReal Topology

noncomputable section

local instance : NullSingletonClass (μH[1] : Measure ℂ) :=
  nullSingletonClass_hausdorff ℂ (by norm_num)

/-- A connected trace has at least the distance between any two of its points
as Hausdorff one-measure. -/
theorem edist_le_hausdorff_of_isPreconnected {S : Set ℂ}
    (hS : IsPreconnected S) {a b : ℂ} (ha : a ∈ S) (hb : b ∈ S) :
    edist a b ≤ μH[1] S := by
  have hsub : Icc (0 : ℝ) (dist a b) ⊆ (dist a) '' S := by
    simpa only [dist_self] using
      hS.intermediate_value ha hb (LipschitzWith.dist_right a).continuous.continuousOn
  have hm := measure_mono (μ := (μH[1] : Measure ℝ)) hsub
  have hl := (LipschitzWith.dist_right a).hausdorffMeasure_image_le
    (d := 1) (by norm_num) S
  rw [hausdorffMeasure_real, Real.volume_Icc] at hm
  rw [hausdorffMeasure_real] at hl
  simpa [edist_dist] using hm.trans (by simpa using hl)

/-- Adjacent partition subarcs overlap only in a point when the original
arc is injective; the point has zero Hausdorff one-measure. -/
private theorem partition_images_aedisjoint {f : ℝ → ℂ} {a b : ℝ}
    (hinj : InjOn f (Ioo a b)) {u : ℕ → ℝ}
    (hu : Monotone u) (hus : ∀ i, u i ∈ Icc a b) :
    Pairwise (fun (i j : ℕ) => AEDisjoint (μH[1] : Measure ℂ)
      (f '' Icc (u i) (u (i + 1))) (f '' Icc (u j) (u (j + 1)))) := by
  have hforward {i j : ℕ} (hij : i < j) :
      AEDisjoint (μH[1] : Measure ℂ)
        (f '' Icc (u i) (u (i + 1))) (f '' Icc (u j) (u (j + 1))) := by
    apply measure_mono_null (t := {f (u (i + 1)), f a, f b}) ?_
      ((toFinite _).measure_zero (μH[1] : Measure ℂ))
    rintro z ⟨⟨x, hx, rfl⟩, y, hy, heq⟩
    have hxs : x ∈ Icc a b := ⟨(hus i).1.trans hx.1, hx.2.trans (hus (i+1)).2⟩
    have hys : y ∈ Icc a b := ⟨(hus j).1.trans hy.1, hy.2.trans (hus (j+1)).2⟩
    by_cases hxa : x = a
    · simp [hxa]
    by_cases hxb : x = b
    · simp [hxb]
    by_cases hya : y = a
    · have : f x = f a := by simpa [hya] using heq.symm
      simp [this]
    by_cases hyb : y = b
    · have : f x = f b := by simpa [hyb] using heq.symm
      simp [this]
    have hxy : x = y := hinj
      ⟨lt_of_le_of_ne hxs.1 (Ne.symm hxa), lt_of_le_of_ne hxs.2 hxb⟩
      ⟨lt_of_le_of_ne hys.1 (Ne.symm hya), lt_of_le_of_ne hys.2 hyb⟩ heq.symm
    have hxend : x = u (i+1) := by
      apply le_antisymm hx.2
      exact (hu (Nat.succ_le_of_lt hij)).trans (hxy.symm ▸ hy.1)
    simp [hxend]
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hforward h
  · exact (hforward h).symm

/-- Every partition sum of an injective continuous arc is bounded by the
Hausdorff measure of its geometric trace. -/
theorem eVariationOn_le_hausdorff {f : ℝ → ℂ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hinj : InjOn f (Ioo a b)) :
    eVariationOn f (Icc a b) ≤ μH[1] (f '' Icc a b) := by
  unfold eVariationOn
  apply iSup_le
  rintro ⟨n, u, hu, hus⟩
  have hsub (i : ℕ) : Icc (u i) (u (i+1)) ⊆ Icc a b :=
    Icc_subset_Icc (hus i).1 (hus (i+1)).2
  have hmeas (i : ℕ) : MeasurableSet (f '' Icc (u i) (u (i+1))) :=
    (isCompact_Icc.image_of_continuousOn (hf.mono (hsub i))).measurableSet
  calc
    (∑ i ∈ Finset.range n, edist (f (u (i+1))) (f (u i))) ≤
        ∑ i ∈ Finset.range n, μH[1] (f '' Icc (u i) (u (i+1))) := by
      apply Finset.sum_le_sum
      intro i hi
      apply edist_le_hausdorff_of_isPreconnected
        (isPreconnected_Icc.image _ (hf.mono (hsub i)))
      · exact mem_image_of_mem _ ⟨hu (Nat.le_succ i), le_rfl⟩
      · exact mem_image_of_mem _ ⟨le_rfl, hu (Nat.le_succ i)⟩
    _ = μH[1] (⋃ i ∈ Finset.range n, f '' Icc (u i) (u (i+1))) := by
      symm
      apply measure_biUnion_finset₀
      · intro i hi j hj hij
        exact partition_images_aedisjoint hinj hu hus hij
      · intro i hi
        exact (hmeas i).nullMeasurableSet
    _ ≤ μH[1] (f '' Icc a b) := by
      apply measure_mono
      exact iUnion₂_subset fun i hi => image_mono (hsub i)

/-- Finite geometric trace length forces bounded variation; no smoothness
or finite variation hypothesis is inserted into the canonical curve family. -/
theorem boundedVariationOn_of_hausdorff_ne_top {f : ℝ → ℂ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (hinj : InjOn f (Ioo a b))
    (hfinite : μH[1] (f '' Icc a b) ≠ ∞) : BoundedVariationOn f (Icc a b) :=
  ne_top_of_le_ne_top hfinite (eVariationOn_le_hausdorff hf hinj)

/-- The one-Lipschitz arclength parameter bounds geometric trace measure
by total variation even when the original curve repeats portions. -/
theorem hausdorff_le_eVariationOn (γ : RectifiableCurve) :
    μH[1] (γ.toFun '' Icc 0 1) ≤ eVariationOn γ.toFun (Icc 0 1) := by
  have h := (arcParameter_lipschitz γ).hausdorffMeasure_image_le
    (d := 1) (by norm_num)
  rw [arcParameter_image, hausdorffMeasure_real, Real.volume_Icc] at h
  simpa [curveLength, ENNReal.ofReal_toReal γ.finite] using h

/-- A simple rectifiable curve has exactly its total variation as geometric
Hausdorff length. -/
theorem hausdorff_eq_eVariationOn (γ : RectifiableCurve)
    (hinj : InjOn γ.toFun (Ioo 0 1)) :
    μH[1] (γ.toFun '' Icc 0 1) = eVariationOn γ.toFun (Icc 0 1) :=
  le_antisymm (hausdorff_le_eVariationOn γ)
    (eVariationOn_le_hausdorff γ.continuous hinj)

/-- A one-Lipschitz real parameter pushes Lebesgue measure to a measure
dominating Hausdorff one-measure on its image. -/
theorem hausdorff_restrict_image_le_map {f : ℝ → ℂ} {s : Set ℝ}
    (hs : MeasurableSet s) (hf : LipschitzOnWith 1 f s) :
    (μH[1] : Measure ℂ).restrict (f '' s) ≤
      Measure.map f (volume.restrict s) := by
  have hm : AEMeasurable f (volume.restrict s) := hf.continuousOn.aemeasurable hs
  apply Measure.le_iff.mpr
  intro T hT
  rw [Measure.restrict_apply hT, Measure.map_apply_of_aemeasurable hm hT,
    Measure.restrict_apply' hs]
  have he : f '' (f ⁻¹' T ∩ s) = T ∩ f '' s := by
    ext z
    constructor
    · rintro ⟨t, ⟨ht, hs⟩, rfl⟩
      exact ⟨ht, ⟨t, hs, rfl⟩⟩
    · rintro ⟨hz, t, ht, rfl⟩
      exact ⟨t, ⟨hz, ht⟩, rfl⟩
  have h := (hf.mono (s := f ⁻¹' T ∩ s) inter_subset_right).hausdorffMeasure_image_le
    (d := 1) (by norm_num)
  rw [he, hausdorffMeasure_real] at h
  simpa using h

/-- For a simple arc, the pushed Lebesgue arclength measure is precisely
the restriction of Hausdorff one-measure to the actual trace. -/
theorem hausdorff_restrict_eq_arcParameter_map (γ : RectifiableCurve)
    (hinj : InjOn γ.toFun (Ioo 0 1)) :
    (μH[1] : Measure ℂ).restrict (γ.toFun '' Icc 0 1) =
      Measure.map (arcParameter γ) (volume.restrict (Icc 0 (curveLength γ))) := by
  have hfin : μH[1] (γ.toFun '' Icc 0 1) ≠ ∞ := by
    rw [hausdorff_eq_eVariationOn γ hinj]
    exact γ.finite
  letI : IsFiniteMeasure ((μH[1] : Measure ℂ).restrict (γ.toFun '' Icc 0 1)) :=
    isFiniteMeasure_restrict.mpr hfin
  apply Measure.eq_of_le_of_measure_univ_eq
  · simpa only [arcParameter_image] using
      hausdorff_restrict_image_le_map measurableSet_Icc (arcParameter_lipschitz γ)
  · rw [Measure.restrict_apply_univ,
      Measure.map_apply_of_aemeasurable
        ((arcParameter_lipschitz γ).continuousOn.aemeasurable measurableSet_Icc)
        MeasurableSet.univ]
    simp only [preimage_univ, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
    rw [hausdorff_eq_eVariationOn γ hinj]
    exact (ENNReal.ofReal_toReal γ.finite).symm

/-- The canonical geometric line integral equals integration in the actual
arclength parameter, for every measurable nonnegative density. -/
theorem lineLength_eq_metricLength {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ)
    (γ : RectifiableCurve) (hinj : InjOn γ.toFun (Ioo 0 1)) :
    SlitWaveModulus.lineLength ρ (γ.toFun '' Icc 0 1) = metricLength ρ γ := by
  unfold SlitWaveModulus.lineLength metricLength
  rw [hausdorff_restrict_eq_arcParameter_map γ hinj]
  exact lintegral_map' hρ.aemeasurable
    ((arcParameter_lipschitz γ).continuousOn.aemeasurable measurableSet_Icc)

/-- The canonical compact-interval curve, extended constantly beyond its
parameter interval solely to use Mathlib's real-parameter variation. -/
def realCurve (γ : MarkedSlitTransport.Curve) : ℝ → ℂ :=
  fun t => γ (projIcc 0 1 (by norm_num) t)

theorem realCurve_continuous (γ : MarkedSlitTransport.Curve) :
    Continuous (realCurve γ) :=
  γ.continuous.comp continuous_projIcc

theorem realCurve_apply (γ : MarkedSlitTransport.Curve) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : realCurve γ t = γ ⟨t, ht⟩ := by
  simp only [realCurve, projIcc_of_mem _ ht]

theorem realCurve_image (γ : MarkedSlitTransport.Curve) :
    realCurve γ '' Icc 0 1 = MarkedSlitTransport.trace γ := by
  ext z
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨projIcc 0 1 (by norm_num) t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, t.property, realCurve_apply γ t.property⟩

theorem realCurve_injOn {γ : MarkedSlitTransport.Curve}
    (hs : MarkedSlitTransport.Simple γ) : InjOn (realCurve γ) (Ioo 0 1) := by
  intro x hx y hy heq
  rw [realCurve_apply γ ⟨hx.1.le, hx.2.le⟩,
    realCurve_apply γ ⟨hy.1.le, hy.2.le⟩] at heq
  exact congrArg Subtype.val (hs hx hy heq)

/-- Every finite-Hausdorff-length canonical simple curve has a derived
rectifiable representative with the same original parametrization. -/
def rectifiableOfFinite (γ : MarkedSlitTransport.Curve)
    (hs : MarkedSlitTransport.Simple γ)
    (hfinite : μH[1] (MarkedSlitTransport.trace γ) ≠ ∞) : RectifiableCurve where
  toFun := realCurve γ
  continuous := (realCurve_continuous γ).continuousOn
  finite := boundedVariationOn_of_hausdorff_ne_top
    (realCurve_continuous γ).continuousOn (realCurve_injOn hs)
    (by simpa only [realCurve_image] using hfinite)

/-- This identity applies to the canonical parent trace itself, including
the allowed case where its two physical endpoints coincide. -/
theorem canonical_lineLength_eq_metricLength {ρ : ℂ → ℝ≥0∞}
    (hρ : Measurable ρ) (γ : MarkedSlitTransport.Curve)
    (hs : MarkedSlitTransport.Simple γ)
    (hfinite : μH[1] (MarkedSlitTransport.trace γ) ≠ ∞) :
    SlitWaveModulus.lineLength ρ (MarkedSlitTransport.trace γ) =
      metricLength ρ (rectifiableOfFinite γ hs hfinite) := by
  have h := lineLength_eq_metricLength hρ (rectifiableOfFinite γ hs hfinite)
    (realCurve_injOn hs)
  simpa only [rectifiableOfFinite, realCurve_image] using h

end

end ParentWaveTraceLength
