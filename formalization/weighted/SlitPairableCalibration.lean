import SlitPotentialLength

/-!
# Calibration of two actual temporal restrictions

Two source children occupy an initial and a terminal parameter interval of
one simple physical parent.  They may leave either half-plane, and the
middle part of the parent need not remain in the source.  The only local
analytic control used here is on the two closed child traces themselves.
Their possible common points have zero one-dimensional Hausdorff measure.
-/

namespace SlitPairableCalibration

open Set MeasureTheory Measure Filter Metric Function
open MarkedSlitTransport SlitPotentialLength SlitWaveModulus
open scoped Topology ENNReal NNReal

noncomputable section

def firstTrace (γ : Curve) (s : Parameter) : Set ℂ := γ '' Icc initial s

def lastTrace (γ : Curve) (t : Parameter) : Set ℂ := γ '' Icc t terminal

def childTraces (γ : Curve) (s t : Parameter) : Set ℂ :=
  firstTrace γ s ∪ lastTrace γ t

theorem childTraces_subset_trace (γ : Curve) (s t : Parameter) :
    childTraces γ s t ⊆ trace γ :=
  union_subset (image_subset_range _ _) (image_subset_range _ _)

/-- Distinct temporal source children of an interior-simple parent cannot
duplicate positive geometric length, even when the Euclidean parent
endpoints coincide or the two restrictions meet at their inner endpoint. -/
theorem child_traces_aedisjoint {γ : Curve} (hsimple : Simple γ)
    {s t : Parameter} (hs : s ∈ parameterInterior) (ht : t ∈ parameterInterior)
    (hst : s ≤ t) :
    AEDisjoint (μH[1] : Measure ℂ) (firstTrace γ s) (lastTrace γ t) := by
  haveI := nullSingletonClass_hausdorff ℂ (show (0 : ℝ) < 1 by norm_num)
  apply measure_mono_null (t := {γ initial, γ s, γ terminal})
  · rintro z ⟨⟨r, hr, hrz⟩, ⟨v, hv, hvz⟩⟩
    by_cases hr0 : r = initial
    · subst r
      rw [← hrz]
      simp
    by_cases hv1 : v = terminal
    · subst v
      rw [← hvz]
      simp
    have hr0' : (r : ℝ) ≠ 0 := fun h => hr0 (Subtype.ext h)
    have hv1' : (v : ℝ) ≠ 1 := fun h => hv1 (Subtype.ext h)
    have hri : r ∈ parameterInterior :=
      ⟨lt_of_le_of_ne r.property.1 hr0'.symm, lt_of_le_of_lt hr.2 hs.2⟩
    have hvi : v ∈ parameterInterior :=
      ⟨lt_of_lt_of_le ht.1 hv.1, lt_of_le_of_ne v.property.2 hv1'⟩
    have hrv : r = v := hsimple hri hvi (hrz.trans hvz.symm)
    have hrs : r = s := le_antisymm hr.2 (hst.trans (hrv ▸ hv.1))
    rw [← hrz, hrs]
    simp
  · exact (by simp : ({γ initial, γ s, γ terminal} : Set ℂ).Finite).measure_zero _

/-- A single actual compact parameter interval crossing the two potential
levels has weighted Hausdorff length at least one.  No arclength
parametrization or rectifiability is needed. -/
theorem one_le_weighted_subtrace {γ : Curve} {r s : Parameter} (hrs : r ≤ s)
    {u g : ℂ → ℝ}
    (hg : ∀ z ∈ γ '' Icc r s, ContinuousAt g z)
    (hpos : ∀ z ∈ γ '' Icc r s, 0 < g z)
    (hloc : LocalSlopeBound u g (γ '' Icc r s))
    (hend : (u (γ r) = 0 ∧ u (γ s) = 1) ∨
      (u (γ r) = 1 ∧ u (γ s) = 0)) :
    (1 : ℝ≥0∞) ≤ ∫⁻ z in γ '' Icc r s, ENNReal.ofReal (g z) ∂μH[1] := by
  have hcomp : ContinuousOn (u ∘ γ) (Icc r s) := by
    intro v hv
    exact ((hloc.continuousAt ⟨v, hv, rfl⟩).comp
      γ.continuous.continuousAt).continuousWithinAt
  have hI : Icc (0 : ℝ) 1 ⊆ u '' (γ '' Icc r s) := by
    rcases hend with ⟨hr, hs⟩ | ⟨hr, hs⟩
    · have h := intermediate_value_Icc hrs hcomp
      simpa only [Function.comp_apply, hr, hs, ← image_image] using h
    · have h := intermediate_value_Icc' hrs hcomp
      simpa only [Function.comp_apply, hr, hs, ← image_image] using h
  have hunit : μH[1] (Icc (0 : ℝ) 1) = 1 := by
    rw [hausdorffMeasure_real, Real.volume_Icc]
    norm_num
  rw [← hunit]
  exact (measure_mono hI).trans
    (hausdorff_image_le_lintegral (isCompact_Icc.image γ.continuous) hg hpos hloc)

/-- Both actual restrictions contribute, although the portion of the
parent between them is completely unconstrained by the potential. -/
theorem two_le_weighted_childTraces {γ : Curve} (hsimple : Simple γ)
    {s t : Parameter} (hs : s ∈ parameterInterior) (ht : t ∈ parameterInterior)
    (hst : s ≤ t) {u g : ℂ → ℝ}
    (hg : ∀ z ∈ childTraces γ s t, ContinuousAt g z)
    (hpos : ∀ z ∈ childTraces γ s t, 0 < g z)
    (hloc : LocalSlopeBound u g (childTraces γ s t))
    (hfirst : u (γ initial) = 1) (hlast : u (γ terminal) = 1)
    (hszero : u (γ s) = 0) (htzero : u (γ t) = 0) :
    (2 : ℝ≥0∞) ≤
      ∫⁻ z in childTraces γ s t, ENNReal.ofReal (g z) ∂μH[1] := by
  have ha : (1 : ℝ≥0∞) ≤
      ∫⁻ z in firstTrace γ s, ENNReal.ofReal (g z) ∂μH[1] :=
    one_le_weighted_subtrace s.property.1
      (fun z hz => hg z (Or.inl hz)) (fun z hz => hpos z (Or.inl hz))
      (fun z hz => hloc z (Or.inl hz)) (Or.inr ⟨hfirst, hszero⟩)
  have hb : (1 : ℝ≥0∞) ≤
      ∫⁻ z in lastTrace γ t, ENNReal.ofReal (g z) ∂μH[1] :=
    one_le_weighted_subtrace t.property.2
      (fun z hz => hg z (Or.inr hz)) (fun z hz => hpos z (Or.inr hz))
      (fun z hz => hloc z (Or.inr hz)) (Or.inl ⟨htzero, hlast⟩)
  have hB : MeasurableSet (lastTrace γ t) :=
    (isCompact_Icc.image γ.continuous).measurableSet
  rw [childTraces, Measure.restrict_union₀
    (child_traces_aedisjoint hsimple hs ht hst) hB.nullMeasurableSet,
    lintegral_add_measure]
  simpa only [one_add_one_eq_two] using add_le_add ha hb

/-- Any density dominating half the local slope on the two actual source
restrictions is admissible for the complete parent.  The density outside
those restrictions is arbitrary. -/
theorem one_le_lineLength_of_two_subarcs {γ : Curve} (hsimple : Simple γ)
    {s t : Parameter} (hs : s ∈ parameterInterior) (ht : t ∈ parameterInterior)
    (hst : s ≤ t) {u g : ℂ → ℝ} {ρ : ℂ → ℝ≥0∞}
    (hg : ∀ z ∈ childTraces γ s t, ContinuousAt g z)
    (hpos : ∀ z ∈ childTraces γ s t, 0 < g z)
    (hloc : LocalSlopeBound u g (childTraces γ s t))
    (hfirst : u (γ initial) = 1) (hlast : u (γ terminal) = 1)
    (hszero : u (γ s) = 0) (htzero : u (γ t) = 0)
    (hρ : ∀ z ∈ childTraces γ s t,
      (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal (g z) ≤ ρ z) :
    1 ≤ lineLength ρ (trace γ) := by
  have h := mul_le_mul_right
    (two_le_weighted_childTraces hsimple hs ht hst hg hpos hloc
      hfirst hlast hszero htzero) (2 : ℝ≥0∞)⁻¹
  have hh : (1 : ℝ≥0∞) ≤ ∫⁻ z in childTraces γ s t,
      (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal (g z) ∂μH[1] := by
    rw [lintegral_const_mul' _ _ (by norm_num)]
    simpa only [ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)] using h
  have hclosed : MeasurableSet (childTraces γ s t) :=
    (isCompact_Icc.image γ.continuous).measurableSet.union
      (isCompact_Icc.image γ.continuous).measurableSet
  exact (hh.trans (setLIntegral_mono' hclosed hρ)).trans
    (lintegral_mono_set (childTraces_subset_trace γ s t))

end
end SlitPairableCalibration
