import SlitWaveModulus
import MarkedSlitTransport
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic

/-!
# Potential calibration on arbitrary simple geometric traces

The local hypothesis below controls the ordinary Lipschitz constants of a
scalar potential.  The resulting Hausdorff-length estimate is proved for
every compact trace, without a rectifiability assumption.  Splitting a
simple arc at an interior zero of the potential counts both endpoint-to-zero
transitions without duplicating any positive one-dimensional measure.
-/

namespace SlitPotentialLength

open Set MeasureTheory Measure Filter Metric Function
open scoped Topology ENNReal NNReal

noncomputable section

/-- A continuous upper bound for arbitrarily local Lipschitz constants.
This predicate concerns neighborhoods in the physical plane, rather than
assuming any integral inequality on a selected curve. -/
def LocalSlopeBound (u : ℂ → ℝ) (g : ℂ → ℝ) (S : Set ℂ) : Prop :=
  ∀ x ∈ S, ∀ L : ℝ, g x < L →
    ∃ U ∈ 𝓝 x, LipschitzOnWith (Real.toNNReal L) u U

theorem localSlopeBound_of_strict_derivative {u g : ℂ → ℝ} {S : Set ℂ}
    (du : ℂ → ℂ →L[ℝ] ℝ)
    (hd : ∀ x ∈ S, HasStrictFDerivAt u (du x) x)
    (hg : ∀ x ∈ S, ‖du x‖ ≤ g x) : LocalSlopeBound u g S := by
  intro x hx L hL
  apply (hd x hx).exists_lipschitzOnWith_of_nnnorm_lt
  apply Real.lt_toNNReal_iff_coe_lt.mpr
  exact lt_of_le_of_lt (hg x hx) hL

private theorem image_bound_from_cover {u g : ℂ → ℝ} {S : Set ℂ}
    (hS : MeasurableSet S) (U : ℕ → Set ℂ) (hU : ∀ n, MeasurableSet (U n))
    (hcover : S ⊆ ⋃ n, U n) (K : ℕ → ℝ≥0) (C : ℝ≥0∞)
    (hLip : ∀ n, LipschitzOnWith (K n) u (U n))
    (hbound : ∀ n, ∀ x ∈ S ∩ U n, (K n : ℝ≥0∞) ≤ C * ENNReal.ofReal (g x))
    (hC : C ≠ ⊤) :
    μH[1] (u '' S) ≤ C * ∫⁻ x in S, ENNReal.ofReal (g x) ∂μH[1] := by
  let V : ℕ → Set ℂ := fun n => S ∩ disjointed U n
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
    μH[1] (u '' S) = μH[1] (⋃ n, u '' V n) := by rw [← image_iUnion, hUnion]
    _ ≤ ∑' n, μH[1] (u '' V n) := measure_iUnion_le _
    _ ≤ ∑' n, (K n : ℝ≥0∞) * μH[1] (V n) := by
      apply ENNReal.tsum_le_tsum
      intro n
      simpa only [ENNReal.rpow_one] using
        ((hLip n).mono (hsub n)).hausdorffMeasure_image_le (d := 1) (by norm_num)
    _ ≤ ∑' n, ∫⁻ x in V n, C * ENNReal.ofReal (g x) ∂μH[1] := by
      apply ENNReal.tsum_le_tsum
      intro n
      rw [← setLIntegral_const]
      exact setLIntegral_mono' (hV n) fun x hx => hbound n x ⟨hx.1, hsub n hx⟩
    _ = ∫⁻ x in S, C * ENNReal.ofReal (g x) ∂μH[1] := by
      rw [← lintegral_iUnion hV hdisj, hUnion]
    _ = C * ∫⁻ x in S, ENNReal.ofReal (g x) ∂μH[1] :=
      lintegral_const_mul' _ _ hC

private theorem image_bound_with_slack {u g : ℂ → ℝ} {S : Set ℂ}
    (hS : IsCompact S) (hg : ∀ x ∈ S, ContinuousAt g x)
    (hpos : ∀ x ∈ S, 0 < g x) (hloc : LocalSlopeBound u g S)
    {k : ℝ} (hk : 1 < k) :
    μH[1] (u '' S) ≤ ENNReal.ofReal (k * k) *
      ∫⁻ x in S, ENNReal.ofReal (g x) ∂μH[1] := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  haveI : Nonempty S := hne.to_subtype
  have hk0 : 0 ≤ k := by linarith
  have hdata : ∀ x : S, ∃ V : Set ℂ, IsOpen V ∧ (x : ℂ) ∈ V ∧
      LipschitzOnWith (Real.toNNReal (k * g x)) u V ∧
      ∀ y ∈ V, g x < k * g y := by
    intro x
    have hkg : g x < k * g x := by nlinarith [hpos x x.property]
    obtain ⟨V, hV, hLip⟩ := hloc x x.property (k * g x) hkg
    have hnear : ∀ᶠ y in 𝓝 (x : ℂ), g x < k * g y :=
      ((hg x x.property).const_mul k).eventually (lt_mem_nhds hkg)
    obtain ⟨W, hWV, hWo, hWx⟩ := _root_.mem_nhds_iff.mp (inter_mem hV hnear)
    exact ⟨W, hWo, hWx, hLip.mono (fun y hy => (hWV hy).1),
      fun y hy => (hWV hy).2⟩
  choose V hVo hxV hLip hnear using hdata
  obtain ⟨f, hf⟩ := hS.isLindelof.indexed_countable_subcover V hVo (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩)
  apply image_bound_from_cover hS.measurableSet (fun n => V (f n))
    (fun n => (hVo (f n)).measurableSet) hf
    (fun n => Real.toNNReal (k * g (f n))) (ENNReal.ofReal (k * k))
    (fun n => hLip (f n))
  · intro n y hy
    change ENNReal.ofReal (k * g (f n)) ≤ _
    rw [← ENNReal.ofReal_mul (mul_nonneg hk0 hk0)]
    apply ENNReal.ofReal_le_ofReal
    calc
      k * g (f n) ≤ k * (k * g y) :=
        mul_le_mul_of_nonneg_left (hnear (f n) y hy.2).le hk0
      _ = (k * k) * g y := by ring
  · exact ENNReal.ofReal_ne_top

/-- A variable local Lipschitz bound controls the measure of the potential
image by the weighted Hausdorff measure of the original compact set.  The
set need not be a rectifiable curve and may have infinite length. -/
theorem hausdorff_image_le_lintegral {u g : ℂ → ℝ} {S : Set ℂ}
    (hS : IsCompact S) (hg : ∀ x ∈ S, ContinuousAt g x)
    (hpos : ∀ x ∈ S, 0 < g x) (hloc : LocalSlopeBound u g S) :
    μH[1] (u '' S) ≤ ∫⁻ x in S, ENNReal.ofReal (g x) ∂μH[1] := by
  let B := ∫⁻ x in S, ENNReal.ofReal (g x) ∂μH[1]
  by_cases hB : B = ⊤
  · rw [show (∫⁻ x in S, ENNReal.ofReal (g x) ∂μH[1]) = ⊤ from hB]
    exact le_top
  have hlim : Tendsto (fun k : ℝ => ENNReal.ofReal (k * k) * B)
      (𝓝[>] 1) (𝓝 B) := by
    have hc : Continuous (fun k : ℝ => ENNReal.ofReal (k * k) * B) :=
      (ENNReal.continuous_mul_const hB).comp
        (ENNReal.continuous_ofReal.comp (continuous_id.mul continuous_id))
    simpa using (hc.continuousAt (x := (1 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)))
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with k hk
  exact image_bound_with_slack hS hg hpos hloc hk

theorem LocalSlopeBound.continuousAt {u g : ℂ → ℝ} {S : Set ℂ}
    (h : LocalSlopeBound u g S) {x : ℂ} (hx : x ∈ S) : ContinuousAt u x := by
  obtain ⟨V, hV, hLip⟩ := h x hx (g x + 1) (by linarith)
  exact hLip.continuousOn.continuousAt hV

open MarkedSlitTransport

private theorem split_trace_aedisjoint {γ : Curve} (hsimple : Simple γ)
    {t : Parameter} (ht : t ∈ parameterInterior) :
    AEDisjoint (μH[1] : Measure ℂ)
      (γ '' Icc initial t) (γ '' Icc t terminal) := by
  haveI := nullSingletonClass_hausdorff ℂ (show (0 : ℝ) < 1 by norm_num)
  apply measure_mono_null (t := {γ initial, γ t, γ terminal})
  · rintro z ⟨⟨s, hs, hsz⟩, ⟨v, hv, hvz⟩⟩
    by_cases hs0 : s = initial
    · subst s
      rw [← hsz]
      simp
    by_cases hv1 : v = terminal
    · subst v
      rw [← hvz]
      simp
    have hs0' : (s : ℝ) ≠ 0 := by
      intro h
      exact hs0 (Subtype.ext h)
    have hv1' : (v : ℝ) ≠ 1 := by
      intro h
      exact hv1 (Subtype.ext h)
    have hsi : s ∈ parameterInterior :=
      ⟨lt_of_le_of_ne s.property.1 hs0'.symm, lt_of_le_of_lt hs.2 ht.2⟩
    have hvi : v ∈ parameterInterior :=
      ⟨lt_of_lt_of_le ht.1 hv.1, lt_of_le_of_ne v.property.2 hv1'⟩
    have hsv : s = v := hsimple hsi hvi (hsz.trans hvz.symm)
    have hst : s = t := le_antisymm hs.2 (hsv ▸ hv.1)
    rw [← hsz, hst]
    simp
  · exact (by simp : ({γ initial, γ t, γ terminal} : Set ℂ).Finite).measure_zero _

/-- The two transitions from endpoint potential one to an interior zero
force weighted geometric length at least two.  Interior simplicity is the
only multiplicity hypothesis, and infinite-length leaves are included. -/
theorem two_le_weighted_length_of_simple_excursion {γ : Curve}
    (hsimple : Simple γ) {u g : ℂ → ℝ}
    (hg : ∀ x ∈ trace γ, ContinuousAt g x)
    (hpos : ∀ x ∈ trace γ, 0 < g x)
    (hloc : LocalSlopeBound u g (trace γ))
    (hfirst : u (γ initial) = 1) (hlast : u (γ terminal) = 1)
    {t : Parameter} (ht : t ∈ parameterInterior) (hzero : u (γ t) = 0) :
    (2 : ℝ≥0∞) ≤ ∫⁻ z in trace γ, ENNReal.ofReal (g z) ∂μH[1] := by
  let A := γ '' Icc initial t
  let B := γ '' Icc t terminal
  have hA : IsCompact A := isCompact_Icc.image γ.continuous
  have hB : IsCompact B := isCompact_Icc.image γ.continuous
  have hAS : A ⊆ trace γ := image_subset_range _ _
  have hBS : B ⊆ trace γ := image_subset_range _ _
  have hcomp : Continuous (u ∘ γ) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    exact (hloc.continuousAt (mem_range_self s)).comp γ.continuous.continuousAt
  have h0t : initial ≤ t := t.property.1
  have ht1 : t ≤ terminal := t.property.2
  have hIA : Icc (0 : ℝ) 1 ⊆ u '' A := by
    have h := intermediate_value_Icc' h0t hcomp.continuousOn
    simpa only [Function.comp_apply, hzero, hfirst, ← image_image] using h
  have hIB : Icc (0 : ℝ) 1 ⊆ u '' B := by
    have h := intermediate_value_Icc ht1 hcomp.continuousOn
    simpa only [Function.comp_apply, hzero, hlast, ← image_image] using h
  have hunit : μH[1] (Icc (0 : ℝ) 1) = 1 := by
    rw [hausdorffMeasure_real, Real.volume_Icc]
    norm_num
  have ha : (1 : ℝ≥0∞) ≤ ∫⁻ z in A, ENNReal.ofReal (g z) ∂μH[1] := by
    rw [← hunit]
    exact (measure_mono hIA).trans (hausdorff_image_le_lintegral hA
      (fun x hx => hg x (hAS hx)) (fun x hx => hpos x (hAS hx))
      (fun x hx => hloc x (hAS hx)))
  have hb : (1 : ℝ≥0∞) ≤ ∫⁻ z in B, ENNReal.ofReal (g z) ∂μH[1] := by
    rw [← hunit]
    exact (measure_mono hIB).trans (hausdorff_image_le_lintegral hB
      (fun x hx => hg x (hBS hx)) (fun x hx => hpos x (hBS hx))
      (fun x hx => hloc x (hBS hx)))
  have hUnion : A ∪ B = trace γ := by
    apply subset_antisymm (union_subset hAS hBS)
    rintro z ⟨s, rfl⟩
    rcases le_total s t with hst | hts
    · exact Or.inl ⟨s, ⟨s.property.1, hst⟩, rfl⟩
    · exact Or.inr ⟨s, ⟨hts, s.property.2⟩, rfl⟩
  have hadd : (∫⁻ z in trace γ, ENNReal.ofReal (g z) ∂μH[1]) =
      (∫⁻ z in A, ENNReal.ofReal (g z) ∂μH[1]) +
      (∫⁻ z in B, ENNReal.ofReal (g z) ∂μH[1]) := by
    rw [← hUnion, Measure.restrict_union₀ (split_trace_aedisjoint hsimple ht)
      hB.measurableSet.nullMeasurableSet, lintegral_add_measure]
  rw [hadd]
  simpa only [one_add_one_eq_two] using add_le_add ha hb

/-- Half the local slope is an admissible geometric density on every
simple excursion from potential one through zero and back to one. -/
theorem one_le_half_density_length_of_simple_excursion {γ : Curve}
    (hsimple : Simple γ) {u g : ℂ → ℝ}
    (hg : ∀ x ∈ trace γ, ContinuousAt g x)
    (hpos : ∀ x ∈ trace γ, 0 < g x)
    (hloc : LocalSlopeBound u g (trace γ))
    (hfirst : u (γ initial) = 1) (hlast : u (γ terminal) = 1)
    {t : Parameter} (ht : t ∈ parameterInterior) (hzero : u (γ t) = 0) :
    1 ≤ SlitWaveModulus.lineLength
      (fun z => (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal (g z)) (trace γ) := by
  unfold SlitWaveModulus.lineLength
  rw [lintegral_const_mul' _ _ (by norm_num)]
  have h := mul_le_mul_right
    (two_le_weighted_length_of_simple_excursion hsimple hg hpos hloc
      hfirst hlast ht hzero) (2 : ℝ≥0∞)⁻¹
  simpa only [ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)] using h

end
end SlitPotentialLength
