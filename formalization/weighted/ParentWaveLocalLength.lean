import SlitWaveModulus
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Local length bounds for the canonical Hausdorff trace metric

Local Lipschitz estimates are assembled with a disjoint measurable cover.
No rectifiability or differentiability of the set being measured is assumed.
This is the measure-theoretic bridge needed to use the actual elliptic
differential on arbitrary continuous parent traces.
-/

namespace ParentWaveLocalLength

open Set MeasureTheory Measure Filter
open scoped ENNReal NNReal Topology

noncomputable section

theorem hausdorff_image_le_integral_of_cover {f : ℂ → ℂ} {S : Set ℂ}
    {V : ℕ → Set ℂ} {K : ℕ → ℝ≥0} {g : ℂ → ℝ≥0∞}
    (hV : ∀ n, MeasurableSet (V n)) (hcover : S ⊆ ⋃ n, V n)
    (hLip : ∀ n, LipschitzOnWith (K n) f (V n))
    (hbound : ∀ n, ∀ z ∈ V n, (K n : ℝ≥0∞) ≤ g z) :
    μH[1] (f '' S) ≤ ∫⁻ z in S, g z ∂μH[1] := by
  let E := disjointed V
  have hE : ∀ n, MeasurableSet (E n) := MeasurableSet.disjointed hV
  have hES : S ⊆ ⋃ n, E n := by simpa only [E, iUnion_disjointed] using hcover
  have hsplit : S = ⋃ n, E n ∩ S := by
    ext z
    simp only [mem_iUnion, mem_inter_iff]
    exact ⟨fun hz => (mem_iUnion.mp (hES hz)).imp (fun _ h => ⟨h,hz⟩),
      fun ⟨_,_,hz⟩ => hz⟩
  have hp (n : ℕ) : μH[1] (f '' (E n ∩ S)) ≤
      ∫⁻ z in E n, g z ∂((μH[1] : Measure ℂ).restrict S) := by
    calc
      μH[1] (f '' (E n ∩ S)) ≤ (K n : ℝ≥0∞) * μH[1] (E n ∩ S) := by
        simpa only [ENNReal.rpow_one] using
          ((hLip n).mono (inter_subset_left.trans (disjointed_subset V n))).hausdorffMeasure_image_le
            (d := 1) (by norm_num)
      _ = ∫⁻ _ in E n, (K n : ℝ≥0∞) ∂((μH[1] : Measure ℂ).restrict S) := by
        rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
          Measure.restrict_apply (hE n)]
      _ ≤ ∫⁻ z in E n, g z ∂((μH[1] : Measure ℂ).restrict S) := by
        apply setLIntegral_mono' (hE n)
        intro z hz
        exact hbound n z (disjointed_subset V n hz)
  calc
    μH[1] (f '' S) = μH[1] (⋃ n, f '' (E n ∩ S)) := by
      congr 1
      calc
        f '' S = f '' (⋃ n, E n ∩ S) := congrArg (fun T => f '' T) hsplit
        _ = ⋃ n, f '' (E n ∩ S) := image_iUnion
    _ ≤ ∑' n, μH[1] (f '' (E n ∩ S)) := measure_iUnion_le _
    _ ≤ ∑' n, ∫⁻ z in E n, g z ∂((μH[1] : Measure ℂ).restrict S) :=
      ENNReal.tsum_le_tsum hp
    _ = ∫⁻ z in ⋃ n, E n, g z ∂((μH[1] : Measure ℂ).restrict S) :=
      (lintegral_iUnion hE (disjoint_disjointed V) g).symm
    _ = ∫⁻ z in S, g z ∂μH[1] := by
      rw [Measure.restrict_restrict (MeasurableSet.iUnion hE), inter_eq_right.mpr hES]

/-- Arbitrarily sharp local Lipschitz majorants imply the corresponding
Hausdorff measure bound on every set, including sets of infinite length. -/
theorem hausdorff_image_le_integral_of_local {f : ℂ → ℂ} {S : Set ℂ}
    {g : ℂ → ℝ≥0∞} (hg : Measurable g)
    (hlocal : ∀ k : ℝ≥0, 1 < k → ∀ z ∈ S,
      ∃ V : Set ℂ, ∃ K : ℝ≥0, IsOpen V ∧ z ∈ V ∧
        LipschitzOnWith K f V ∧ ∀ w ∈ V, (K : ℝ≥0∞) ≤ (k : ℝ≥0∞) * g w) :
    μH[1] (f '' S) ≤ ∫⁻ z in S, g z ∂μH[1] := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  letI : Nonempty S := hS.to_subtype
  have hk (k : ℝ≥0) (hk : 1 < k) :
      μH[1] (f '' S) ≤ (k : ℝ≥0∞) * ∫⁻ z in S, g z ∂μH[1] := by
    choose V K hVo hxV hLip hbound using fun z : S => hlocal k hk z z.2
    have hcover : S ⊆ ⋃ z : S, V z := by
      intro z hz
      exact mem_iUnion.mpr ⟨⟨z,hz⟩,hxV ⟨z,hz⟩⟩
    obtain ⟨v,hv⟩ := (HereditarilyLindelofSpace.isLindelof S).indexed_countable_subcover
      V hVo hcover
    have hi := hausdorff_image_le_integral_of_cover
      (fun n => (hVo (v n)).measurableSet) hv (fun n => hLip (v n))
      (fun n => hbound (v n))
    rwa [lintegral_const_mul _ hg] at hi
  have ht : Tendsto
      (fun k : ℝ≥0 => (k : ℝ≥0∞) * ∫⁻ z in S, g z ∂μH[1])
      (𝓝[>] (1 : ℝ≥0)) (𝓝 (∫⁻ z in S, g z ∂μH[1])) := by
    have hc : Tendsto (fun k : ℝ≥0 => (k : ℝ≥0∞))
        (𝓝[>] (1 : ℝ≥0)) (𝓝 (1 : ℝ≥0∞)) :=
      (ENNReal.continuous_coe.tendsto (1 : ℝ≥0)).mono_left nhdsWithin_le_nhds
    simpa only [one_mul] using ENNReal.Tendsto.mul_const hc
      (b := ∫⁻ z in S, g z ∂μH[1]) (Or.inl one_ne_zero)
  exact ge_of_tendsto ht
    (eventually_nhdsWithin_iff.mpr (Eventually.of_forall hk))

/-- Weighted transport for every measurable density. The map need not be
injective, and the source set need not be rectifiable or measurable. -/
theorem lineLength_image_le_of_local {f : ℂ → ℂ} {S : Set ℂ}
    {g ρ : ℂ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (hρ : Measurable ρ)
    (hlocal : ∀ k : ℝ≥0, 1 < k → ∀ z ∈ S,
      ∃ V : Set ℂ, ∃ K : ℝ≥0, IsOpen V ∧ z ∈ V ∧
        LipschitzOnWith K f V ∧ ∀ w ∈ V, (K : ℝ≥0∞) ≤ (k : ℝ≥0∞) * g w) :
    SlitWaveModulus.lineLength ρ (f '' S) ≤
      SlitWaveModulus.lineLength (fun z => g z * ρ (f z)) S := by
  have hm : (μH[1] : Measure ℂ).restrict (f '' S) ≤
      Measure.map f (((μH[1] : Measure ℂ).restrict S).withDensity g) := by
    apply Measure.le_iff.mpr
    intro T hT
    rw [Measure.restrict_apply hT, Measure.map_apply hf hT,
      withDensity_apply _ (hf hT), Measure.restrict_restrict (hf hT)]
    have he : T ∩ f '' S = f '' (f ⁻¹' T ∩ S) := by
      ext z
      constructor
      · rintro ⟨hz,w,hw,rfl⟩
        exact ⟨w,⟨hz,hw⟩,rfl⟩
      · rintro ⟨w,⟨hwT,hw⟩,rfl⟩
        exact ⟨hwT,w,hw,rfl⟩
    rw [he]
    exact hausdorff_image_le_integral_of_local hg
      (fun k hk z hz => hlocal k hk z hz.2)
  calc
    SlitWaveModulus.lineLength ρ (f '' S) ≤
        ∫⁻ z, ρ z ∂Measure.map f (((μH[1] : Measure ℂ).restrict S).withDensity g) :=
      lintegral_mono' hm le_rfl
    _ = SlitWaveModulus.lineLength (fun z => g z * ρ (f z)) S := by
      rw [lintegral_map hρ hf]
      exact lintegral_withDensity_eq_lintegral_mul _ hg
        (show Measurable (fun z => ρ (f z)) from hρ.comp hf)

/-- The literal complex derivative supplies arbitrarily sharp local
Lipschitz bounds wherever it is continuous and nonzero. -/
theorem local_bound_of_hasDeriv {f f' : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hd : ∀ z ∈ U, HasDerivAt f (f' z) z)
    (hc : ContinuousOn f' U) (hn : ∀ z ∈ U, f' z ≠ 0)
    (k : ℝ≥0) (hk : 1 < k) {z : ℂ} (hz : z ∈ U) :
    ∃ V : Set ℂ, ∃ K : ℝ≥0, IsOpen V ∧ z ∈ V ∧
      LipschitzOnWith K f V ∧
      ∀ w ∈ V, (K : ℝ≥0∞) ≤ (k : ℝ≥0∞) * ENNReal.ofReal ‖f' w‖ := by
  have hnpos : 0 < ‖f' z‖₊ := nnnorm_pos.mpr (hn z hz)
  have hgap : ‖f' z‖₊ < k * ‖f' z‖₊ := by
    simpa only [one_mul] using mul_lt_mul_of_pos_right hk hnpos
  obtain ⟨K,hK,hK'⟩ := exists_between hgap
  have hcn := (hc.continuousAt (hU.mem_nhds hz)).nnnorm
  have hb : {w | w ∈ U ∧ ‖f' w‖₊ < K ∧ K < k * ‖f' w‖₊} ∈ 𝓝 z :=
    inter_mem (hU.mem_nhds hz)
      ((hcn.eventually (gt_mem_nhds hK)).and
        ((continuousAt_const.mul hcn).eventually (lt_mem_nhds hK')))
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hb
  refine ⟨Metric.ball z r,K,Metric.isOpen_ball,Metric.mem_ball_self hr,?_,?_⟩
  · exact (convex_ball z r).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun w hw => (hd w (hball hw).1).hasDerivWithinAt)
      (fun w hw => (hball hw).2.1.le)
  · intro w hw
    rw [← coe_nnnorm (f' w), ENNReal.ofReal_coe_nnreal, ← ENNReal.coe_mul,
      ENNReal.coe_le_coe]
    exact (hball hw).2.2.le

/-- A conformal chart's actual differential controls every Hausdorff trace,
not just paths that were supplied with a smooth parameter. -/
theorem lineLength_image_le_of_hasDeriv {f f' : ℂ → ℂ} {U S : Set ℂ}
    {ρ : ℂ → ℝ≥0∞} (hf : Measurable f) (hf' : Measurable f')
    (hU : IsOpen U) (hd : ∀ z ∈ U, HasDerivAt f (f' z) z)
    (hc : ContinuousOn f' U) (hn : ∀ z ∈ U, f' z ≠ 0)
    (hS : S ⊆ U) (hρ : Measurable ρ) :
    SlitWaveModulus.lineLength ρ (f '' S) ≤
      SlitWaveModulus.lineLength (fun z => ENNReal.ofReal ‖f' z‖ * ρ (f z)) S := by
  apply lineLength_image_le_of_local hf (ENNReal.measurable_ofReal.comp hf'.norm) hρ
  intro k hk z hz
  exact local_bound_of_hasDeriv hU hd hc hn k hk (hS hz)

/-- Localization also works relative to a measurable closed domain. This
form includes traces touching the real boundary of a conformal chart. -/
theorem hausdorff_image_le_integral_of_localOn {f : ℂ → ℂ} {S D : Set ℂ}
    {g : ℂ → ℝ≥0∞} (hD : MeasurableSet D) (hSD : S ⊆ D) (hg : Measurable g)
    (hlocal : ∀ k : ℝ≥0, 1 < k → ∀ z ∈ S,
      ∃ V : Set ℂ, ∃ K : ℝ≥0, IsOpen V ∧ z ∈ V ∧
        LipschitzOnWith K f (V ∩ D) ∧
        ∀ w ∈ V ∩ D, (K : ℝ≥0∞) ≤ (k : ℝ≥0∞) * g w) :
    μH[1] (f '' S) ≤ ∫⁻ z in S, g z ∂μH[1] := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  letI : Nonempty S := hS.to_subtype
  have hk (k : ℝ≥0) (hk : 1 < k) :
      μH[1] (f '' S) ≤ (k : ℝ≥0∞) * ∫⁻ z in S, g z ∂μH[1] := by
    choose V K hVo hxV hLip hbound using fun z : S => hlocal k hk z z.2
    have hcover : S ⊆ ⋃ z : S, V z := by
      intro z hz
      exact mem_iUnion.mpr ⟨⟨z,hz⟩,hxV ⟨z,hz⟩⟩
    obtain ⟨v,hv⟩ := (HereditarilyLindelofSpace.isLindelof S).indexed_countable_subcover
      V hVo hcover
    have hcover' : S ⊆ ⋃ n, V (v n) ∩ D := by
      intro z hz
      obtain ⟨n,hn⟩ := mem_iUnion.mp (hv hz)
      exact mem_iUnion.mpr ⟨n,hn,hSD hz⟩
    have hi := hausdorff_image_le_integral_of_cover
      (fun n => (hVo (v n)).measurableSet.inter hD) hcover'
      (fun n => hLip (v n)) (fun n => hbound (v n))
    rwa [lintegral_const_mul _ hg] at hi
  have hc : Tendsto (fun k : ℝ≥0 => (k : ℝ≥0∞))
      (𝓝[>] (1 : ℝ≥0)) (𝓝 (1 : ℝ≥0∞)) :=
    (ENNReal.continuous_coe.tendsto (1 : ℝ≥0)).mono_left nhdsWithin_le_nhds
  have ht := ENNReal.Tendsto.mul_const hc
    (b := ∫⁻ z in S, g z ∂μH[1]) (Or.inl one_ne_zero)
  rw [one_mul] at ht
  exact ge_of_tendsto ht
    (eventually_nhdsWithin_iff.mpr (Eventually.of_forall hk))

/-- The relative-domain bound transports every measurable density too. -/
theorem lineLength_image_le_of_localOn {f : ℂ → ℂ} {S D : Set ℂ}
    {g ρ : ℂ → ℝ≥0∞} (hD : MeasurableSet D) (hSD : S ⊆ D)
    (hf : Measurable f) (hg : Measurable g) (hρ : Measurable ρ)
    (hlocal : ∀ k : ℝ≥0, 1 < k → ∀ z ∈ S,
      ∃ V : Set ℂ, ∃ K : ℝ≥0, IsOpen V ∧ z ∈ V ∧
        LipschitzOnWith K f (V ∩ D) ∧
        ∀ w ∈ V ∩ D, (K : ℝ≥0∞) ≤ (k : ℝ≥0∞) * g w) :
    SlitWaveModulus.lineLength ρ (f '' S) ≤
      SlitWaveModulus.lineLength (fun z => g z * ρ (f z)) S := by
  have hm : (μH[1] : Measure ℂ).restrict (f '' S) ≤
      Measure.map f (((μH[1] : Measure ℂ).restrict S).withDensity g) := by
    apply Measure.le_iff.mpr
    intro T hT
    rw [Measure.restrict_apply hT, Measure.map_apply hf hT,
      withDensity_apply _ (hf hT), Measure.restrict_restrict (hf hT)]
    have he : T ∩ f '' S = f '' (f ⁻¹' T ∩ S) := by
      ext z
      constructor
      · rintro ⟨hz,w,hw,rfl⟩
        exact ⟨w,⟨hz,hw⟩,rfl⟩
      · rintro ⟨w,⟨hwT,hw⟩,rfl⟩
        exact ⟨hwT,w,hw,rfl⟩
    rw [he]
    exact hausdorff_image_le_integral_of_localOn hD
      (inter_subset_right.trans hSD) hg (fun k hk z hz => hlocal k hk z hz.2)
  calc
    SlitWaveModulus.lineLength ρ (f '' S) ≤
        ∫⁻ z, ρ z ∂Measure.map f (((μH[1] : Measure ℂ).restrict S).withDensity g) :=
      lintegral_mono' hm le_rfl
    _ = SlitWaveModulus.lineLength (fun z => g z * ρ (f z)) S := by
      rw [lintegral_map hρ hf]
      exact lintegral_withDensity_eq_lintegral_mul _ hg
        (show Measurable (fun z => ρ (f z)) from hρ.comp hf)

/-- Only local measurability on the actual open chart is required. -/
theorem lineLength_image_le_of_hasDerivOn {f f' : ℂ → ℂ} {U S : Set ℂ}
    {ρ : ℂ → ℝ≥0∞} (hU : IsOpen U)
    (hd : ∀ z ∈ U, HasDerivAt f (f' z) z)
    (hc : ContinuousOn f' U) (hn : ∀ z ∈ U, f' z ≠ 0)
    (hS : S ⊆ U) (hSm : MeasurableSet S) (hρ : Measurable ρ) :
    SlitWaveModulus.lineLength ρ (f '' S) ≤
      SlitWaveModulus.lineLength (fun z => ENNReal.ofReal ‖f' z‖ * ρ (f z)) S := by
  classical
  let F := U.piecewise f (fun _ => 0)
  let D := U.piecewise f' (fun _ => 0)
  have hF : Measurable F := (show ContinuousOn f U from
    fun z hz => (hd z hz).continuousAt.continuousWithinAt).measurable_piecewise
      continuous_const.continuousOn hU.measurableSet
  have hD : Measurable D := hc.measurable_piecewise
    continuous_const.continuousOn hU.measurableSet
  have hDF : ∀ z ∈ U, HasDerivAt F (D z) z := by
    intro z hz
    have he : F =ᶠ[𝓝 z] f := by
      filter_upwards [hU.mem_nhds hz] with w hw
      exact piecewise_eq_of_mem U f _ hw
    simpa only [D,piecewise_eq_of_mem U f' _ hz] using
      (hd z hz).congr_of_eventuallyEq he
  have hDc : ContinuousOn D U := hc.congr (by
    intro z hz
    exact piecewise_eq_of_mem U f' _ hz)
  have hDn : ∀ z ∈ U, D z ≠ 0 := by
    intro z hz
    simpa only [D,piecewise_eq_of_mem U f' _ hz] using hn z hz
  have h := lineLength_image_le_of_hasDeriv hF hD hU hDF hDc hDn hS hρ
  have hEq : F '' S = f '' S := by
    apply image_congr
    intro z hz
    exact piecewise_eq_of_mem U f _ (hS hz)
  rw [hEq] at h
  refine h.trans_eq ?_
  apply setLIntegral_congr_fun hSm
  intro z hz
  simp only [F,D,piecewise_eq_of_mem U f _ (hS hz),
    piecewise_eq_of_mem U f' _ (hS hz)]

end
end ParentWaveLocalLength
