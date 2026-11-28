import ChildSlitModel
import CircularCrestModulus
import Mathlib.Analysis.Calculus.MeanValue

/-!
# A positive geometric child Wave

Concentric upper semicircles give a Borel Wave in the literal source
relative class. Their Hausdorff trace length is bounded by the angular
arclength integral, proved here from the Lipschitz inequality for
Hausdorff measure. Thus the existing circular energy calculation applies
to every density for these geometric traces, not just to a parametrized
surrogate. The resulting lower bound is uniform whenever the two ending
intervals contain the indicated semicircle endpoints.
-/

namespace ChildSlitPositive

open Set Function MeasureTheory MeasureTheory.Measure Metric
open MarkedSlitTransport ChildSlitModel SlitWaveModulus
open CircularCrestEnergy
open scoped ENNReal NNReal Topology

noncomputable section

private def angle (t : Parameter) : ℝ := Real.pi * (1 - (t : ℝ))

private theorem angle_mem (t : Parameter) : angle t ∈ Icc 0 Real.pi := by
  constructor
  · exact mul_nonneg Real.pi_pos.le (sub_nonneg.mpr t.property.2)
  · unfold angle
    calc
      Real.pi * (1 - (t : ℝ)) ≤ Real.pi * 1 :=
        mul_le_mul_of_nonneg_left (by linarith [t.property.1]) Real.pi_pos.le
      _ = Real.pi := mul_one _

private theorem angle_mem_interior {t : Parameter} (ht : t ∈ parameterInterior) :
    angle t ∈ Ioo 0 Real.pi := by
  constructor
  · exact mul_pos Real.pi_pos (sub_pos.mpr ht.2)
  · unfold angle
    calc
      Real.pi * (1 - (t : ℝ)) < Real.pi * 1 :=
        mul_lt_mul_of_pos_left (by linarith [ht.1]) Real.pi_pos
      _ = Real.pi := mul_one _

private theorem angle_surjective {v : ℝ} (hv : v ∈ Icc 0 Real.pi) :
    ∃ t : Parameter, angle t = v := by
  have h0 : 0 ≤ 1 - v / Real.pi := sub_nonneg.mpr ((div_le_one Real.pi_pos).mpr hv.2)
  have h1 : 1 - v / Real.pi ≤ 1 := by
    have := div_nonneg hv.1 Real.pi_pos.le
    linarith
  refine ⟨⟨1 - v / Real.pi, h0, h1⟩, ?_⟩
  dsimp [angle]
  field_simp [Real.pi_ne_zero]
  <;> ring

private theorem angle_surjective_interior {v : ℝ} (hv : v ∈ Ioo 0 Real.pi) :
    ∃ t ∈ parameterInterior, angle t = v := by
  have h0 : 0 < 1 - v / Real.pi := sub_pos.mpr ((div_lt_one Real.pi_pos).mpr hv.2)
  have h1 : 1 - v / Real.pi < 1 := by
    have := div_pos hv.1 Real.pi_pos
    linarith
  refine ⟨⟨1 - v / Real.pi, h0.le, h1.le⟩, ⟨h0, h1⟩, ?_⟩
  dsimp [angle]
  field_simp [Real.pi_ne_zero]
  <;> ring

/-- The left-to-right upper semicircle as a continuous unit-interval curve. -/
def semicircle (m r : ℝ) : Curve where
  toFun t := point (m : ℂ) r (angle t)
  continuous_toFun := (point_continuous (m : ℂ)).comp
    (continuous_const.prodMk
      (continuous_const.mul (continuous_const.sub continuous_subtype_val)))

private theorem semicircle_initial (m r : ℝ) :
    semicircle m r initial = ((m - r : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [semicircle, angle, initial, point, Complex.polarCoord_symm_apply]

private theorem semicircle_terminal (m r : ℝ) :
    semicircle m r terminal = ((m + r : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp [semicircle, angle, terminal, point, Complex.polarCoord_symm_apply]

private theorem semicircle_radius (m : ℝ) {r : ℝ} (hr : 0 < r) (t : Parameter) :
    ‖semicircle m r t - (m : ℂ)‖ = r := by
  simp [semicircle, point, Complex.norm_polarCoord_symm, abs_of_pos hr]

private theorem semicircle_above (m : ℝ) {r : ℝ} (hr : 0 < r)
    {t : Parameter} (ht : t ∈ parameterInterior) : 0 < (semicircle m r t).im := by
  have hθ := angle_mem_interior ht
  have hsin := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  simpa [semicircle, point, Complex.polarCoord_symm_apply] using mul_pos hr hsin

private theorem semicircle_simple (m : ℝ) {r : ℝ} (hr : 0 < r) :
    Simple (semicircle m r) := by
  intro t ht u hu htu
  have htθ := angle_mem_interior ht
  have huθ := angle_mem_interior hu
  have hct := point_coordinates (m : ℂ) hr
    ⟨(neg_lt_zero.mpr Real.pi_pos).trans htθ.1, htθ.2⟩
  have hcu := point_coordinates (m : ℂ) hr
    ⟨(neg_lt_zero.mpr Real.pi_pos).trans huθ.1, huθ.2⟩
  have he := congrArg (fun z : ℂ => (z - (m : ℂ)).arg) htu
  change (point (m : ℂ) r (angle t) - (m : ℂ)).arg =
    (point (m : ℂ) r (angle u) - (m : ℂ)).arg at he
  rw [hct.2, hcu.2] at he
  have he' : 1 - (t : ℝ) = 1 - (u : ℝ) := mul_left_cancel₀ Real.pi_ne_zero he
  apply Subtype.ext
  linarith

private theorem semicircle_trace (m r : ℝ) :
    trace (semicircle m r) = point (m : ℂ) r '' Icc 0 Real.pi := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨angle t, angle_mem t, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨t, ht⟩ := angle_surjective hv
    refine ⟨t, ?_⟩
    change point (m : ℂ) r (angle t) = point (m : ℂ) r v
    rw [ht]

private theorem semicircle_leaf (M : ChildMarking) (D : Set ℂ) (m : ℝ)
    {r b : ℝ} (hr : 0 < r) (hrb : r ≤ b)
    (hleft : m-r ∈ Ioo M.firstLo M.firstHi)
    (hright : m+r ∈ Ioo M.secondLo M.secondHi)
    (hD : closedBall (m : ℂ) b ⊆ D) : ChildLeaf M D (semicircle m r) := by
  have hs := semicircle_simple m hr
  have hi : ∀ t ∈ parameterInterior, semicircle m r t ∈ D := by
    intro t _
    apply hD
    rw [mem_closedBall, dist_eq_norm, semicircle_radius m hr]
    exact hrb
  have ha : ∀ t ∈ parameterInterior, semicircle m r t ∉ M.slit := by
    intro t ht hz
    have hz0 : (semicircle m r t).im = 0 := hz.1
    exact (semicircle_above m hr ht).ne' hz0
  refine ⟨hs, ?_, ?_, ?_, ?_, hi, ha, ?_⟩
  · rw [semicircle_initial]
    exact ⟨by simp, hleft.1, hleft.2⟩
  · rw [semicircle_terminal]
    exact ⟨by simp, hright.1, hright.2⟩
  · exact ⟨1, by norm_num, fun t ht0 ht1 => semicircle_above m hr ⟨ht0, ht1⟩⟩
  · refine ⟨1, by norm_num, ?_⟩
    intro t ht0 ht1
    exact semicircle_above m hr ⟨by simpa using ht0, ht1⟩
  · refine ⟨semicircle m r, ⟨hs, fun t ht => semicircle_above m hr ht⟩, ?_⟩
    refine ⟨⟨fun p => semicircle m r p.2,
      (semicircle m r).continuous.comp continuous_snd⟩,
      fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, ?_⟩
    exact fun _ t ht => ⟨hi t ht, ha t ht⟩

/-- The entire interval of semicircular leaves, with no leaf removed. -/
def semicircleFamily (m a b : ℝ) : Set Curve := semicircle m '' Ioo a b

private theorem semicircle_support (m a b : ℝ) :
    support (semicircleFamily m a b) =
      (fun p : ℝ × ℝ => point (m : ℂ) p.1 p.2) ''
        (Ioo a b ×ˢ Ioo 0 Real.pi) := by
  ext z
  simp only [support, semicircleFamily, mem_iUnion, interiorTrace, mem_image, mem_prod]
  constructor
  · rintro ⟨γ, ⟨r, hr, rfl⟩, t, ht, rfl⟩
    exact ⟨(r, angle t), ⟨hr, angle_mem_interior ht⟩, rfl⟩
  · rintro ⟨⟨r, v⟩, ⟨hr, hv⟩, rfl⟩
    obtain ⟨t, ht, htv⟩ := angle_surjective_interior hv
    refine ⟨semicircle m r, ⟨r, hr, rfl⟩, t, ht, ?_⟩
    change point (m : ℂ) r (angle t) = point (m : ℂ) r v
    rw [htv]

/-- This circular test family is a geometric Borel Wave in the source
domain and the exact same-bank relative class. -/
theorem semicircle_wave (M : ChildMarking) (D : Set ℂ) (m : ℝ)
    {a b : ℝ} (ha : 0 < a)
    (hends : ∀ r ∈ Ioo a b,
      m-r ∈ Ioo M.firstLo M.firstHi ∧ m+r ∈ Ioo M.secondLo M.secondHi)
    (hD : closedBall (m : ℂ) b ⊆ D) :
    ChildWave M D (semicircleFamily m a b) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [semicircle_support]
    apply (measurableSet_Ioo.prod measurableSet_Ioo).image_of_measurable_injOn
      (point_continuous (m : ℂ)).measurable
    rintro ⟨r, t⟩ ⟨hr, ht⟩ ⟨s, u⟩ ⟨hs, hu⟩ he
    have hrt := point_coordinates (m : ℂ) (ha.trans hr.1)
      ⟨(neg_lt_zero.mpr Real.pi_pos).trans ht.1, ht.2⟩
    have hsu := point_coordinates (m : ℂ) (ha.trans hs.1)
      ⟨(neg_lt_zero.mpr Real.pi_pos).trans hu.1, hu.2⟩
    apply Prod.ext
    · have hn := congrArg (fun z : ℂ => ‖z - (m : ℂ)‖) he
      exact hrt.1.symm.trans (hn.trans hsu.1)
    · have hn := congrArg (fun z : ℂ => (z - (m : ℂ)).arg) he
      exact hrt.2.symm.trans (hn.trans hsu.2)
  · rintro γ ⟨r, hr, rfl⟩
    exact semicircle_leaf M D m (ha.trans hr.1) hr.2.le
      (hends r hr).1 (hends r hr).2 hD
  · rintro γ ⟨r, hr, rfl⟩ η ⟨s, hs, rfl⟩ hne
    apply Set.disjoint_left.mpr
    rintro z ⟨t, ht, htz⟩ ⟨u, hu, huz⟩
    have he : semicircle m r t = semicircle m s u := htz.trans huz.symm
    have hn := congrArg (fun z : ℂ => ‖z - (m : ℂ)‖) he
    rw [semicircle_radius m (ha.trans hr.1),
      semicircle_radius m (ha.trans hs.1)] at hn
    exact hne (congrArg (semicircle m) hn)

private theorem realCurve_lineLength_image_le (f : ℝ → ℂ) {L : ℝ≥0}
    (hL : LipschitzWith L f) {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) (S : Set ℝ) :
    SlitWaveModulus.lineLength ρ (f '' S) ≤
      (L : ℝ≥0∞) * ∫⁻ t in S, ρ (f t) := by
  have hm : (μH[1] : Measure ℂ).restrict (f '' S) ≤
      (L : ℝ≥0∞) • Measure.map f (volume.restrict S) := by
    apply Measure.le_iff.mpr
    intro T hT
    rw [Measure.restrict_apply hT, Measure.smul_apply,
      Measure.map_apply hL.continuous.measurable hT,
      Measure.restrict_apply (hL.continuous.measurable hT)]
    have h := hL.hausdorffMeasure_image_le (d := 1) (by norm_num) (f ⁻¹' T ∩ S)
    have he : f '' (f ⁻¹' T ∩ S) = T ∩ f '' S := by
      ext z
      constructor
      · rintro ⟨t, ⟨ht, hs⟩, rfl⟩
        exact ⟨ht, ⟨t, hs, rfl⟩⟩
      · rintro ⟨hz, t, ht, rfl⟩
        exact ⟨t, ⟨hz, ht⟩, rfl⟩
    rw [he] at h
    simpa only [hausdorffMeasure_real, ENNReal.rpow_one, smul_eq_mul] using h
  calc
    SlitWaveModulus.lineLength ρ (f '' S) ≤
        ∫⁻ z, ρ z ∂((L : ℝ≥0∞) • Measure.map f (volume.restrict S)) :=
      lintegral_mono' hm le_rfl
    _ = (L : ℝ≥0∞) * ∫⁻ t in S, ρ (f t) := by
      rw [lintegral_smul_measure, lintegral_map hρ hL.continuous.measurable]

private theorem point_lipschitz (m : ℂ) {r : ℝ} (hr : 0 < r) :
    LipschitzWith ⟨r, hr.le⟩ (point m r) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    (fun t => (CircularCrestModulus.point_hasDerivAt m r t).differentiableAt)
  intro t
  rw [(CircularCrestModulus.point_hasDerivAt m r t).deriv]
  change ‖Complex.I * Complex.polarCoord.symm (r, t)‖ ≤ r
  simp [norm_mul, Complex.norm_polarCoord_symm, abs_of_pos hr]

/-- The geometric Hausdorff length is controlled by actual angular
arclength for every measurable extended density, including infinite ones. -/
theorem semicircle_lineLength_le (m : ℝ) {r : ℝ} (hr : 0 < r)
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    SlitWaveModulus.lineLength ρ (trace (semicircle m r)) ≤
      CircularCrestEnergy.leafLength (m : ℂ) r Real.pi ρ := by
  rw [semicircle_trace]
  refine (realCurve_lineLength_image_le (point (m : ℂ) r)
    (point_lipschitz (m : ℂ) hr) hρ (Icc 0 Real.pi)).trans_eq ?_
  rw [← ENNReal.ofReal_coe_nnreal]
  change ENNReal.ofReal r * (∫⁻ t in Icc 0 Real.pi, ρ (point (m : ℂ) r t)) = _
  rw [← restrict_Ioo_eq_restrict_Icc]
  unfold CircularCrestEnergy.leafLength
  rw [lintegral_mul_const _
    (hρ.comp ((point_continuous (m : ℂ)).comp
      (continuous_const.prodMk continuous_id)).measurable)]
  exact mul_comm _ _

/-- A uniform strictly positive lower bound for the full geometric
child optimum, supplied by a certified source-contained test Wave. -/
theorem width_lower_of_semicircles (M : ChildMarking) (D : Set ℂ) (m : ℝ)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hends : ∀ r ∈ Ioo a b,
      m-r ∈ Ioo M.firstLo M.firstHi ∧ m+r ∈ Ioo M.secondLo M.secondHi)
    (hD : closedBall (m : ℂ) b ⊆ D) :
    ENNReal.ofReal ((b-a)/(b*Real.pi)) ≤ ChildSlitModel.width M D := by
  have hΓ := semicircle_wave M D m ha hends hD
  apply le_trans ?_ (modulus_le_width hΓ)
  unfold SlitWaveModulus.modulus
  apply le_iInf₂
  intro ρ hρ
  have hcircle : CircularCrestEnergy.Admissible (m : ℂ) (Ioo a b)
      (fun _ => Real.pi) ρ := by
    refine ⟨hρ.1, ?_⟩
    intro r hr
    exact (hρ.2 (trace (semicircle m r))
      ⟨semicircle m r, ⟨r, hr, rfl⟩, rfl⟩).trans
      (semicircle_lineLength_le m (ha.trans hr.1) hρ.1)
  have he := radial_integral_le_area measurableSet_Ioo
    (fun r hr => ha.trans hr.1) (fun _ _ => ⟨Real.pi_pos, le_rfl⟩) hcircle
  have hb : 0 < b := ha.trans hab
  apply le_trans ?_ he
  calc
    ENNReal.ofReal ((b-a)/(b*Real.pi)) =
        ∫⁻ _r in Ioo a b, ENNReal.ofReal (1/(b*Real.pi)) := by
      simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioo]
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 1/(b*Real.pi))]
      congr 1
      ring
    _ ≤ ∫⁻ r in Ioo a b, ENNReal.ofReal (1/(r*Real.pi)) := by
      apply setLIntegral_mono' measurableSet_Ioo
      intro r hr
      exact ENNReal.ofReal_le_ofReal
        (one_div_le_one_div_of_le (mul_pos (ha.trans hr.1) Real.pi_pos)
          (mul_le_mul_of_nonneg_right hr.2.le Real.pi_pos.le))

theorem width_pos_of_semicircles (M : ChildMarking) (D : Set ℂ) (m : ℝ)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hends : ∀ r ∈ Ioo a b,
      m-r ∈ Ioo M.firstLo M.firstHi ∧ m+r ∈ Ioo M.secondLo M.secondHi)
    (hD : closedBall (m : ℂ) b ⊆ D) : 0 < ChildSlitModel.width M D := by
  have hp : 0 < ENNReal.ofReal ((b-a)/(b*Real.pi)) := by
    apply ENNReal.ofReal_pos.mpr
    exact div_pos (sub_pos.mpr hab) (mul_pos (ha.trans hab) Real.pi_pos)
  exact hp.trans_le (width_lower_of_semicircles M D m ha hab hends hD)

/-- One fixed ribbon fits every marking with these four coarse electrode
bounds. It lies in the unit disk and contributes at least `1/(3π)`. -/
theorem width_lower_of_fixed_windows (M : ChildMarking) (D : Set ℂ)
    (h1 : M.firstLo < -9/10) (h2 : -17/20 < M.firstHi)
    (h3 : M.secondLo < -13/20) (h4 : -3/5 < M.secondHi)
    (hD : closedBall (0 : ℂ) 1 ⊆ D) :
    ENNReal.ofReal (1/(3*Real.pi)) ≤ ChildSlitModel.width M D := by
  have hends : ∀ r ∈ Ioo (1/10 : ℝ) (3/20),
      -3/4-r ∈ Ioo M.firstLo M.firstHi ∧
      -3/4+r ∈ Ioo M.secondLo M.secondHi := by
    intro r hr
    exact ⟨⟨by linarith [hr.2], by linarith [hr.1]⟩,
      ⟨by linarith [hr.1], by linarith [hr.2]⟩⟩
  have hball : closedBall ((-3/4 : ℝ) : ℂ) (3/20) ⊆ D := by
    intro z hz
    apply hD
    rw [mem_closedBall_zero_iff]
    have hz' : ‖z - ((-3/4 : ℝ) : ℂ)‖ ≤ 3/20 := by
      simpa only [mem_closedBall, dist_eq_norm] using hz
    have hm : ‖((-3/4 : ℝ) : ℂ)‖ = 3/4 := by
      norm_num [Complex.norm_real, Real.norm_eq_abs]
    have hn := norm_add_le (z - ((-3/4 : ℝ) : ℂ)) ((-3/4 : ℝ) : ℂ)
    rw [sub_add_cancel, hm] at hn
    linarith
  have hl := width_lower_of_semicircles M D (-3/4)
    (by norm_num : (0 : ℝ) < 1/10) (by norm_num : (1/10 : ℝ) < 3/20)
    hends hball
  convert hl using 1
  congr 1
  field_simp [Real.pi_ne_zero]
  <;> ring

end
end ChildSlitPositive
