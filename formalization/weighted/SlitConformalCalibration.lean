import SlitPairableWaves
import SlitCubicUpperBound
import SlitCubicBoundaryRange
import CrestConformalModulus

/-!
# Common source calibration in a proved conformal coordinate

The geometric two-child length argument is transported through an actual
conformal chart, using sharp local Lipschitz bounds and the area Jacobian.
No rectifiability of the parent or either child is assumed.
-/

namespace SlitConformalCalibration

open Set Filter Metric MeasureTheory
open MarkedSlitTransport SlitWaveModulus SlitPotentialLength
open SlitPotentialReflection SlitCubicCalibration SlitCubicBoundary
open CrestConformalModulus
open scoped Topology ENNReal NNReal
noncomputable section

/-- Composition of two actual conformal charts, on its exact open source. -/
def compose (C D : ConformalChart) : ConformalChart where
  homeomorph := C.homeomorph.trans D.homeomorph
  derivative := fun z => D.derivative (C.homeomorph z)*C.derivative z
  hasDeriv := by
    intro z hz
    exact (D.hasDeriv _ hz.2).comp z (C.hasDeriv _ hz.1)
  derivative_continuous := by
    apply ContinuousOn.mul
    · exact D.derivative_continuous.comp
        (C.homeomorph.continuousOn.mono inter_subset_left) (fun _ hz => hz.2)
    · exact C.derivative_continuous.mono inter_subset_left
  derivative_ne_zero := fun z hz =>
    mul_ne_zero (D.derivative_ne_zero _ hz.2) (C.derivative_ne_zero _ hz.1)

@[simp] theorem compose_source (C D : ConformalChart) :
    (compose C D).homeomorph.source =
      C.homeomorph.source ∩ C.homeomorph ⁻¹' D.homeomorph.source := rfl

@[simp] theorem compose_apply (C D : ConformalChart) (z : ℂ) :
    (compose C D).homeomorph z = D.homeomorph (C.homeomorph z) := rfl

@[simp] theorem compose_derivative (C D : ConformalChart) (z : ℂ) :
    (compose C D).derivative z = D.derivative (C.homeomorph z)*C.derivative z := rfl

theorem chart_local_lipschitz (C : ConformalChart) {z : ℂ}
    (hz : z ∈ C.homeomorph.source) {L : ℝ} (hL : ‖C.derivative z‖ < L) :
    ∃ U ∈ 𝓝 z, LipschitzOnWith (Real.toNNReal L) C.homeomorph U := by
  have hd : ∀ᶠ w in 𝓝 z, HasDerivAt C.homeomorph (C.derivative w) w :=
    Filter.Eventually.mono (C.homeomorph.open_source.mem_nhds hz)
      (fun w hw => C.hasDeriv w hw)
  have hs := hasStrictDerivAt_of_hasDerivAt_of_continuousAt hd
    (C.derivative_continuous.continuousAt (C.homeomorph.open_source.mem_nhds hz))
  apply hs.hasStrictFDerivAt.exists_lipschitzOnWith_of_nnnorm_lt
  apply Real.lt_toNNReal_iff_coe_lt.mpr
  simpa using hL

/-- Sharp local slope survives a conformal change of coordinates. -/
theorem localSlopeBound_comp (C : ConformalChart) {u g : ℂ → ℝ} {S E : Set ℂ}
    (hsource : S ⊆ C.homeomorph.source) (himage : MapsTo C.homeomorph S E)
    (hg : ∀ z ∈ E, 0 < g z) (hloc : LocalSlopeBound u g E) :
    LocalSlopeBound (fun z => u (C.homeomorph z))
      (fun z => g (C.homeomorph z)*‖C.derivative z‖) S := by
  intro z hz L hL
  have ha : 0 < g (C.homeomorph z) := hg _ (himage hz)
  have hb : 0 < ‖C.derivative z‖ := norm_pos_iff.mpr (C.derivative_ne_zero _ (hsource hz))
  obtain ⟨a, hga, haL⟩ := exists_between ((lt_div_iff₀ hb).mpr hL)
  have ha0 : 0 < a := ha.trans hga
  have hab : a*‖C.derivative z‖ < L := (lt_div_iff₀ hb).mp haL
  obtain ⟨b, hdb, hbL⟩ := exists_between ((lt_div_iff₀ ha0).mpr (by simpa [mul_comm] using hab))
  have hb0 : 0 < b := hb.trans hdb
  have habL : a*b < L := by
    simpa only [mul_comm] using (lt_div_iff₀ ha0).mp hbL
  obtain ⟨U,hU,hUlip⟩ := hloc _ (himage hz) a hga
  obtain ⟨V,hV,hVlip⟩ := chart_local_lipschitz C (hsource hz) hdb
  refine ⟨V ∩ C.homeomorph ⁻¹' U,
    inter_mem hV ((C.hasDeriv _ (hsource hz)).continuousAt.preimage_mem_nhds hU), ?_⟩
  have hcomp := hUlip.comp (hVlip.mono inter_subset_left) (fun _ hx => hx.2)
  apply hcomp.weaken
  apply NNReal.coe_le_coe.mp
  simp only [NNReal.coe_mul,Real.coe_toNNReal _ ha0.le,Real.coe_toNNReal _ hb0.le,
    Real.coe_toNNReal _ ((mul_pos ha0 hb0).trans habL).le]
  exact habL.le

def regular (N : Marking) : Set ℂ :=
  {z | fold z ≠ (N.left:ℂ) ∧ fold z ≠ (N.first:ℂ) ∧ fold z ≠ (N.second:ℂ)}

theorem cubic_slope_continuousAt (N : Marking) {z : ℂ} (hz : z ∈ regular N) :
    ContinuousAt (SlitCubicAdmissible.slope N) z :=
  (((differential_continuousAt (fold_im_nonneg z) hz.1 hz.2.1 hz.2.2).comp
    fold_continuous.continuousAt).norm).div_const _

theorem cubic_slope_pos (N : Marking) {z : ℂ} (hz : z ∈ regular N) :
    0 < SlitCubicAdmissible.slope N z := by
  apply div_pos _ (period_pos N.left_lt_first N.first_lt_second)
  apply norm_pos_iff.mpr
  exact inv_ne_zero (mul_ne_zero (mul_ne_zero
    (upperRoot_ne_zero (fold_im_nonneg z) hz.1)
    (upperRoot_ne_zero (fold_im_nonneg z) hz.2.1))
    (upperRoot_ne_zero (fold_im_nonneg z) hz.2.2))

theorem cubic_localSlopeBound (N : Marking) :
    LocalSlopeBound (SlitCubicAdmissible.potential N)
      (SlitCubicAdmissible.slope N) (regular N) := by
  have hi := realDensity_integrable N.left_lt_first N.first_lt_second
  have h := localSlopeBound_fold_re (F := tail N.left N.first N.second)
    (F' := fun z => -differential N.left N.first N.second z)
    (tail_continuousOn_closedUpper hi) (fun _ hz => tail_hasDerivAt hi hz)
    (S := regular N) (by
      intro z hz
      exact (differential_continuousAt (fold_im_nonneg z) hz.1 hz.2.1 hz.2.2).neg)
    (period_pos N.left_lt_first N.first_lt_second)
  intro z hz L hL
  exact h z hz L (by simpa only [SlitCubicAdmissible.slope,norm_neg] using hL)

def potential (C : ConformalChart) (N : Marking) (z : ℂ) : ℝ :=
  SlitCubicAdmissible.potential N (C.homeomorph z)

def slope (C : ConformalChart) (N : Marking) (z : ℂ) : ℝ :=
  SlitCubicAdmissible.slope N (C.homeomorph z)*‖C.derivative z‖

def density (C : ConformalChart) (N : Marking) : ℂ → ℝ≥0∞ :=
  C.pullDensity (SlitCubicAdmissible.density N)

theorem density_eq_half_slope (C : ConformalChart) (N : Marking) {z : ℂ}
    (hz : z ∈ C.homeomorph.source) :
    density C N z = (2:ℝ≥0∞)⁻¹*ENNReal.ofReal (slope C N z) := by
  unfold density ConformalChart.pullDensity
  rw [indicator_of_mem hz]
  simp only [SlitCubicAdmissible.density,ConformalChart.factor,slope]
  rw [mul_assoc,ENNReal.ofReal_mul]
  exact div_nonneg (norm_nonneg _) (period_pos N.left_lt_first N.first_lt_second).le

theorem density_area_le (C : ConformalChart) (N : Marking) :
    SlitWaveModulus.area (density C N) ≤ ENNReal.ofReal
      (SlitCubicBoundaryRange.height N.left N.first N.second /
        (2*period N.left N.first N.second)) := by
  calc
    SlitWaveModulus.area (density C N) = ∫⁻ z in C.homeomorph.target,
        (SlitCubicAdmissible.density N z)^2 := C.area_pull _
    _ ≤ SlitWaveModulus.area (SlitCubicAdmissible.density N) := setLIntegral_le_lintegral _ _
    _ = _ := SlitCubicUpperBound.density_area_exact N

/-- One common quadrilateral metric bounds every geometrically pairable
parent, including arbitrary excursions between the two proper children. -/
theorem pairable_width_le_period_ratio (C : ConformalChart) (M N : Marking)
    (D V T J₀ J₁ : Set ℂ)
    (hsource : SlitPairableWaves.calibrationRegion V T J₀ J₁ ⊆ C.homeomorph.source)
    (hregular : MapsTo C.homeomorph (SlitPairableWaves.calibrationRegion V T J₀ J₁)
      (regular N))
    (hzero : ∀ z ∈ J₀, (C.homeomorph z).im = 0 ∧ (C.homeomorph z).re ≤ N.left)
    (hone : ∀ z ∈ J₁, N.ends (C.homeomorph z)) :
    SlitPairableWaves.width M D V T J₀ J₁ ≤ ENNReal.ofReal
      (SlitCubicBoundaryRange.height N.left N.first N.second /
        (2*period N.left N.first N.second)) := by
  apply le_trans ?_ (density_area_le C N)
  apply SlitPairableWaves.width_le_area (u := potential C N) (g := slope C N)
    (C.pullDensity_measurable (SlitCubicAdmissible.density_measurable N))
  · intro z hz
    exact ((cubic_slope_continuousAt N (hregular hz)).comp
      (C.hasDeriv _ (hsource hz)).continuousAt).mul
        (C.derivative_continuous.continuousAt
          (C.homeomorph.open_source.mem_nhds (hsource hz))).norm
  · intro z hz
    exact mul_pos (cubic_slope_pos N (hregular hz))
      (norm_pos_iff.mpr (C.derivative_ne_zero _ (hsource hz)))
  · exact localSlopeBound_comp C hsource hregular
      (fun _ hz => cubic_slope_pos N hz) (cubic_localSlopeBound N)
  · intro z hz
    exact SlitCubicAdmissible.potential_left (hzero z hz).1 (hzero z hz).2
  · intro z hz
    exact SlitCubicAdmissible.potential_on_ends (hone z hz)
  · intro z hz
    exact (density_eq_half_slope C N (hsource hz)).symm.le

end
end SlitConformalCalibration
