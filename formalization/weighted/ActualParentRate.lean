import ActualParentSupremum
import MarkedSlitDiskHomotopy

/-!
# A finite-period error bound for the complete physical parent optimum

The tail estimate is uniform over every geometric Borel parent lamination.
Choosing `p-10` dyadic shells leaves enough room inside the literal target
disk, so the comparison has no unknown compactness radius or optimizing
lamination. The exponentially small mark error is certified by the actual
critical-orbit estimates.
-/

namespace ActualParentRate

open Set Metric
open MarkedSlitTransport SlitWaveLimit SlitWaveEscape ActualParentMarks
open ActualParentSupremum NearTwoTip NearTwoShooting
open LoopsLimitingCrestParameter LimitingCrestQuadraticReturn
open SlitWaveScaling SlitWaveModulus
open scoped ENNReal

noncomputable section

set_option maxHeartbeats 1000000

def markError (c : ℝ) (p : ℕ) (k : ℝ) : ℝ :=
  cutError (limitCuts k) (actualCuts c p)

def periodDistortion (c : ℝ) (p : ℕ) (k : ℝ) : ℝ≥0∞ :=
  distortion (markError c p k) (1/100)

theorem markError_nonneg (c : ℝ) (p : ℕ) (k : ℝ) :
    0 ≤ markError c p k := cutError_nonneg _ _

theorem markError_le {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    markError c p k ≤ 4*3906*23646*scale p := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun (i : Fin 4) _ => actualCuts_error hp hc hk hroot i)
  simpa [markError, cutError, Finset.sum_const, mul_assoc] using h

theorem scale_error_small {p : ℕ} (hp : 30 ≤ p) :
    4*3906*23646*scale p < (1/200 : ℝ) := by
  have hscale : scale p ≤ (1/4 : ℝ)^30 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hp
  have hnum : 4*3906*23646*(1/4 : ℝ)^30 < 1/200 := by norm_num
  nlinarith

theorem markError_small {p : ℕ} (hp : 30 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    markError c p k < 1/200 :=
  (markError_le (by omega) hc hk hroot).trans_lt (scale_error_small hp)

theorem markCoords_limitMarking {k : ℝ} (hk : k ∈ parameterInterval) :
    markCoords (limitMarking k hk) = limitCuts k := by
  funext i
  exact markCoords_markingOfCuts _ _ i

theorem markCoords_actualMarking {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    markCoords (actualMarking hp hc hk hroot) = actualCuts c p := by
  funext i
  exact markCoords_markingOfCuts _ _ i

theorem limitMarking_separated {k : ℝ} (hk : k ∈ parameterInterval)
    (i j : Fin 4) (hij : i ≠ j) :
    (1/100 : ℝ) ≤ |markCoords (limitMarking k hk) i-
      markCoords (limitMarking k hk) j| := by
  rw [markCoords_limitMarking]
  exact (by norm_num : (1/100 : ℝ) ≤ 1/25).trans (limitCuts_separated hk hij).le

theorem limit_endpointRadius_lt {k : ℝ} (hk : k ∈ parameterInterval) :
    endpointRadius (limitMarking k hk) < 4 := by
  obtain ⟨h2l,h2u,h5l,h5u,h3l,h3u⟩ := limit_cut_boxes hk
  change |criticalOrbit k 2| + |criticalOrbit k 5| + |criticalOrbit k 3| + |(1 : ℝ)| + 1 < 4
  rw [abs_of_neg (by linarith : criticalOrbit k 2 < 0),
    abs_of_neg (by linarith : criticalOrbit k 5 < 0),
    abs_of_neg (by linarith : criticalOrbit k 3 < 0), abs_one]
  linarith

/-- Quantitative comparison before selecting the number of shells.
All assumptions are explicit numerical inequalities about actual marks
and the literal outer radius. -/
theorem physical_parent_comparison {p N : ℕ} (hp : 17 ≤ p) (hN : 0 < N)
    {c k : ℝ} (hc : ActualTip p c) (hk : k ∈ parameterInterval)
    (hroot : relation k = 0) (hsmall : markError c p k < 1/100)
    (hfit : 2*(dyadicRadius (endpointRadius (limitMarking k hk)) N+1) +
      markError c p k < targetRadius c p) :
    physicalParentWidth hp hc hk hroot ≤
      periodDistortion c p k * limitingParentWidth k hk ∧
    limitingParentWidth k hk ≤
      periodDistortion c p k * physicalParentWidth hp hc hk hroot +
        ENNReal.ofReal (3*Real.pi/(N : ℝ)) := by
  have hsmall' : cutError (markCoords (limitMarking k hk))
      (markCoords (actualMarking hp hc hk hroot)) < (1/100 : ℝ) := by
    simpa only [markCoords_limitMarking, markCoords_actualMarking, markError] using hsmall
  have hfit' : 2*(dyadicRadius (endpointRadius (limitMarking k hk)) N+1) +
      cutError (markCoords (limitMarking k hk))
        (markCoords (actualMarking hp hc hk hroot)) < targetRadius c p := by
    simpa only [markCoords_limitMarking, markCoords_actualMarking, markError] using hfit
  rw [physicalParentWidth_eq_actual]
  constructor
  · have hu := width_small_marks_upper (limitMarking k hk)
      (actualMarking hp hc hk hroot) (by norm_num : (0 : ℝ) < 1/100)
      (limitMarking_separated hk) hsmall' (ball (0 : ℂ) (targetRadius c p))
    simpa only [actualParentWidth, limitingParentWidth, periodDistortion, markError,
      markCoords_limitMarking, markCoords_actualMarking] using hu
  · have hl := width_small_marks_lower (limitMarking k hk)
      (actualMarking hp hc hk hroot) (by norm_num : (0 : ℝ) < 1/100)
      (limitMarking_separated hk) hsmall' hfit'
    have h := (width_cutoff (limitMarking k hk) hN).trans (add_le_add hl le_rfl)
    simpa only [actualParentWidth, limitingParentWidth, periodDistortion, markError,
      markCoords_limitMarking, markCoords_actualMarking] using h

theorem actual_shell_margin {p : ℕ} (hp : 30 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    2*(dyadicRadius (endpointRadius (limitMarking k hk)) (p-10)+1) +
      markError c p k < targetRadius c p := by
  have hbase := limit_endpointRadius_lt hk
  have hsmall := markError_small hp hc hk hroot
  have hpow : (1 : ℝ) ≤ 2^(p-10) := one_le_pow₀ (by norm_num)
  have hprod : (2 : ℝ)^(p-10) * endpointRadius (limitMarking k hk) <
      2^(p-10)*4 := mul_lt_mul_of_pos_left hbase (by positivity)
  have hexp : (2 : ℝ)^p = 2^(p-10)*1024 := by
    conv_lhs => rw [show p = (p-10)+10 by omega]
    rw [pow_add]
    norm_num
  have hradius := targetRadius_lower hc
  rw [hexp] at hradius
  dsimp [dyadicRadius]
  linarith

/-- An unconditional finite-period comparison for every actual tip of
period at least thirty. The shell count is explicit and grows linearly
with the period. -/
theorem physical_parent_period_comparison {p : ℕ} (hp : 30 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    physicalParentWidth (by omega : 17 ≤ p) hc hk hroot ≤
      periodDistortion c p k * limitingParentWidth k hk ∧
    limitingParentWidth k hk ≤
      periodDistortion c p k * physicalParentWidth (by omega : 17 ≤ p) hc hk hroot +
        ENNReal.ofReal (3*Real.pi/((p-10 : ℕ) : ℝ)) := by
  apply physical_parent_comparison (by omega) (by omega : 0 < p-10) hc hk hroot
  · exact (markError_small hp hc hk hroot).trans (by norm_num)
  · exact actual_shell_margin hp hc hk hroot

theorem distortion_real_bounds {E : ℝ} (hE : 0 ≤ E) (hsmall : E ≤ 1/200) :
    1 ≤ (distortion E (1/100)).toReal ∧
    (distortion E (1/100)).toReal ≤ 1+1600*E := by
  have hfrac : E/(1/100 : ℝ) = 100*E := by ring
  have hden : 0 < 1-100*E := by linarith
  have hs : (1/4 : ℝ) ≤ (1-100*E)^2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_left hs (show 0 ≤ 1600*E by positivity)
  unfold distortion
  rw [ENNReal.toReal_ofReal (by positivity), hfrac, inv_pow, mul_comm, ← div_eq_mul_inv]
  constructor
  · apply (le_div_iff₀ (sq_pos_of_pos hden)).2
    nlinarith
  · apply (div_le_iff₀ (sq_pos_of_pos hden)).2
    nlinarith

private theorem abs_sub_le_of_multiplicative_bounds {P Q D e : ℝ}
    (hD : 1 ≤ D) (he : 0 ≤ e) (hu : P ≤ D*Q) (hl : Q ≤ D*P+e) :
    |P-Q| ≤ (D-1)*Q+e := by
  by_cases hpq : P ≤ Q
  · rw [abs_of_nonpos (sub_nonpos.mpr hpq)]
    have hm := mul_le_mul_of_nonneg_left hpq (sub_nonneg.mpr hD)
    nlinarith
  · rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hpq))]
    linarith

/-- A real absolute-error certificate for the complete physical optimum.
The exponential term is the proved motion of the four marked cuts; the
`3π/(p-10)` term controls all escaping leaves simultaneously. -/
theorem physical_parent_real_error {p : ℕ} (hp : 30 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    |(physicalParentWidth (by omega : 17 ≤ p) hc hk hroot).toReal -
      (limitingParentWidth k hk).toReal| ≤
      1600*(4*3906*23646*scale p)*(limitingParentWidth k hk).toReal +
        3*Real.pi/((p-10 : ℕ) : ℝ) := by
  have hcomp := physical_parent_period_comparison hp hc hk hroot
  have hPn := physicalParentWidth_ne_top (by omega : 17 ≤ p) hc hk hroot
  have hQn := limitingParentWidth_ne_top k hk
  have hDn : periodDistortion c p k ≠ ⊤ := ENNReal.ofReal_ne_top
  have he0 : 0 ≤ 3*Real.pi/((p-10 : ℕ) : ℝ) := by positivity
  have hu := ENNReal.toReal_mono (ENNReal.mul_ne_top hDn hQn) hcomp.1
  have hl := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top hDn hPn, ENNReal.ofReal_ne_top⟩) hcomp.2
  rw [ENNReal.toReal_mul] at hu
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top hDn hPn) ENNReal.ofReal_ne_top,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal he0] at hl
  have hD := distortion_real_bounds (markError_nonneg c p k)
    (markError_small hp hc hk hroot).le
  have habs := abs_sub_le_of_multiplicative_bounds hD.1 he0 hu hl
  have hE := markError_le (by omega : 17 ≤ p) hc hk hroot
  have hcoeff : (periodDistortion c p k).toReal-1 ≤
      1600*(4*3906*23646*scale p) := by
    dsimp only [periodDistortion]
    linarith [hD.2]
  exact habs.trans (add_le_add
    (mul_le_mul_of_nonneg_right hcoeff (show 0 ≤ (limitingParentWidth k hk).toReal
      from ENNReal.toReal_nonneg)) le_rfl)

/-- For every actual target, the selected plane relative class is the
same class witnessed by a homotopy entirely inside the finite disk.
The generous disk margin is proved from the actual orbit, rather than
included as a hypothesis on the parent family. -/
theorem actual_parent_disk_class {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0)
    {γ : Curve} (hγ : ParentLeaf (actualMarking hp hc hk hroot)
      (ball (0 : ℂ) (targetRadius c p)) γ) :
    LeftClassIn (actualMarking hp hc hk hroot)
      (ball (0 : ℂ) (targetRadius c p)) γ := by
  apply hγ.leftClassIn_ball (R := 2) (by norm_num)
  · have he := abs_lt.mp (actualCuts_error_lt hp hc hk hroot 0)
    obtain ⟨h2l,h2u,-,-,-,-⟩ := limit_cut_boxes hk
    change |actualCuts c p 0| ≤ 2
    change -(1/100 : ℝ) < actualCuts c p 0-criticalOrbit k 2 ∧
      actualCuts c p 0-criticalOrbit k 2 < 1/100 at he
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · change |(1 : ℝ)| ≤ 2
    norm_num
  · have hpow : (2 : ℝ)^17 ≤ 2^p := pow_le_pow_right₀ (by norm_num) hp
    have hradius := targetRadius_lower hc
    norm_num at hpow ⊢
    linarith

/-- The same native disk-class identification holds before normalization,
on the literal target of radius `2⁻ᵖ` in the quadratic dynamical plane. -/
theorem physical_parent_disk_class {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0)
    {γ : Curve} (hγ : ParentLeaf (physicalMarking hp hc hk hroot)
      (ball (0 : ℂ) ((1/2 : ℝ)^p)) γ) :
    LeftClassIn (physicalMarking hp hc hk hroot)
      (ball (0 : ℂ) ((1/2 : ℝ)^p)) γ := by
  let d := criticalValue c p
  have hd : 0 < d := hc.2.1
  let h := scalarCoordinate d hd
  let hi := scalarCoordinate d⁻¹ (inv_pos.mpr hd)
  have hm : (physicalMarking hp hc hk hroot).coordinateMap hi =
      actualMarking hp hc hk hroot := by
    rw [scalar_marking, ← actualMarking_scale hp hc hk hroot]
    exact scalar_marking_inverse _ d hd
  have hr : d⁻¹*(1/2 : ℝ)^p = targetRadius c p := by
    unfold targetRadius
    dsimp only [d]
    ring
  have hn : ParentLeaf (actualMarking hp hc hk hroot)
      (ball (0 : ℂ) (targetRadius c p)) (coordinateCurve hi γ) := by
    have hn := hγ.coordinateMap hi
    simpa only [hm, hi, scalar_plane, dilation_image_ball, hr] using hn
  have hl := (actual_parent_disk_class hp hc hk hroot hn).coordinateMap h
  have hM : (actualMarking hp hc hk hroot).coordinateMap h =
      physicalMarking hp hc hk hroot := by
    rw [scalar_marking]
    exact actualMarking_scale hp hc hk hroot
  have hR : d*targetRadius c p = (1/2 : ℝ)^p := by
    unfold targetRadius
    dsimp only [d]
    field_simp [hc.2.1.ne']
  have hγid : coordinateCurve h (coordinateCurve hi γ) = γ := by
    ext t
    simp only [coordinateCurve_apply]
    rw [congrFun (scalar_plane d hd) _, congrFun (scalar_plane d⁻¹ (inv_pos.mpr hd)) _]
    simp [dilation_apply, smul_smul, hd.ne']
  simpa only [hM, hγid, h, scalar_plane, dilation_image_ball, hR] using hl

/-- Requiring the relative homotopy to remain inside the physical target
disk leaves the complete supremum unchanged. This is an equality of the
full admissible families, not a restriction to selected representatives. -/
theorem physical_parent_disk_supremum {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    physicalParentWidth hp hc hk hroot =
      ⨆ (Γ : Set Curve)
        (_ : ParentWave (physicalMarking hp hc hk hroot)
          (ball (0 : ℂ) ((1/2 : ℝ)^p)) Γ)
        (_ : ∀ γ ∈ Γ, LeftClassIn (physicalMarking hp hc hk hroot)
          (ball (0 : ℂ) ((1/2 : ℝ)^p)) γ), modulus (traces Γ) := by
  apply le_antisymm
  · apply iSup₂_le
    intro Γ hΓ
    exact le_iSup_of_le Γ (le_iSup_of_le hΓ
      (le_iSup_of_le (fun γ hγ => physical_parent_disk_class hp hc hk hroot (hΓ.leaf γ hγ)) le_rfl))
  · apply iSup_le
    intro Γ
    apply iSup_le
    intro hΓ
    apply iSup_le
    intro _
    exact modulus_le_width hΓ

end

end ActualParentRate
