import SlitDiskMarking
import ActualParentRate
import SlitDiskOptimality
import SlitCubicOptimality

/-!
# Quantitative normalization of the finite disk optimum

Affine normalization of the explicit squared Cayley coordinates keeps all
four marked cuts uniformly close to their physical positions.  The full
plane mark-transport estimates then apply without a logarithmic escaping
family term.
-/

namespace SlitDiskRate

open Set Filter Function MeasureTheory MarkedSlitTransport SlitWaveLimit
open SlitWaveScaling SlitDiskMarking ActualParentSupremum
open scoped Topology NNReal ENNReal
noncomputable section

/-- The affine normalization of a physical real cut after the Cayley map. -/
def normalizedCut (R x : ℝ) : ℝ := R * (SlitDiskCayley.realMap R x + 1) / 4

theorem normalizedCut_eq {R x : ℝ} (hden : R+x ≠ 0) :
    normalizedCut R x = R^2*x/(R+x)^2 := by
  unfold normalizedCut SlitDiskCayley.realMap
  field_simp
  ring

theorem normalizedCut_sub {R x : ℝ} (hden : R+x ≠ 0) :
    normalizedCut R x-x = -(x^2*(2*R+x)/(R+x)^2) := by
  rw [normalizedCut_eq hden]
  field_simp
  ring

/-- Uniform reciprocal-radius displacement of all cuts in the fixed box. -/
theorem normalizedCut_error_le {R x : ℝ} (hR : 4 ≤ R) (hx : |x| ≤ 2) :
    |normalizedCut R x-x| ≤ 40/R := by
  have hR0 : 0 < R := by linarith
  have hxl := (abs_le.mp hx).1
  have hxu := (abs_le.mp hx).2
  have hden : 0 < R+x := by linarith
  have hden2 : R^2 ≤ 4*(R+x)^2 := by
    have hh : R/2 ≤ R+x := by linarith
    have hp := mul_self_le_mul_self (by positivity : 0 ≤ R/2) hh
    nlinarith
  have hsq : x^2 ≤ 4 := by nlinarith [sq_abs x, sq_le_sq₀ (abs_nonneg x) (by norm_num : (0:ℝ) ≤ 2) |>.2 hx]
  have hn0 : 0 ≤ 2*R+x := by linarith
  have hnum : x^2*(2*R+x) ≤ 10*R := by
    have hm := mul_le_mul_of_nonneg_right hsq hn0
    nlinarith
  rw [normalizedCut_sub hden.ne',abs_neg,abs_of_nonneg (div_nonneg (mul_nonneg (sq_nonneg _) hn0) (sq_nonneg _))]
  apply (div_le_div_iff₀ (sq_pos_of_pos hden) hR0).mpr
  have hnR := mul_le_mul_of_nonneg_right hnum hR0.le
  nlinarith

theorem cutError_triangle {n : ℕ} (a b c : Fin n → ℝ) :
    cutError a c ≤ cutError a b + cutError b c := by
  unfold cutError
  rw [←Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => (abs_sub_le (c i) (b i) (a i)).trans_eq (add_comm _ _)

/-- The positive affine map used after the squared Cayley transform. -/
def normalization (R : ℝ) (hR : 0 < R) : ℝ ≃o ℝ :=
  (OrderIso.addRight 1).trans (OrderIso.mulLeft₀ (R/4) (by positivity))

@[simp] theorem normalization_apply (R : ℝ) (hR : 0 < R) (x : ℝ) :
    normalization R hR x = (R/4)*(x+1) := rfl

def normalizedMarking {R : ℝ} (hR : 0 < R) (M : Marking)
    (hleft : -R < M.left) (hright : M.right < R) : Marking :=
  (transformedMarking hR M hleft hright).map (normalization R hR)

theorem markCoords_normalizedMarking {R : ℝ} (hR : 0 < R) (M : Marking)
    (hleft : -R < M.left) (hright : M.right < R) (i : Fin 4) :
    markCoords (normalizedMarking hR M hleft hright) i = normalizedCut R (markCoords M i) := by
  fin_cases i
  all_goals change (R/4)*(SlitDiskCayley.realMap R _+1) =
    R*(SlitDiskCayley.realMap R _+1)/4
  all_goals dsimp [markCoords]; ring

theorem normalizedMarking_error_le {R : ℝ} (hR : 0 < R) (M : Marking)
    (hleft : -R < M.left) (hright : M.right < R) (hR4 : 4 ≤ R)
    (hbox : ∀ i, |markCoords M i| ≤ 2) :
    cutError (markCoords M) (markCoords (normalizedMarking hR M hleft hright)) ≤ 160/R := by
  unfold cutError
  simp only [markCoords_normalizedMarking]
  calc
    _ ≤ ∑ i : Fin 4, 40/R := Finset.sum_le_sum fun i _ => normalizedCut_error_le hR4 (hbox i)
    _ = 160/R := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring

private theorem horizontal_translation_lipschitz (s : ℝ) :
    LipschitzWith 1 (horizontal (OrderIso.addRight s)) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [NNReal.coe_one,one_mul,dist_eq_norm]
  have he : horizontal (OrderIso.addRight s) z-horizontal (OrderIso.addRight s) w = z-w := by
    apply Complex.ext <;> simp [horizontal_re,horizontal_im]
  rw [he]

theorem width_translation (M : Marking) (s : ℝ) :
    width (M.map (OrderIso.addRight s)) univ = width M univ := by
  have hL := horizontal_translation_lipschitz s
  have hK : LipschitzWith 1 (horizontal (OrderIso.addRight s)).symm := by
    rw [←horizontal_symm,OrderIso.addRight_symm]
    exact horizontal_translation_lipschitz (-s)
  have hu := width_le_mul_width M (OrderIso.addRight s) hL hK (by norm_num) (by norm_num)
    (D := univ) (E := univ) (subset_univ _)
  have hl := width_le_mul_width (M.map (OrderIso.addRight s)) (OrderIso.addRight s).symm
    (by simpa only [horizontal_symm] using hK)
    (by simpa only [horizontal_symm,Homeomorph.symm_symm] using hL)
    (by norm_num) (by norm_num) (D := univ) (E := univ) (subset_univ _)
  rw [marking_map_symm] at hl
  simp only [ENNReal.coe_one,one_pow,one_mul] at hu hl
  exact le_antisymm hl hu

theorem width_normalization (M : Marking) {R : ℝ} (hR : 0 < R) :
    width (M.map (normalization R hR)) univ = width M univ := by
  have he : M.map (normalization R hR) =
      (M.map (OrderIso.addRight 1)).map (OrderIso.mulLeft₀ (R/4) (by positivity)) := by
    apply Marking.ext <;> rfl
  rw [he]
  have hd := width_dilation (M.map (OrderIso.addRight 1)) univ (R/4) (by positivity)
  rw [image_univ,(dilation (R/4) (by positivity)).surjective.range_eq] at hd
  exact hd.trans (width_translation M 1)

/-- Both directions of full-plane mark transport use the same explicit distortion. -/
theorem plane_mark_comparison (M A : Marking) {r : ℝ} (hr : 0 < r)
    (hsep : ∀ i j, i ≠ j → r ≤ |markCoords M i-markCoords M j|)
    (hsmall : cutError (markCoords M) (markCoords A) < r) :
    width A univ ≤ distortion (cutError (markCoords M) (markCoords A)) r * width M univ ∧
    width M univ ≤ distortion (cutError (markCoords M) (markCoords A)) r * width A univ := by
  refine ⟨width_small_marks_upper M A hr hsep hsmall univ,?_⟩
  let E := cutError (markCoords M) (markCoords A)
  let h := cutOrderIso (markCoords M) (markCoords A) hr hsmall
  have hE : 0 ≤ E := cutError_nonneg _ _
  have hLpos : 0 < 1+E/r := add_pos_of_pos_of_nonneg zero_lt_one (div_nonneg hE hr.le)
  have hKpos : 0 < (1-E/r)⁻¹ := inv_pos.mpr (sub_pos.mpr ((div_lt_one hr).mpr hsmall))
  let L : ℝ≥0 := ⟨1+E/r,hLpos.le⟩
  let K : ℝ≥0 := ⟨(1-E/r)⁻¹,hKpos.le⟩
  have hL : LipschitzWith L (horizontal h) := cutHorizontal_lipschitz _ _ hr hsmall
  have hK : LipschitzWith K (horizontal h).symm := cutHorizontal_inverse_lipschitz _ _ hr hsmall
  have hmap : M.map h = A := marking_map_eq (cutOrderIso_marks _ _ hr hsmall hsep)
  have hLn : L ≠ 0 := ne_of_gt (show 0 < L from hLpos)
  have hKn : K ≠ 0 := ne_of_gt (show 0 < K from hKpos)
  have hw := width_le_mul_width M h hL hK hLn hKn
    (D := univ) (E := univ) (subset_univ _)
  rw [hmap] at hw
  have hLcoe : (L:ℝ≥0∞) = ENNReal.ofReal (1+E/r) := by
    rw [←ENNReal.ofReal_coe_nnreal]
    rfl
  have hKcoe : (K:ℝ≥0∞) = ENNReal.ofReal ((1-E/r)⁻¹) := by
    rw [←ENNReal.ofReal_coe_nnreal]
    rfl
  rw [hKcoe,hLcoe,←ENNReal.ofReal_pow hKpos.le,←ENNReal.ofReal_pow hLpos.le,
    ←ENNReal.ofReal_mul (sq_nonneg _)] at hw
  exact hw

/-- A finite real Lipschitz bound for the exact full-plane optimum as its cuts move. -/
theorem plane_mark_real_error (M A : Marking)
    (hsep : ∀ i j, i ≠ j → (1/100:ℝ) ≤ |markCoords M i-markCoords M j|)
    (hsmall : cutError (markCoords M) (markCoords A) ≤ 1/200) :
    |(width A univ).toReal-(width M univ).toReal| ≤
      1600*cutError (markCoords M) (markCoords A)*(width M univ).toReal := by
  let E := cutError (markCoords M) (markCoords A)
  let D := distortion E (1/100)
  have hE : 0 ≤ E := cutError_nonneg _ _
  have hc := plane_mark_comparison M A (by norm_num : (0:ℝ)<1/100) hsep
    (hsmall.trans_lt (by norm_num))
  have hMn := marked_width_ne_top M univ
  have hAn := marked_width_ne_top A univ
  have hDn : D ≠ ⊤ := ENNReal.ofReal_ne_top
  have hu := ENNReal.toReal_mono (ENNReal.mul_ne_top hDn hMn) hc.1
  have hl := ENNReal.toReal_mono (ENNReal.mul_ne_top hDn hAn) hc.2
  rw [ENNReal.toReal_mul] at hu hl
  have hD := ActualParentRate.distortion_real_bounds hE hsmall
  change 1 ≤ D.toReal ∧ D.toReal ≤ 1+1600*E at hD
  change |(width A univ).toReal-(width M univ).toReal| ≤ 1600*E*(width M univ).toReal
  by_cases hpq : (width A univ).toReal ≤ (width M univ).toReal
  · rw [abs_of_nonpos (sub_nonpos.mpr hpq)]
    have hm := mul_le_mul_of_nonneg_left hpq (sub_nonneg.mpr hD.1)
    have he := mul_le_mul_of_nonneg_right hD.2 (ENNReal.toReal_nonneg (a := width M univ))
    nlinarith
  · rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hpq))]
    have he := mul_le_mul_of_nonneg_right hD.2 (ENNReal.toReal_nonneg (a := width M univ))
    nlinarith

/-- The literal finite-disk optimum is exactly a full-plane optimum with explicit nearby cuts. -/
theorem width_disk_eq_normalized_plane {R : ℝ} (hR : 0 < R) (M : Marking)
    (hleft : -R < M.left) (hright : M.right < R) :
    width M (Metric.ball (0:ℂ) R) = width (normalizedMarking hR M hleft hright) univ := by
  rw [SlitDiskOptimality.width_eq_period_ratio hR M hleft hright]
  unfold normalizedMarking
  rw [width_normalization,SlitCubicOptimality.width_eq_period_ratio]
  rfl

end
end SlitDiskRate
