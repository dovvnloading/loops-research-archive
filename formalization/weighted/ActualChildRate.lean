import ActualChildSupremum
import ActualParentRate

/-!
# Effective finite-period comparison for the full actual child optimum

The source component contains a disk of radius at least 2^(floor(p/2))/16.
That proved physical inradius pays for floor(p/2)-8 complete dyadic shells.
The quantitative error controls every same-bank Wave and its entire
source-contained homotopy; it is independent of any maximizing family.
The scalar distortion arithmetic is credited to the earlier parent proof.
-/

namespace ActualChildRate

open Set Metric
open MarkedSlitTransport SlitWaveEscape ChildSlitModel ChildSlitTransport ChildSlitLimit
open ActualChildMarks ActualChildSource ActualChildSupremum
open NearTwoTip NearTwoShooting LoopsLimitingCrestParameter LimitingCrestQuadraticReturn
open scoped ENNReal

noncomputable section
set_option maxHeartbeats 1000000

def markError (c : ℝ) (p : ℕ) (k : ℝ) : ℝ :=
  cutError (limitChildCuts k) (actualChildCuts c p)

def periodDistortion (c : ℝ) (p : ℕ) (k : ℝ) : ℝ≥0∞ :=
  distortion (markError c p k) (1/100)

theorem markError_nonneg (c : ℝ) (p : ℕ) (k : ℝ) :
    0 ≤ markError c p k := cutError_nonneg _ _

theorem markError_le {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    markError c p k ≤ 6*3906*23646*scale p := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun (i : Fin 6) _ => actualChildCuts_error hp hc hk hroot i)
  simpa [markError, cutError, Finset.sum_const, mul_assoc] using h

theorem scale_error_small {p : ℕ} (hp : 30 ≤ p) :
    6*3906*23646*scale p < (1/200 : ℝ) := by
  have hscale : scale p ≤ (1/4 : ℝ)^30 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hp
  have hnum : 6*3906*23646*(1/4 : ℝ)^30 < 1/200 := by norm_num
  nlinarith

theorem markError_small {p : ℕ} (hp : 30 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    markError c p k < 1/200 :=
  (markError_le (by omega) hc hk hroot).trans_lt (scale_error_small hp)

theorem markCoords_limitMarking {k : ℝ} (hk : k ∈ parameterInterval) :
    markCoords (limitMarking k hk) = limitChildCuts k := by
  funext i
  exact markCoords_markingOfCuts _ _ i

theorem markCoords_actualMarking {p : ℕ} (hp : 17 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    markCoords (actualMarking hp hc hk hroot) = actualChildCuts c p := by
  funext i
  exact markCoords_markingOfCuts _ _ i

theorem limitMarking_separated {k : ℝ} (hk : k ∈ parameterInterval)
    (i j : Fin 6) (hij : i ≠ j) :
    (1/100 : ℝ) ≤ |markCoords (limitMarking k hk) i-
      markCoords (limitMarking k hk) j| := by
  rw [markCoords_limitMarking]
  exact (by norm_num : (1/100 : ℝ) ≤ 1/50).trans (limitChildCuts_separated hk hij).le

theorem limit_endpointRadius_lt {k : ℝ} (hk : k ∈ parameterInterval) :
    endpointRadius (limitMarking k hk) < 5 := by
  obtain ⟨h2l,h2u,_,_,_,_⟩ := ActualParentMarks.limit_cut_boxes hk
  have h4 := parameter_orbit_bounds hk
  change |(-1 : ℝ)| + |-criticalOrbit k 4| +
    |criticalOrbit k 2| + |(1 : ℝ)| + 1 < 5
  simp only [abs_neg,abs_one,abs_of_pos (by linarith [h4.2.2.1] :
    0 < criticalOrbit k 4),
    abs_of_neg (by linarith : criticalOrbit k 2 < 0)]
  linarith [h4.2.2.2]

/-- Quantitative comparison before selecting the number of shells.
All assumptions are explicit numerical inequalities about actual marks
and the proved source inradius. -/
theorem physical_child_comparison {p N : ℕ} (hp : 17 ≤ p) (hN : 0 < N)
    {c k : ℝ} (hc : ActualTip p c) (hk : k ∈ parameterInterval)
    (hroot : relation k = 0) (hsmall : markError c p k < 1/100)
    (hfit : 2*(dyadicRadius (endpointRadius (limitMarking k hk)) N+1) +
      markError c p k < innerRadius c p) :
    physicalChildWidth hp hc hk hroot ≤
      periodDistortion c p k * limitingChildWidth k hk ∧
    limitingChildWidth k hk ≤
      periodDistortion c p k * physicalChildWidth hp hc hk hroot +
        ENNReal.ofReal (3*Real.pi/(N : ℝ)) := by
  have hsmall' : cutError (markCoords (limitMarking k hk))
      (markCoords (actualMarking hp hc hk hroot)) < (1/100 : ℝ) := by
    simpa only [markCoords_limitMarking, markCoords_actualMarking, markError] using hsmall
  have hfit' : 2*(dyadicRadius (endpointRadius (limitMarking k hk)) N+1) +
      cutError (markCoords (limitMarking k hk))
        (markCoords (actualMarking hp hc hk hroot)) < innerRadius c p := by
    simpa only [markCoords_limitMarking, markCoords_actualMarking, markError] using hfit
  rw [physicalChildWidth_eq_actual]
  constructor
  · have hu := width_small_marks_upper (limitMarking k hk)
      (actualMarking hp hc hk hroot) (by norm_num : (0 : ℝ) < 1/100)
      (limitMarking_separated hk) hsmall' (normalizedSource c p)
    simpa only [actualChildWidth, limitingChildWidth, periodDistortion, markError,
      markCoords_limitMarking, markCoords_actualMarking] using hu
  · have hl := width_small_marks_lower (limitMarking k hk)
      (actualMarking hp hc hk hroot) (by norm_num : (0 : ℝ) < 1/100)
      (limitMarking_separated hk) hsmall' hfit'
    have hd := width_mono (actualMarking hp hc hk hroot)
      (ball_subset_closedBall.trans (closedBall_subset_normalizedSource hp hc))
    have h := (width_cutoff (limitMarking k hk) hN).trans
      (add_le_add (hl.trans (mul_le_mul_left' hd _)) le_rfl)
    simpa only [actualChildWidth, limitingChildWidth, periodDistortion, markError,
      markCoords_limitMarking, markCoords_actualMarking] using h

theorem actual_shell_margin {p : ℕ} (hp : 30 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    2*(dyadicRadius (endpointRadius (limitMarking k hk)) (p/2-8)+1) +
      markError c p k < innerRadius c p := by
  have hbase := limit_endpointRadius_lt hk
  have hsmall := markError_small hp hc hk hroot
  have hpow : (1 : ℝ) ≤ 2^(p/2-8) := one_le_pow₀ (by norm_num)
  have hprod : (2 : ℝ)^(p/2-8) * endpointRadius (limitMarking k hk) <
      2^(p/2-8)*5 := mul_lt_mul_of_pos_left hbase (by positivity)
  have hexp : (2 : ℝ)^(p/2) = 2^(p/2-8)*256 := by
    conv_lhs => rw [show p/2 = (p/2-8)+8 by omega]
    rw [pow_add]
    norm_num
  have hradius := innerRadius_lower hc
  rw [hexp] at hradius
  dsimp [dyadicRadius]
  linarith

/-- An unconditional finite-period comparison for every actual tip of
period at least thirty. The shell count is explicit and grows linearly
with the period. -/
theorem physical_child_period_comparison {p : ℕ} (hp : 30 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    physicalChildWidth (by omega : 17 ≤ p) hc hk hroot ≤
      periodDistortion c p k * limitingChildWidth k hk ∧
    limitingChildWidth k hk ≤
      periodDistortion c p k * physicalChildWidth (by omega : 17 ≤ p) hc hk hroot +
        ENNReal.ofReal (3*Real.pi/((p/2-8 : ℕ) : ℝ)) := by
  apply physical_child_comparison (by omega) (by omega : 0 < p/2-8) hc hk hroot
  · exact (markError_small hp hc hk hroot).trans (by norm_num)
  · exact actual_shell_margin hp hc hk hroot

private theorem distortion_real_bounds {E : ℝ} (hE : 0 ≤ E) (hsmall : E ≤ 1/200) :
    1 ≤ (distortion E (1/100)).toReal ∧
    (distortion E (1/100)).toReal ≤ 1+1600*E := by
  exact ActualParentRate.distortion_real_bounds hE hsmall

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
The exponential term is the proved motion of the six marked cuts; the
`3π/(p/2-8)` term controls all escaping leaves simultaneously. -/
theorem physical_child_real_error {p : ℕ} (hp : 30 ≤ p) {c k : ℝ}
    (hc : ActualTip p c) (hk : k ∈ parameterInterval) (hroot : relation k = 0) :
    |(physicalChildWidth (by omega : 17 ≤ p) hc hk hroot).toReal -
      (limitingChildWidth k hk).toReal| ≤
      1600*(6*3906*23646*scale p)*(limitingChildWidth k hk).toReal +
        3*Real.pi/((p/2-8 : ℕ) : ℝ) := by
  have hcomp := physical_child_period_comparison hp hc hk hroot
  have hPn := physicalChildWidth_ne_top (by omega : 17 ≤ p) hc hk hroot
  have hQn := limitingChildWidth_ne_top k hk
  have hDn : periodDistortion c p k ≠ ⊤ := ENNReal.ofReal_ne_top
  have he0 : 0 ≤ 3*Real.pi/((p/2-8 : ℕ) : ℝ) := by positivity
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
      1600*(6*3906*23646*scale p) := by
    dsimp only [periodDistortion]
    linarith [hD.2]
  exact habs.trans (add_le_add
    (mul_le_mul_of_nonneg_right hcoeff (show 0 ≤ (limitingChildWidth k hk).toReal
      from ENNReal.toReal_nonneg)) le_rfl)


end
end ActualChildRate
