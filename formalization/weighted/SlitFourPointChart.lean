import SlitCubicClosedChart
import SlitCubicLowerEnergy

/-!
# Four finite real electrodes and the actual cubic rectangle

The half-plane automorphism `z ↦ -1/(z-u)` sends `(u,v)` to the left
real ray and `(w,t)` to the finite cubic gap.  Its explicit inverse
transports the existing rectangle chart and its closed vertical edges.
-/

namespace SlitFourPointChart

open Set Function
open SlitCubicCalibration SlitCubicBoundary SlitCubicBoundaryRange
open SlitCubicRectangle SlitCubicSurjective
open scoped Topology

noncomputable section

def map (u : ℝ) (z : ℂ) : ℂ := -(z-(u:ℂ))⁻¹

def inverse (u : ℝ) (z : ℂ) : ℂ := (u:ℂ)-z⁻¹

def realMap (u x : ℝ) : ℝ := -(x-u)⁻¹

@[simp] theorem inverse_map (u : ℝ) (z : ℂ) : inverse u (map u z) = z := by
  simp only [inverse,map,inv_neg,inv_inv]
  ring

@[simp] theorem map_inverse (u : ℝ) (z : ℂ) : map u (inverse u z) = z := by
  have h : (u:ℂ)-z⁻¹-(u:ℂ) = -z⁻¹ := by ring
  simp [map,inverse,h]

theorem map_injective (u : ℝ) : Injective (map u) :=
  Function.LeftInverse.injective (inverse_map u)

theorem inverse_injective (u : ℝ) : Injective (inverse u) :=
  Function.LeftInverse.injective (map_inverse u)

theorem map_im (u : ℝ) (z : ℂ) :
    (map u z).im = z.im / Complex.normSq (z-(u:ℂ)) := by
  simp [map,Complex.inv_im,neg_div]

theorem inverse_im (u : ℝ) (z : ℂ) :
    (inverse u z).im = z.im / Complex.normSq z := by
  simp [inverse,Complex.inv_im,neg_div]

private theorem ne_real_of_upper {z : ℂ} (hz : z ∈ upper) (u : ℝ) : z ≠ (u:ℂ) := by
  intro he
  have h : 0 < z.im := hz
  simp [he] at h

private theorem ne_zero_of_upper {z : ℂ} (hz : z ∈ upper) : z ≠ 0 := by
  simpa using ne_real_of_upper hz 0

theorem map_mem_upper (u : ℝ) {z : ℂ} (hz : z ∈ upper) : map u z ∈ upper := by
  change 0 < (map u z).im
  rw [map_im]
  exact div_pos hz (Complex.normSq_pos.mpr (sub_ne_zero.mpr (ne_real_of_upper hz u)))

theorem inverse_mem_upper (u : ℝ) {z : ℂ} (hz : z ∈ upper) : inverse u z ∈ upper := by
  change 0 < (inverse u z).im
  rw [inverse_im]
  exact div_pos hz (Complex.normSq_pos.mpr (ne_zero_of_upper hz))

theorem map_mem_upper_iff (u : ℝ) (z : ℂ) : map u z ∈ upper ↔ z ∈ upper :=
  ⟨fun h => by simpa using inverse_mem_upper u h, map_mem_upper u⟩

theorem inverse_mem_upper_iff (u : ℝ) (z : ℂ) : inverse u z ∈ upper ↔ z ∈ upper :=
  ⟨fun h => by simpa using map_mem_upper u h, inverse_mem_upper u⟩

@[simp] theorem map_ofReal (u x : ℝ) : map u (x:ℂ) = (realMap u x : ℂ) := by
  simp [map,realMap]

@[simp] theorem inverse_ofReal (u x : ℝ) : inverse u (x:ℂ) = ((u-x⁻¹:ℝ):ℂ) := by
  simp [inverse]

theorem map_conj (u : ℝ) (z : ℂ) :
    map u (starRingEnd ℂ z) = starRingEnd ℂ (map u z) := by
  simp [map]

theorem inverse_conj (u : ℝ) (z : ℂ) :
    inverse u (starRingEnd ℂ z) = starRingEnd ℂ (inverse u z) := by
  simp [inverse]

theorem realMap_neg {u x : ℝ} (hx : u < x) : realMap u x < 0 := by
  exact neg_neg_of_pos (inv_pos.mpr (sub_pos.mpr hx))

theorem realMap_strictMonoOn (u : ℝ) : StrictMonoOn (realMap u) (Ioi u) := by
  intro x hx y _ hxy
  simpa only [realMap,one_div] using
    neg_lt_neg (one_div_lt_one_div_of_lt (sub_pos.mpr hx) (sub_lt_sub_right hxy u))

theorem inverse_realMap (u x : ℝ) : u-(realMap u x)⁻¹ = x := by
  simp only [realMap,inv_neg,inv_inv]
  ring

theorem inverse_real_left {u v x : ℝ} (huv : u < v) (hx : x < realMap u v) :
    u-x⁻¹ ∈ Ioo u v := by
  have hx0 : x < 0 := hx.trans (realMap_neg huv)
  have hleft : u < u-x⁻¹ := by have := inv_lt_zero.mpr hx0; linarith
  have hmap : realMap u (u-x⁻¹) = x := by
    simp only [realMap]
    rw [show u-x⁻¹-u = -x⁻¹ by ring,inv_neg,inv_inv,neg_neg]
  refine ⟨hleft, ?_⟩
  apply ((realMap_strictMonoOn u).lt_iff_lt hleft huv).mp
  simpa only [hmap] using hx

theorem inverse_real_gap {u v w t x : ℝ} (huv : u < v) (hvw : v < w) (hwt : w < t)
    (hx : x ∈ Ioo (realMap u w) (realMap u t)) :
    u-x⁻¹ ∈ Ioo w t := by
  have hut : u < t := huv.trans (hvw.trans hwt)
  have hux := (inverse_real_left hut hx.2).1
  have hmap : realMap u (u-x⁻¹) = x := by
    simp only [realMap]
    rw [show u-x⁻¹-u = -x⁻¹ by ring,inv_neg,inv_inv,neg_neg]
  constructor
  · apply ((realMap_strictMonoOn u).lt_iff_lt (huv.trans hvw) hux).mp
    simpa only [hmap] using hx.1
  · exact (inverse_real_left hut hx.2).2

theorem map_hasDerivAt (u : ℝ) {z : ℂ} (hz : z ≠ (u:ℂ)) :
    HasDerivAt (map u) ((z-(u:ℂ))^2)⁻¹ z := by
  have h := (((hasDerivAt_id z).sub_const (u:ℂ)).inv (sub_ne_zero.mpr hz)).neg
  apply h.congr_deriv
  simp only [neg_div,neg_neg,one_div,id_eq]

theorem inverse_hasDerivAt (u : ℝ) {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt (inverse u) (z^2)⁻¹ z := by
  have h := (hasDerivAt_const z (u:ℂ)).sub ((hasDerivAt_id z).inv hz)
  apply h.congr_deriv
  simp only [zero_sub,neg_div,neg_neg,one_div,id_eq]

/-- The genuine half-plane automorphism with its ordinary complex derivative. -/
def conformalChart (u : ℝ) : CrestConformalModulus.ConformalChart where
  homeomorph := {
    toFun := map u
    invFun := inverse u
    source := upper
    target := upper
    map_source' := fun _ hz => map_mem_upper u hz
    map_target' := fun _ hz => inverse_mem_upper u hz
    left_inv' := fun z _ => inverse_map u z
    right_inv' := fun z _ => map_inverse u z
    open_source := isOpen_lt continuous_const Complex.continuous_im
    open_target := isOpen_lt continuous_const Complex.continuous_im
    continuousOn_toFun := fun z hz =>
      (map_hasDerivAt u (ne_real_of_upper hz u)).continuousAt.continuousWithinAt
    continuousOn_invFun := fun z hz =>
      (inverse_hasDerivAt u (ne_zero_of_upper hz)).continuousAt.continuousWithinAt }
  derivative := fun z => ((z-(u:ℂ))^2)⁻¹
  hasDeriv := fun _ hz => map_hasDerivAt u (ne_real_of_upper hz u)
  derivative_continuous := by
    apply ContinuousOn.inv₀
    · exact (continuous_id.sub continuous_const).pow 2 |>.continuousOn
    · intro z hz
      exact pow_ne_zero _ (sub_ne_zero.mpr (ne_real_of_upper hz u))
  derivative_ne_zero := fun _ hz =>
    inv_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr (ne_real_of_upper hz u)))

@[simp] theorem conformalChart_source (u : ℝ) : (conformalChart u).homeomorph.source = upper := rfl
@[simp] theorem conformalChart_target (u : ℝ) : (conformalChart u).homeomorph.target = upper := rfl
@[simp] theorem conformalChart_apply (u : ℝ) (z : ℂ) : (conformalChart u).homeomorph z = map u z := rfl
@[simp] theorem conformalChart_symm_apply (u : ℝ) (z : ℂ) :
    (conformalChart u).homeomorph.symm z = inverse u z := rfl

theorem first_lt_second {u v w : ℝ} (huv : u < v) (hvw : v < w) :
    realMap u v < realMap u w :=
  realMap_strictMonoOn u huv (huv.trans hvw) hvw

theorem second_lt_third {u v w t : ℝ} (huv : u < v) (hvw : v < w) (hwt : w < t) :
    realMap u w < realMap u t :=
  realMap_strictMonoOn u (huv.trans hvw) (huv.trans (hvw.trans hwt)) hwt

def width (u v w t : ℝ) : ℝ := period (realMap u v) (realMap u w) (realMap u t)

def height (u v w t : ℝ) : ℝ :=
  SlitCubicBoundaryRange.height (realMap u v) (realMap u w) (realMap u t)

theorem width_pos {u v w t : ℝ} (huv : u < v) (hvw : v < w) (hwt : w < t) :
    0 < width u v w t := period_pos (first_lt_second huv hvw) (second_lt_third huv hvw hwt)

theorem height_pos {u v w t : ℝ} (huv : u < v) (hvw : v < w) (hwt : w < t) :
    0 < height u v w t :=
  SlitCubicBoundaryRange.height_pos (first_lt_second huv hvw) (second_lt_third huv hvw hwt)

/-- The inverse four-electrode rectangle, obtained from actual functions. -/
def inverseConformal {u v w t : ℝ} (huv : u < v) (hvw : v < w) (hwt : w < t) :
    CrestConformalModulus.ConformalChart where
  homeomorph := (SlitCubicLowerEnergy.inverseConformal
    (first_lt_second huv hvw) (second_lt_third huv hvw hwt)).homeomorph.trans
      (conformalChart u).homeomorph.symm
  derivative := fun ζ =>
    (((rectangleChart (first_lt_second huv hvw)
      (second_lt_third huv hvw hwt)).symm ζ)^2)⁻¹ *
        SlitCubicLowerEnergy.inverseVelocity
          (first_lt_second huv hvw) (second_lt_third huv hvw hwt) ζ
  hasDeriv := by
    intro ζ hζ
    exact (inverse_hasDerivAt u (ne_zero_of_upper hζ.2)).comp ζ
      ((SlitCubicLowerEnergy.inverseConformal
        (first_lt_second huv hvw) (second_lt_third huv hvw hwt)).hasDeriv ζ hζ.1)
  derivative_continuous := by
    apply ContinuousOn.mul
    · apply ContinuousOn.inv₀
      · exact ((rectangleChart (first_lt_second huv hvw)
          (second_lt_third huv hvw hwt)).continuousOn_symm.mono inter_subset_left).pow 2
      · intro ζ hζ
        exact pow_ne_zero _ (ne_zero_of_upper hζ.2)
    · exact (SlitCubicLowerEnergy.inverseConformal
        (first_lt_second huv hvw) (second_lt_third huv hvw hwt)).derivative_continuous.mono
          inter_subset_left
  derivative_ne_zero := fun ζ hζ => mul_ne_zero
    (inv_ne_zero (pow_ne_zero _ (ne_zero_of_upper hζ.2)))
    ((SlitCubicLowerEnergy.inverseConformal
      (first_lt_second huv hvw) (second_lt_third huv hvw hwt)).derivative_ne_zero ζ hζ.1)

@[simp] theorem inverseConformal_source {u v w t : ℝ}
    (huv : u < v) (hvw : v < w) (hwt : w < t) :
    (inverseConformal huv hvw hwt).homeomorph.source =
      openRectangle (width u v w t) (height u v w t) := by
  apply inter_eq_left.mpr
  intro ζ hζ
  exact (rectangleChart (first_lt_second huv hvw)
    (second_lt_third huv hvw hwt)).map_target hζ

@[simp] theorem inverseConformal_target {u v w t : ℝ}
    (huv : u < v) (hvw : v < w) (hwt : w < t) :
    (inverseConformal huv hvw hwt).homeomorph.target = upper := by
  change upper ∩ map u ⁻¹' upper = upper
  apply inter_eq_left.mpr
  intro z hz
  exact map_mem_upper u hz

@[simp] theorem inverseConformal_apply {u v w t : ℝ}
    (huv : u < v) (hvw : v < w) (hwt : w < t) (ζ : ℂ) :
    (inverseConformal huv hvw hwt).homeomorph ζ =
      inverse u ((rectangleChart (first_lt_second huv hvw)
        (second_lt_third huv hvw hwt)).symm ζ) := rfl

@[simp] theorem inverseConformal_symm_apply {u v w t : ℝ}
    (huv : u < v) (hvw : v < w) (hwt : w < t) (z : ℂ) :
    (inverseConformal huv hvw hwt).homeomorph.symm z =
      tail (realMap u v) (realMap u w) (realMap u t) (map u z) := rfl

/-- The extension across the two finite electrode edges. -/
def closedInverse (u v w t : ℝ) (ζ : ℂ) : ℂ :=
  inverse u (SlitCubicClosedChart.closedInverse (realMap u v) (realMap u w) (realMap u t) ζ)

theorem cubicClosedInverse_ne_zero {u v w t : ℝ}
    (huv : u < v) (hvw : v < w) (hwt : w < t) {ζ : ℂ}
    (hζ : ζ ∈ SlitCubicClosedChart.closedHorizontalBand (width u v w t) (height u v w t)) :
    SlitCubicClosedChart.closedInverse (realMap u v) (realMap u w) (realMap u t) ζ ≠ 0 := by
  intro he
  have hm := SlitCubicClosedChart.closedInverse_mem_source
    (first_lt_second huv hvw) (second_lt_third huv hvw hwt) hζ
  rw [he] at hm
  rcases SlitCubicClosedChart.real_closedSource_cases
    (first_lt_second huv hvw) (second_lt_third huv hvw hwt) (x := 0) hm with hh | hh
  · exact (not_lt_of_ge (realMap_neg huv).le) hh
  · exact (not_lt_of_ge (realMap_neg (huv.trans (hvw.trans hwt))).le) hh.2

theorem closedInverse_continuousOn {u v w t : ℝ}
    (huv : u < v) (hvw : v < w) (hwt : w < t) :
    ContinuousOn (closedInverse u v w t)
      (SlitCubicClosedChart.closedHorizontalBand (width u v w t) (height u v w t)) := by
  intro ζ hζ
  exact (inverse_hasDerivAt u (cubicClosedInverse_ne_zero huv hvw hwt hζ)).continuousAt.comp_continuousWithinAt
    (SlitCubicClosedChart.closedInverse_continuousOn
      (first_lt_second huv hvw) (second_lt_third huv hvw hwt) ζ hζ)

theorem closedInverse_mem_closedUpper {u v w t : ℝ}
    (huv : u < v) (hvw : v < w) (hwt : w < t) {ζ : ℂ}
    (hζ : ζ ∈ SlitCubicClosedChart.closedHorizontalBand (width u v w t) (height u v w t)) :
    closedInverse u v w t ζ ∈ closedUpper := by
  change 0 ≤ (inverse u _).im
  rw [inverse_im]
  exact div_nonneg (SlitCubicClosedChart.closedInverse_mem_source
    (first_lt_second huv hvw) (second_lt_third huv hvw hwt) hζ).1 (Complex.normSq_nonneg _)

theorem closedInverse_mem_upper {u v w t : ℝ}
    (huv : u < v) (hvw : v < w) (hwt : w < t) {ζ : ℂ}
    (hζ : ζ ∈ openRectangle (width u v w t) (height u v w t)) :
    closedInverse u v w t ζ ∈ upper :=
  inverse_mem_upper u (SlitCubicClosedChart.closedInverse_mem_upper
    (first_lt_second huv hvw) (second_lt_third huv hvw hwt) hζ)

theorem closedInverse_left_edge {u v w t y : ℝ}
    (huv : u < v) (hvw : v < w) (hwt : w < t)
    (hy : y ∈ Ioo (-height u v w t) 0) :
    (closedInverse u v w t ((y:ℂ)*Complex.I)).im = 0 ∧
      (closedInverse u v w t ((y:ℂ)*Complex.I)).re ∈ Ioo u v := by
  have hh := SlitCubicClosedChart.closedInverse_left_edge
    (first_lt_second huv hvw) (second_lt_third huv hvw hwt) hy
  let q := SlitCubicClosedChart.closedInverse (realMap u v) (realMap u w) (realMap u t)
    ((y:ℂ)*Complex.I)
  have he : q = (q.re:ℂ) := by apply Complex.ext <;> simp [q,hh.1]
  change (inverse u q).im = 0 ∧ (inverse u q).re ∈ Ioo u v
  rw [he,inverse_ofReal]
  simpa only [Complex.ofReal_im,Complex.ofReal_re,true_and] using inverse_real_left huv hh.2

theorem closedInverse_right_edge {u v w t y : ℝ}
    (huv : u < v) (hvw : v < w) (hwt : w < t)
    (hy : y ∈ Ioo (-height u v w t) 0) :
    (closedInverse u v w t ((width u v w t:ℂ)+(y:ℂ)*Complex.I)).im = 0 ∧
      (closedInverse u v w t ((width u v w t:ℂ)+(y:ℂ)*Complex.I)).re ∈ Ioo w t := by
  have hh := SlitCubicClosedChart.closedInverse_right_edge
    (first_lt_second huv hvw) (second_lt_third huv hvw hwt) hy
  let q := SlitCubicClosedChart.closedInverse (realMap u v) (realMap u w) (realMap u t)
    ((width u v w t:ℂ)+(y:ℂ)*Complex.I)
  have he : q = (q.re:ℂ) := by apply Complex.ext <;> simp [q,width,hh.1]
  change (inverse u q).im = 0 ∧ (inverse u q).re ∈ Ioo w t
  rw [he,inverse_ofReal]
  simpa only [Complex.ofReal_im,Complex.ofReal_re,true_and,q,width] using inverse_real_gap huv hvw hwt hh.2

theorem closedInverse_eq_inverseConformal {u v w t : ℝ}
    (huv : u < v) (hvw : v < w) (hwt : w < t) {ζ : ℂ}
    (hζ : ζ ∈ openRectangle (width u v w t) (height u v w t)) :
    closedInverse u v w t ζ = (inverseConformal huv hvw hwt).homeomorph ζ := by
  simp only [closedInverse,inverseConformal_apply,
    SlitCubicClosedChart.closedInverse_eq_rectangleChart_symm
      (first_lt_second huv hvw) (second_lt_third huv hvw hwt) hζ]

theorem closedInverse_injOn {u v w t : ℝ}
    (huv : u < v) (hvw : v < w) (hwt : w < t) :
    InjOn (closedInverse u v w t)
      (SlitCubicClosedChart.closedHorizontalBand (width u v w t) (height u v w t)) := by
  intro ζ hζ η hη he
  exact SlitCubicClosedChart.closedInverse_injOn
    (first_lt_second huv hvw) (second_lt_third huv hvw hwt) hζ hη (inverse_injective u he)

/-- A velocity formula continuous all the way to the two electrode edges. -/
def closedVelocity (u v w t : ℝ) (ζ : ℂ) : ℂ :=
  let q := SlitCubicClosedChart.closedInverse (realMap u v) (realMap u w) (realMap u t) ζ
  (q^2)⁻¹ * -(upperRoot (realMap u v) q * upperRoot (realMap u w) q * upperRoot (realMap u t) q)

theorem closedVelocity_continuousOn {u v w t : ℝ}
    (huv : u < v) (hvw : v < w) (hwt : w < t) :
    ContinuousOn (closedVelocity u v w t)
      (SlitCubicClosedChart.closedHorizontalBand (width u v w t) (height u v w t)) := by
  have hc := SlitCubicClosedChart.closedInverse_continuousOn
    (first_lt_second huv hvw) (second_lt_third huv hvw hwt)
  exact ((hc.pow 2).inv₀ (fun ζ hζ => pow_ne_zero _
    (cubicClosedInverse_ne_zero huv hvw hwt hζ))).mul
    ((((upperRoot_continuous _).comp_continuousOn hc).mul
      ((upperRoot_continuous _).comp_continuousOn hc)).mul
      ((upperRoot_continuous _).comp_continuousOn hc)).neg

theorem closedInverse_hasDerivAt {u v w t : ℝ}
    (huv : u < v) (hvw : v < w) (hwt : w < t) {ζ : ℂ}
    (hζ : ζ ∈ openRectangle (width u v w t) (height u v w t)) :
    HasDerivAt (closedInverse u v w t) (closedVelocity u v w t ζ) ζ := by
  exact (inverse_hasDerivAt u (cubicClosedInverse_ne_zero huv hvw hwt
    (SlitCubicClosedChart.openRectangle_subset_closedHorizontalBand _ _ hζ))).comp ζ
      (SlitCubicClosedChart.closedInverse_hasDerivAt
        (first_lt_second huv hvw) (second_lt_third huv hvw hwt) hζ)

theorem inverseConformal_derivative {u v w t : ℝ}
    (huv : u < v) (hvw : v < w) (hwt : w < t) {ζ : ℂ}
    (hζ : ζ ∈ openRectangle (width u v w t) (height u v w t)) :
    (inverseConformal huv hvw hwt).derivative ζ = closedVelocity u v w t ζ := by
  simp only [inverseConformal,closedVelocity,SlitCubicLowerEnergy.inverseVelocity,
    SlitCubicClosedChart.closedInverse_eq_rectangleChart_symm
      (first_lt_second huv hvw) (second_lt_third huv hvw hwt) hζ]

end
end SlitFourPointChart
