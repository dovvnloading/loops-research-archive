import SlitDiskCayley
import SlitCubicBoundaryRange
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Topology.Order.IntermediateValue

/-!
# Fixed-interval expansion of the actual finite-disk cubic periods

The squared Cayley substitution moves all branch points. Its Jacobian
reduces their periods to an explicit smooth weight on the original fixed
intervals. The derivative at reciprocal radius zero is the negative first
moment of the cubic kernel.
-/

namespace SlitDiskPeriodExpansion

open Set Filter MeasureTheory
open SlitCubicCalibration SlitCubicBoundary SlitCubicBoundaryRange
open scoped Topology
noncomputable section

def radicand (a b c q x : ℝ) : ℝ :=
  (1 - q^2*a*x) * (1 - q^2*b*x) * (1 - q^2*c*x)

def radicandDerivative (a b c q x : ℝ) : ℝ :=
  -2*q*x * (a*(1-q^2*b*x)*(1-q^2*c*x) +
    b*(1-q^2*a*x)*(1-q^2*c*x) + c*(1-q^2*a*x)*(1-q^2*b*x))

def weight (a b c q x : ℝ) : ℝ :=
  (1-q*x) / Real.sqrt (radicand a b c q x)

def weightDerivative (a b c q x : ℝ) : ℝ :=
  ((-x) * Real.sqrt (radicand a b c q x) -
    (1-q*x) * (radicandDerivative a b c q x / (2*Real.sqrt (radicand a b c q x)))) /
      (Real.sqrt (radicand a b c q x))^2

def weightedInterval (a b c l u q : ℝ) : ℝ :=
  ∫ x in Ioo l u, weight a b c q x * realDensity a b c x

def moment (a b c l u : ℝ) : ℝ :=
  ∫ x in Ioo l u, x * realDensity a b c x

/-- Affine normalization of the squared Cayley cut map, at reciprocal
radius `q`. Its value at zero is the original cut. -/
def normalizedMap (q x : ℝ) : ℝ := x / (1+q*x)^2

def normalizedDerivative (q x : ℝ) : ℝ := (1-q*x)/(1+q*x)^3

def commonFactor (a b c q : ℝ) : ℝ := (1+q*a)*(1+q*b)*(1+q*c)

theorem normalizedMap_inv_eq {R : ℝ} (hR : R ≠ 0) (x : ℝ) :
    normalizedMap (1/R) x = R^2*x/(R+x)^2 := by
  have he : 1+(1/R)*x = (R+x)/R := by field_simp
  rw [normalizedMap, he, div_pow, div_div_eq_mul_div]
  ring

theorem invRadius_small {R x : ℝ} (hR : 0 < R) (hx : x ∈ Ioo (-R) R) :
    |(1/R)*x| < 1 := by
  rw [one_div_mul_eq_div, abs_div, abs_of_pos hR]
  exact (div_lt_one hR).mpr (abs_lt.mpr hx)

private theorem one_add_pos {q x : ℝ} (hx : |q*x| < 1) : 0 < 1+q*x := by
  linarith [(abs_lt.mp hx).1]

private theorem one_sub_pos {q x : ℝ} (hx : |q*x| < 1) : 0 < 1-q*x := by
  linarith [(abs_lt.mp hx).2]

private theorem one_sub_product_pos {q x p : ℝ} (hx : |q*x| < 1) (hp : |q*p| < 1) :
    0 < 1-q^2*x*p := by
  have hh : |(q*x)*(q*p)| < 1 := by
    rw [abs_mul]
    nlinarith [abs_nonneg (q*x), abs_nonneg (q*p)]
  have hu := (abs_lt.mp hh).2
  nlinarith

theorem commonFactor_pos {a b c q : ℝ}
    (ha : |q*a| < 1) (hb : |q*b| < 1) (hc : |q*c| < 1) : 0 < commonFactor a b c q :=
  mul_pos (mul_pos (one_add_pos ha) (one_add_pos hb)) (one_add_pos hc)

theorem normalizedMap_sub {q x p : ℝ} (hx : |q*x| < 1) (hp : |q*p| < 1) :
    normalizedMap q x - normalizedMap q p =
      (x-p)*(1-q^2*x*p)/((1+q*x)^2*(1+q*p)^2) := by
  unfold normalizedMap
  have hX : (1+q*x)^2 ≠ 0 := pow_ne_zero 2 (one_add_pos hx).ne'
  have hP : (1+q*p)^2 ≠ 0 := pow_ne_zero 2 (one_add_pos hp).ne'
  rw [div_sub_div x p hX hP]
  congr 1
  ring

theorem normalizedMap_strictMonoOn (q : ℝ) :
    StrictMonoOn (normalizedMap q) {x | |q*x| < 1} := by
  intro x hx y hy hxy
  apply sub_pos.mp
  rw [normalizedMap_sub hy hx]
  exact div_pos (mul_pos (sub_pos.mpr hxy) (one_sub_product_pos hy hx))
    (mul_pos (sq_pos_of_pos (one_add_pos hy)) (sq_pos_of_pos (one_add_pos hx)))

theorem normalizedMap_hasDerivAt {q x : ℝ} (hx : |q*x| < 1) :
    HasDerivAt (normalizedMap q) (normalizedDerivative q x) x := by
  have h := (hasDerivAt_id x).div
    ((((hasDerivAt_id x).const_mul q).const_add 1).pow 2)
    (pow_ne_zero 2 (one_add_pos hx).ne')
  apply h.congr_deriv
  dsimp [normalizedDerivative]
  field_simp [(one_add_pos hx).ne']
  ring

private theorem smallOn_Icc {q l u x : ℝ} (hl : |q*l| < 1) (hu : |q*u| < 1)
    (hx : x ∈ Icc l u) : |q*x| < 1 := by
  apply abs_lt.mpr
  by_cases hq : 0 ≤ q
  · exact ⟨(abs_lt.mp hl).1.trans_le (mul_le_mul_of_nonneg_left hx.1 hq),
      (mul_le_mul_of_nonneg_left hx.2 hq).trans_lt (abs_lt.mp hu).2⟩
  · have hq' : q ≤ 0 := (lt_of_not_ge hq).le
    exact ⟨(abs_lt.mp hu).1.trans_le (mul_le_mul_of_nonpos_left hx.2 hq'),
      (mul_le_mul_of_nonpos_left hx.1 hq').trans_lt (abs_lt.mp hl).2⟩

theorem normalizedMap_image_Ioo {q l u : ℝ} (hlu : l ≤ u)
    (hl : |q*l| < 1) (hu : |q*u| < 1) :
    normalizedMap q '' Ioo l u = Ioo (normalizedMap q l) (normalizedMap q u) := by
  apply ContinuousOn.image_Ioo_of_strictMonoOn hlu
  · exact fun x hx => (normalizedMap_hasDerivAt (smallOn_Icc hl hu hx)).continuousAt.continuousWithinAt
  · exact (normalizedMap_strictMonoOn q).mono (fun _ hx => smallOn_Icc hl hu hx)

private theorem realDensity_sq (a b c x : ℝ) :
    (realDensity a b c x)^2 = 1/(|x-a| * |x-b| * |x-c|) := by
  simp only [realDensity, div_pow, one_pow, mul_pow, Real.sq_sqrt (abs_nonneg _)]

private theorem normalizedMap_abs_sub {q x p : ℝ} (hx : |q*x| < 1) (hp : |q*p| < 1) :
    |normalizedMap q x - normalizedMap q p| =
      |x-p| * (1-q^2*x*p)/((1+q*x)^2*(1+q*p)^2) := by
  rw [normalizedMap_sub hx hp, abs_div, abs_mul,
    abs_of_pos (one_sub_product_pos hx hp),
    abs_of_pos (mul_pos (sq_pos_of_pos (one_add_pos hx)) (sq_pos_of_pos (one_add_pos hp)))]

/-- The normalized squared-Cayley Jacobian cancels the moving cubic
singularities against a smooth fixed-interval weight. -/
theorem normalized_density_jacobian {a b c q x : ℝ}
    (ha : |q*a| < 1) (hb : |q*b| < 1) (hc : |q*c| < 1) (hx : |q*x| < 1)
    (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) :
    normalizedDerivative q x *
      realDensity (normalizedMap q a) (normalizedMap q b) (normalizedMap q c) (normalizedMap q x) =
      commonFactor a b c q * weight a b c q x * realDensity a b c x := by
  have hpa := one_sub_product_pos hx ha
  have hpb := one_sub_product_pos hx hb
  have hpc := one_sub_product_pos hx hc
  have hP : 0 < radicand a b c q x := by
    simpa only [radicand, mul_assoc, mul_left_comm, mul_comm] using mul_pos (mul_pos hpa hpb) hpc
  have hJ : 0 < normalizedDerivative q x :=
    div_pos (one_sub_pos hx) (pow_pos (one_add_pos hx) 3)
  have hW : 0 < weight a b c q x := div_pos (one_sub_pos hx) (Real.sqrt_pos.mpr hP)
  have hnL : 0 ≤ normalizedDerivative q x *
      realDensity (normalizedMap q a) (normalizedMap q b) (normalizedMap q c) (normalizedMap q x) :=
    mul_nonneg hJ.le (SlitCubicIntegrability.kernel_nonneg _ _ _ _)
  have hnR : 0 ≤ commonFactor a b c q * weight a b c q x * realDensity a b c x :=
    mul_nonneg (mul_nonneg (commonFactor_pos ha hb hc).le hW.le)
      (SlitCubicIntegrability.kernel_nonneg a b c x)
  apply (sq_eq_sq₀ hnL hnR).mp
  rw [mul_pow, mul_pow, mul_pow, realDensity_sq, realDensity_sq,
    normalizedMap_abs_sub hx ha, normalizedMap_abs_sub hx hb, normalizedMap_abs_sub hx hc]
  simp only [normalizedDerivative, commonFactor, weight, div_pow, mul_pow,
    Real.sq_sqrt hP.le]
  have hxa' : |x-a| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hxa)
  have hxb' : |x-b| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hxb)
  have hxc' : |x-c| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hxc)
  dsimp [radicand]
  field_simp [(one_add_pos hx).ne', (one_add_pos ha).ne', (one_add_pos hb).ne',
    (one_add_pos hc).ne', hpa.ne', hpb.ne', hpc.ne', hxa', hxb', hxc']

theorem normalized_interval_eq {a b c q l u : ℝ} (hlu : l ≤ u)
    (ha : |q*a| < 1) (hb : |q*b| < 1) (hc : |q*c| < 1)
    (hl : |q*l| < 1) (hu : |q*u| < 1)
    (havoid : ∀ x ∈ Ioo l u, x ≠ a ∧ x ≠ b ∧ x ≠ c) :
    (∫ y in Ioo (normalizedMap q l) (normalizedMap q u),
      realDensity (normalizedMap q a) (normalizedMap q b) (normalizedMap q c) y) =
      commonFactor a b c q * weightedInterval a b c l u q := by
  have hs : Ioo l u ⊆ {x | |q*x| < 1} :=
    fun _ hx => smallOn_Icc hl hu (Ioo_subset_Icc_self hx)
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun x hx => (normalizedMap_hasDerivAt (hs hx)).hasDerivWithinAt)
    ((normalizedMap_strictMonoOn q).mono hs).injOn
    (realDensity (normalizedMap q a) (normalizedMap q b) (normalizedMap q c))
  rw [normalizedMap_image_Ioo hlu hl hu] at h
  rw [h]
  calc
    _ = ∫ x in Ioo l u,
        commonFactor a b c q * (weight a b c q x * realDensity a b c x) := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      have hJ : 0 ≤ normalizedDerivative q x :=
        (div_pos (one_sub_pos (hs hx)) (pow_pos (one_add_pos (hs hx)) 3)).le
      obtain ⟨hxa, hxb, hxc⟩ := havoid x hx
      simpa only [abs_of_nonneg hJ, smul_eq_mul, mul_assoc] using
        normalized_density_jacobian ha hb hc (hs hx) hxa hxb hxc
    _ = _ := integral_const_mul _ _

/-- Exact normal form of the first transformed cubic period. -/
theorem normalized_period_eq {a b c q : ℝ} (hab : a < b) (hbc : b < c)
    (ha : |q*a| < 1) (hb : |q*b| < 1) (hc : |q*c| < 1) :
    period (normalizedMap q a) (normalizedMap q b) (normalizedMap q c) =
      commonFactor a b c q * weightedInterval a b c a b q := by
  exact normalized_interval_eq hab.le ha hb hc ha hb
    (fun x hx => ⟨hx.1.ne', hx.2.ne, (hx.2.trans hbc).ne⟩)

/-- Exact normal form of the second transformed cubic period. -/
theorem normalized_height_eq {a b c q : ℝ} (hab : a < b) (hbc : b < c)
    (ha : |q*a| < 1) (hb : |q*b| < 1) (hc : |q*c| < 1) :
    height (normalizedMap q a) (normalizedMap q b) (normalizedMap q c) =
      commonFactor a b c q * weightedInterval a b c b c q := by
  exact normalized_interval_eq hbc.le ha hb hc hb hc
    (fun x hx => ⟨(hab.trans hx.1).ne', hx.1.ne', hx.2.ne⟩)

/-- The moving-cut period ratio is exactly a quotient of smooth
fixed-interval integrals, with the common Jacobian factor canceled. -/
theorem normalized_ratio_eq {a b c q : ℝ} (hab : a < b) (hbc : b < c)
    (ha : |q*a| < 1) (hb : |q*b| < 1) (hc : |q*c| < 1) :
    height (normalizedMap q a) (normalizedMap q b) (normalizedMap q c) /
        (2 * period (normalizedMap q a) (normalizedMap q b) (normalizedMap q c)) =
      weightedInterval a b c b c q / (2 * weightedInterval a b c a b q) := by
  rw [normalized_height_eq hab hbc ha hb hc, normalized_period_eq hab hbc ha hb hc]
  rw [show 2 * (commonFactor a b c q * weightedInterval a b c a b q) =
    commonFactor a b c q * (2 * weightedInterval a b c a b q) by ring]
  exact mul_div_mul_left _ _ (commonFactor_pos ha hb hc).ne'

@[simp] theorem radicand_zero (a b c x : ℝ) : radicand a b c 0 x = 1 := by
  simp [radicand]

@[simp] theorem weight_zero (a b c x : ℝ) : weight a b c 0 x = 1 := by
  simp [weight]

@[simp] theorem weightDerivative_zero (a b c x : ℝ) : weightDerivative a b c 0 x = -x := by
  simp [weightDerivative, radicandDerivative]

@[simp] theorem weightedInterval_zero (a b c l u : ℝ) :
    weightedInterval a b c l u 0 = ∫ x in Ioo l u, realDensity a b c x := by
  simp only [weightedInterval, weight_zero, one_mul]

theorem radicand_hasDerivAt (a b c q x : ℝ) :
    HasDerivAt (fun t => radicand a b c t x) (radicandDerivative a b c q x) q := by
  have hp (p : ℝ) : HasDerivAt (fun t : ℝ => 1-t^2*p*x) (-2*q*p*x) q := by
    convert! ((hasDerivAt_const q (1 : ℝ)).sub (((hasDerivAt_id q).pow 2).mul_const p |>.mul_const x)) using 1
    simp only [id_eq, pow_one, Nat.cast_ofNat, Nat.reduceSub, mul_one]
    ring
  have hd := ((hp a).mul (hp b)).mul (hp c)
  convert! hd using 1
  dsimp [radicandDerivative, Pi.mul_apply]
  ring

theorem weight_hasDerivAt {a b c q x : ℝ} (hp : 0 < radicand a b c q x) :
    HasDerivAt (fun t => weight a b c t x) (weightDerivative a b c q x) q := by
  have hs := (radicand_hasDerivAt a b c q x).sqrt hp.ne'
  have hn : Real.sqrt (radicand a b c q x) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  simpa only [weight, weightDerivative, mul_one, one_mul, zero_sub, Pi.sub_apply,
    Pi.div_apply, id_eq] using!
    ((hasDerivAt_const q (1 : ℝ)).sub ((hasDerivAt_id q).mul_const x)).div hs hn

theorem weight_measurable (a b c q : ℝ) : Measurable (weight a b c q) := by
  unfold weight radicand
  fun_prop

theorem weightDerivative_measurable (a b c q : ℝ) : Measurable (weightDerivative a b c q) := by
  unfold weightDerivative radicandDerivative radicand
  fun_prop

private theorem weightDerivative_continuousAt {a b c : ℝ} {p : ℝ × ℝ}
    (hp : 0 < radicand a b c p.1 p.2) :
    ContinuousAt (fun p : ℝ × ℝ => weightDerivative a b c p.1 p.2) p := by
  have hP : Continuous (fun p : ℝ × ℝ => radicand a b c p.1 p.2) := by
    unfold radicand
    fun_prop
  have hD : Continuous (fun p : ℝ × ℝ => radicandDerivative a b c p.1 p.2) := by
    unfold radicandDerivative
    fun_prop
  have hs := (Real.continuous_sqrt.comp hP).continuousAt (x := p)
  have hn : Real.sqrt (radicand a b c p.1 p.2) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  exact (((continuous_snd.continuousAt.neg.mul hs).sub
    ((continuous_const.sub (continuous_fst.mul continuous_snd)).continuousAt.mul
      (hD.continuousAt.div (continuous_const.continuousAt.mul hs)
        (mul_ne_zero (by norm_num) hn)))).div (hs.pow 2) (pow_ne_zero 2 hn))

private theorem positive_radicand_rectangle (a b c l u : ℝ) :
    ∃ r : ℝ, 0 < r ∧ ∀ q ∈ Metric.closedBall (0 : ℝ) r,
      ∀ x ∈ Icc l u, 0 < radicand a b c q x := by
  have hopen : IsOpen {p : ℝ × ℝ | 0 < radicand a b c p.1 p.2} := by
    apply isOpen_lt continuous_const
    unfold radicand
    fun_prop
  have hsub : ({0} : Set ℝ) ×ˢ Icc l u ⊆ {p : ℝ × ℝ | 0 < radicand a b c p.1 p.2} := by
    rintro ⟨q, x⟩ ⟨hq, hx⟩
    rcases hq with rfl
    simp
  obtain ⟨U, V, hU, hV, hzero, hI, hUV⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc hopen hsub
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (hzero (mem_singleton 0)))
  refine ⟨r/2, half_pos hr, ?_⟩
  intro q hq x hx
  exact hUV (show (q,x) ∈ U ×ˢ V from
    ⟨hball (lt_of_le_of_lt hq (half_lt_self hr)), hI hx⟩)

/-- Differentiation under the actual integrable cubic kernel takes place
on fixed intervals, with a compact uniform bound for the explicit weight. -/
theorem weightedInterval_hasDerivAt_zero {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (l u : ℝ) : HasDerivAt (weightedInterval a b c l u) (-moment a b c l u) 0 := by
  obtain ⟨r, hr, hpositive⟩ := positive_radicand_rectangle a b c l u
  let K : Set (ℝ × ℝ) := Metric.closedBall (0 : ℝ) r ×ˢ Icc l u
  have hc : ContinuousOn (fun p : ℝ × ℝ => ‖weightDerivative a b c p.1 p.2‖) K := by
    intro p hp
    exact (weightDerivative_continuousAt (hpositive p.1 hp.1 p.2 hp.2)).norm.continuousWithinAt
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : ℝ) r).prod isCompact_Icc).bddAbove_image hc
  have hCbound : ∀ q ∈ Metric.closedBall (0 : ℝ) r, ∀ x ∈ Icc l u,
      ‖weightDerivative a b c q x‖ ≤ |C| := by
    intro q hq x hx
    exact (hC (mem_image_of_mem _ (show (q,x) ∈ K from ⟨hq,hx⟩))).trans (le_abs_self C)
  have hi := (realDensity_integrable hab hbc).integrableOn (s := Ioo l u)
  have hkernel : Measurable (realDensity a b c) := SlitCubicIntegrability.kernel_measurable a b c
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioo l u))
    (F := fun q x => weight a b c q x * realDensity a b c x)
    (F' := fun q x => weightDerivative a b c q x * realDensity a b c x)
    (bound := fun x => |C| * realDensity a b c x)
    (Metric.ball_mem_nhds (0 : ℝ) hr)
    (Eventually.of_forall (fun q => ((weight_measurable a b c q).mul hkernel).aestronglyMeasurable))
    (by simpa only [weight_zero, one_mul] using! hi)
    (((weightDerivative_measurable a b c 0).mul hkernel).aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      intro q hq
      rw [norm_mul, Real.norm_eq_abs (realDensity a b c x),
        abs_of_nonneg (show 0 ≤ realDensity a b c x from SlitCubicIntegrability.kernel_nonneg a b c x)]
      exact mul_le_mul_of_nonneg_right (hCbound q (Metric.ball_subset_closedBall hq) x
        (Ioo_subset_Icc_self hx)) (SlitCubicIntegrability.kernel_nonneg a b c x))
    (hi.const_mul |C|)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      intro q hq
      exact (weight_hasDerivAt (hpositive q (Metric.ball_subset_closedBall hq) x
        (Ioo_subset_Icc_self hx))).mul_const (realDensity a b c x))
  change HasDerivAt (fun q => weightedInterval a b c l u q) _ 0
  simpa only [weightedInterval, weightDerivative_zero, neg_mul, integral_neg, moment] using! hd.2

end
end SlitDiskPeriodExpansion
