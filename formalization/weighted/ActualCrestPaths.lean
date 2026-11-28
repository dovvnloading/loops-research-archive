import GlobalCrestPhysical
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Actual circular paths through four central returns

The secant of the complete normalized return determines its imaginary
part exactly.  On the selected circle this gives the nonreal interior
of each image, including the fourth image of the component cut off at
the unique crossing.  All source inclusions concern the same proper
central component as the existing parent construction.
-/

namespace ActualCrestPaths

open Set Function Filter
open scoped Topology ComplexConjugate
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn LimitingCrest
open GlobalCrestCrossing GlobalCrestEstimates GlobalCrestClassification
open GlobalCrestSourceGates GlobalCrestFinalCut ActualCrestProperReturn
open QuadraticCrestDividedDifference ThreeReturnParent
open LoopsLimitingCrestParameter

noncomputable section

theorem normalizedReturn_conj (c : ℝ) (p : ℕ) (z : ℂ) :
    normalizedReturn c p (conj z) = conj (normalizedReturn c p z) := by
  have hi (n : ℕ) (w : ℂ) :
      ((quadraticMap c)^[n]) (conj w) = conj (((quadraticMap c)^[n]) w) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [iterate_succ_apply', iterate_succ_apply', ih]
      simp [quadraticMap]
  unfold normalizedReturn
  rw [show (criticalValue c p : ℂ) * conj z =
      conj ((criticalValue c p : ℂ) * z) by simp, hi]
  simp

/-- The imaginary part has the exact quadratic sign law throughout the
certified disk, despite the high degree of the literal return. -/
theorem normalizedReturn_im (c : ℝ) (p : ℕ) (hp : 0 < p)
    (hd : criticalValue c p ≠ 0) (z : ℂ) :
    (normalizedReturn c p z).im =
      2*z.re*z.im*(normalizedSecant c p z (conj z)).re := by
  have h := congrArg Complex.im (normalized_difference c p hp hd z (conj z))
  rw [normalizedReturn_conj] at h
  simp only [pow_two, Complex.sub_im, Complex.conj_im, Complex.mul_im,
    Complex.sub_re, Complex.mul_re, Complex.conj_re] at h
  nlinarith only [h]

theorem actual_im_sign {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : ‖z‖ ≤ 23/20) :
    (normalizedReturn c p z).im = 0 ↔ z.re = 0 ∨ z.im = 0 := by
  have hs := actual_secant_re_neg hp hc (hz.trans (by norm_num))
    (show ‖conj z‖ ≤ 3/2 by simpa using hz.trans (show (23/20 : ℝ) ≤ 3/2 by norm_num))
  rw [normalizedReturn_im c p (by omega) hc.2.1.ne']
  have hne : (normalizedSecant c p z (conj z)).re ≠ 0 := by linarith
  simp [mul_eq_zero, hne]

theorem actual_im_pos_of_neg_pos {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : ‖z‖ ≤ 23/20)
    (hr : z.re < 0) (hi : 0 < z.im) :
    0 < (normalizedReturn c p z).im := by
  have hs := actual_secant_re_neg hp hc (hz.trans (by norm_num))
    (show ‖conj z‖ ≤ 3/2 by simpa using hz.trans (show (23/20 : ℝ) ≤ 3/2 by norm_num))
  rw [normalizedReturn_im c p (by omega) hc.2.1.ne']
  exact mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos (by linarith) hi) (by linarith)

theorem actual_im_neg_of_pos_pos {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : ‖z‖ ≤ 23/20)
    (hr : 0 < z.re) (hi : 0 < z.im) :
    (normalizedReturn c p z).im < 0 := by
  have hs := actual_secant_re_neg hp hc (hz.trans (by norm_num))
    (show ‖conj z‖ ≤ 3/2 by simpa using hz.trans (show (23/20 : ℝ) ≤ 3/2 by norm_num))
  rw [normalizedReturn_im c p (by omega) hc.2.1.ne']
  exact mul_neg_of_pos_of_neg (mul_pos (by linarith) hi) (by linarith)

theorem actual_im_pos_of_pos_neg {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : ‖z‖ ≤ 23/20)
    (hr : 0 < z.re) (hi : z.im < 0) :
    0 < (normalizedReturn c p z).im := by
  have hs := actual_secant_re_neg hp hc (hz.trans (by norm_num))
    (show ‖conj z‖ ≤ 3/2 by simpa using hz.trans (show (23/20 : ℝ) ≤ 3/2 by norm_num))
  rw [normalizedReturn_im c p (by omega) hc.2.1.ne']
  exact mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg (by linarith) hi) (by linarith)

theorem circlePoint_initialDisk {s u : ℝ}
    (hs : s ∈ Icc (1/16 : ℝ) (133/2000)) (hu : u ∈ Icc (-1 : ℝ) 1) :
    circlePoint s u ∈ initialDisk := by
  change ‖circlePoint s u+(3/4 : ℂ)‖ ≤ 133/2000
  rw [circle_radius (by linarith [hs.1]) hu]
  exact hs.2

theorem circlePoint_re_neg {s u : ℝ}
    (hs : s ∈ Radius) (hu : u ∈ Icc (-1 : ℝ) 1) :
    (circlePoint s u).re < 0 := by
  have hsu := mul_le_mul_of_nonneg_left hu.2 (show 0 ≤ s by linarith [hs.1])
  simp only [circlePoint, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    zero_mul, sub_zero, add_zero]
  nlinarith [hs.2]

theorem circlePoint_im_pos {s u : ℝ}
    (hs : s ∈ Radius) (hu : u ∈ Ioo (-1 : ℝ) 1) :
    0 < (circlePoint s u).im := by
  have hu2 : u^2 < 1 := by
    nlinarith [mul_pos (by linarith [hu.2] : 0 < 1-u) (by linarith [hu.1] : 0 < 1+u)]
  simp only [circlePoint, Complex.add_im, Complex.ofReal_im,
    Complex.mul_im, Complex.ofReal_re, Complex.I_re, Complex.I_im, mul_one,
    mul_zero, add_zero, zero_add]
  exact mul_pos (by linarith [hs.1]) (Real.sqrt_pos.mpr (by linarith))

theorem actual_first_arc_im_pos {p : ℕ} (hp : 17 ≤ p) {c s u : ℝ}
    (hc : ActualTip p c) (hs : s ∈ Radius) (hu : u ∈ Ioo (-1 : ℝ) 1) :
    0 < (normalizedReturn c p (circlePoint s u)).im :=
  actual_im_pos_of_neg_pos hp hc (circlePoint_full_disk hs ⟨hu.1.le,hu.2.le⟩)
    (circlePoint_re_neg hs ⟨hu.1.le,hu.2.le⟩) (circlePoint_im_pos hs hu)

theorem realAngle_mem {p : ℕ} {c : ℝ} (F : Family p c) (s : ℝ) :
    realAngle F s ∈ Ioo (-1/10 : ℝ) (1/10) := F.angle_mem _

theorem realAngle_crossing {p : ℕ} {c s : ℝ} (F : Family p c)
    (hs : s ∈ Radius) :
    (normalizedReturn c p (circlePoint s (realAngle F s))).re = 0 := by
  simpa only [realAngle, radiusProjection_eq hs] using F.crossing ⟨s,hs⟩

theorem circlePoint_cos (s : ℝ) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) Real.pi) :
    circlePoint s (Real.cos θ) =
      (-3/4 : ℂ)+(s : ℂ)*((Real.cos θ : ℂ)+(Real.sin θ : ℂ)*Complex.I) := by
  have he : 1-(Real.cos θ)^2 = (Real.sin θ)^2 := by
    nlinarith only [Real.sin_sq_add_cos_sq θ]
  have hs : Real.sqrt (1-(Real.cos θ)^2) = Real.sin θ := by
    rw [he,Real.sqrt_sq_eq_abs,abs_of_nonneg (Real.sin_nonneg_of_mem_Icc hθ)]
  simp only [circlePoint,hs,Complex.ofReal_add,Complex.ofReal_div,Complex.ofReal_neg,
    Complex.ofReal_ofNat,Complex.ofReal_mul]
  ring

theorem cos_mem_closed_q_side {p : ℕ} {c s θ : ℝ} (F : Family p c)
    (hθ : θ ∈ Icc (0 : ℝ) (Real.arccos (realAngle F s))) :
    Real.cos θ ∈ Icc (realAngle F s) 1 := by
  have ha := realAngle_mem F s
  have hc : Real.cos (Real.arccos (realAngle F s)) = realAngle F s :=
    Real.cos_arccos (by linarith [ha.1]) (by linarith [ha.2])
  refine ⟨?_,Real.cos_le_one θ⟩
  rw [← hc]
  exact Real.cos_le_cos_of_nonneg_of_le_pi hθ.1 (Real.arccos_le_pi _) hθ.2

theorem cos_mem_open_q_side {p : ℕ} {c s θ : ℝ} (F : Family p c)
    (hθ : θ ∈ Ioo (0 : ℝ) (Real.arccos (realAngle F s))) :
    Real.cos θ ∈ Ioo (realAngle F s) 1 := by
  have ha := realAngle_mem F s
  have hc : Real.cos (Real.arccos (realAngle F s)) = realAngle F s :=
    Real.cos_arccos (by linarith [ha.1]) (by linarith [ha.2])
  have hθπ : θ ∈ Icc (0 : ℝ) Real.pi :=
    ⟨hθ.1.le,hθ.2.le.trans (Real.arccos_le_pi _)⟩
  constructor
  · rw [← hc]
    exact Real.strictAntiOn_cos hθπ
      ⟨Real.arccos_nonneg _,Real.arccos_le_pi _⟩ hθ.2
  · have h := Real.strictAntiOn_cos
      (show (0 : ℝ) ∈ Icc (0 : ℝ) Real.pi by exact ⟨le_rfl,Real.pi_pos.le⟩) hθπ hθ.1
    simpa only [Real.cos_zero] using h

theorem actual_q_side_re_pos {p : ℕ} (hp : 17 ≤ p) {c s u : ℝ}
    (hc : ActualTip p c) (F : Family p c) (hs : s ∈ Radius)
    (hu : u ∈ Icc (-1 : ℝ) 1) (ha : realAngle F s < u) :
    0 < (normalizedReturn c p (circlePoint s u)).re := by
  have ham := realAngle_mem F s
  by_cases hu0 : u ≤ 1/10
  · have hg := actual_crossing_growth hp hc hs ⟨ham.1.le,ham.2.le⟩
      ⟨by linarith [ham.1],hu0⟩ ha.le
    rw [realAngle_crossing F hs] at hg
    linarith
  · have hg := crossing_global_growth hc.2.2.2.1 hs
      (show (1/10 : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) hu
      (le_of_not_ge hu0)
    have hm := (crossing_endpoint_margins hc.2.2.2.1 hs).2
    have he := (Complex.abs_re_le_norm
      (normalizedReturn c p (circlePoint s u)-complexMap (kappa p c) (circlePoint s u))).trans
        (actual_return_error_small hp hc ((circlePoint_full_disk hs hu).trans (by norm_num)))
    have hq : (complexMap (kappa p c) (circlePoint s u)).re = crossing (kappa p c) s u := by
      rw [circle_image _ _ hu]; simp
    simp only [Complex.sub_re,hq] at he
    linarith [(abs_le.mp he).1]

theorem actual_w_side_re_neg {p : ℕ} (hp : 17 ≤ p) {c s u : ℝ}
    (hc : ActualTip p c) (F : Family p c) (hs : s ∈ Radius)
    (hu : u ∈ Icc (-1 : ℝ) 1) (ha : u < realAngle F s) :
    (normalizedReturn c p (circlePoint s u)).re < 0 := by
  have ham := realAngle_mem F s
  by_cases hu0 : -1/10 ≤ u
  · have hg := actual_crossing_growth hp hc hs
      ⟨hu0,by linarith [ham.2]⟩ ⟨ham.1.le,ham.2.le⟩ ha.le
    rw [realAngle_crossing F hs] at hg
    linarith
  · have hg := crossing_global_growth hc.2.2.2.1 hs hu
      (show (-1/10 : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num)
      (le_of_not_ge hu0)
    have hm := (crossing_endpoint_margins hc.2.2.2.1 hs).1
    have he := (Complex.abs_re_le_norm
      (normalizedReturn c p (circlePoint s u)-complexMap (kappa p c) (circlePoint s u))).trans
        (actual_return_error_small hp hc ((circlePoint_full_disk hs hu).trans (by norm_num)))
    have hq : (complexMap (kappa p c) (circlePoint s u)).re = crossing (kappa p c) s u := by
      rw [circle_image _ _ hu]; simp
    simp only [Complex.sub_re,hq] at he
    linarith [(abs_le.mp he).2]

theorem actual_first_re_zero_iff {p : ℕ} (hp : 17 ≤ p) {c s u : ℝ}
    (hc : ActualTip p c) (F : Family p c) (hs : s ∈ Radius)
    (hu : u ∈ Icc (-1 : ℝ) 1) :
    (normalizedReturn c p (circlePoint s u)).re = 0 ↔ u = realAngle F s := by
  constructor
  · intro hz
    have ha := realAngle_mem F s
    exact actual_full_crossing_unique hp hc hs hu
      ⟨by linarith [ha.1],by linarith [ha.2]⟩ hz (realAngle_crossing F hs)
  · rintro rfl
    exact realAngle_crossing F hs

theorem circlePoint_injective {s : ℝ} (hs : 0 < s) :
    Injective (circlePoint s) := by
  intro u v huv
  have h := congrArg Complex.re huv
  simp only [circlePoint,Complex.add_re,Complex.ofReal_re,Complex.mul_re,
    Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,
    add_zero] at h
  nlinarith

theorem first_arc_endpoint_sum_neg {p : ℕ} (hp : 17 ≤ p) {c s : ℝ}
    (hc : ActualTip p c) (hs : s ∈ Radius) :
    (normalizedReturn c p (circlePoint s 1)).re +
      (normalizedReturn c p (circlePoint s (-1))).re < 0 := by
  have hu : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := by constructor <;> norm_num
  have hv : (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 := by constructor <;> norm_num
  have hq := (Complex.abs_re_le_norm
    (normalizedReturn c p (circlePoint s 1)-complexMap (kappa p c) (circlePoint s 1))).trans
      (actual_return_error_small hp hc ((circlePoint_full_disk hs hu).trans (by norm_num)))
  have hw := (Complex.abs_re_le_norm
    (normalizedReturn c p (circlePoint s (-1))-complexMap (kappa p c) (circlePoint s (-1)))).trans
      (actual_return_error_small hp hc ((circlePoint_full_disk hs hv).trans (by norm_num)))
  have hqr : (complexMap (kappa p c) (circlePoint s 1)).re = crossing (kappa p c) s 1 := by
    rw [circle_image _ _ hu]; simp
  have hwr : (complexMap (kappa p c) (circlePoint s (-1))).re = crossing (kappa p c) s (-1) := by
    rw [circle_image _ _ hv]; simp
  simp only [Complex.sub_re,hqr,hwr] at hq hw
  have hk := hc.2.2.2.1.1
  have hks : 0 ≤ kappa p c*s^2 := mul_nonneg (by linarith) (sq_nonneg s)
  dsimp only [crossing] at hq hw
  nlinarith [(abs_le.mp hq).2,(abs_le.mp hw).2]

theorem first_arc_im_zero_iff {p : ℕ} (hp : 17 ≤ p) {c s u : ℝ}
    (hc : ActualTip p c) (hs : s ∈ Radius) (hu : u ∈ Icc (-1 : ℝ) 1) :
    (normalizedReturn c p (circlePoint s u)).im = 0 ↔ u = -1 ∨ u = 1 := by
  constructor
  · intro h
    by_contra hn
    have hne := not_or.mp hn
    have hu' : u ∈ Ioo (-1 : ℝ) 1 :=
      ⟨lt_of_le_of_ne hu.1 (Ne.symm hne.1),lt_of_le_of_ne hu.2 hne.2⟩
    exact (ne_of_gt (actual_first_arc_im_pos hp hc hs hu')) h
  · rintro (rfl | rfl)
    · have he : circlePoint s (-1) = (wEndpoint s : ℂ) := by simp [circlePoint,wEndpoint]; ring
      rw [he,normalizedReturn_real]
    · have he : circlePoint s 1 = (qEndpoint s : ℂ) := by simp [circlePoint,qEndpoint]; ring
      rw [he,normalizedReturn_real]

theorem first_arc_no_opposites {p : ℕ} (hp : 17 ≤ p) {c s u v : ℝ}
    (hc : ActualTip p c) (F : Family p c) (hs : s ∈ Radius)
    (hu : u ∈ Icc (-1 : ℝ) 1) (hv : v ∈ Icc (-1 : ℝ) 1) :
    normalizedReturn c p (circlePoint s u) ≠ -normalizedReturn c p (circlePoint s v) := by
  have hi (w : ℝ) (hw : w ∈ Icc (-1 : ℝ) 1) :
      0 ≤ (normalizedReturn c p (circlePoint s w)).im := by
    by_cases h : w = -1 ∨ w = 1
    · rw [(first_arc_im_zero_iff hp hc hs hw).mpr h]
    · have hn := not_or.mp h
      exact (actual_first_arc_im_pos hp hc hs
        ⟨lt_of_le_of_ne hw.1 (Ne.symm hn.1),lt_of_le_of_ne hw.2 hn.2⟩).le
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.neg_im] at him
  have hu0 : (normalizedReturn c p (circlePoint s u)).im = 0 := by
    linarith [hi u hu,hi v hv]
  have hv0 : (normalizedReturn c p (circlePoint s v)).im = 0 := by
    linarith [hi u hu,hi v hv]
  have hre := congrArg Complex.re h
  simp only [Complex.neg_re] at hre
  have hq := actual_q_side_re_pos hp hc F hs
    (show (1 : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num)
    (show realAngle F s < 1 by linarith [(realAngle_mem F s).2])
  have hw := actual_w_side_re_neg hp hc F hs
    (show (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num)
    (show -1 < realAngle F s by linarith [(realAngle_mem F s).1])
  have hsum := first_arc_endpoint_sum_neg hp hc hs
  rcases (first_arc_im_zero_iff hp hc hs hu).mp hu0 with rfl | rfl <;>
    rcases (first_arc_im_zero_iff hp hc hs hv).mp hv0 with rfl | rfl <;> linarith

/-- Strict bounds make membership in the open proper source available
at every stage, including the last source before the fourth image. -/
def StrictSupport (c : ℝ) (p : ℕ) : Prop :=
  ∀ z ∈ initialDisk,
    (∀ m ≤ 4, ‖((normalizedReturn c p)^[m]) z‖ < 23/20) ∧
      0 < (((normalizedReturn c p)^[2]) z).re ∧
      (((normalizedReturn c p)^[3]) z).re < 0

private instance : CompactSpace initialDisk := by
  apply isCompact_iff_compactSpace.mp
  have he : initialDisk = Metric.closedBall (-(3/4 : ℂ)) (133/2000 : ℝ) := by
    ext z
    simp only [initialDisk, mem_setOf_eq, Metric.mem_closedBall, dist_eq_norm,
      sub_neg_eq_add]
  rw [he]
  exact isCompact_closedBall _ _

private instance : Nonempty initialDisk :=
  ⟨⟨-(3/4 : ℂ), by simp [initialDisk]; norm_num⟩⟩

private theorem eventually_norm_lt {α : Type*} [TopologicalSpace α]
    [CompactSpace α] [Nonempty α] {F : ℕ → α → ℂ} {f : α → ℂ} {R : ℝ}
    (hf : Continuous f) (hR : ∀ x, ‖f x‖ < R)
    (hconv : TendstoUniformly F f atTop) :
    ∀ᶠ n in atTop, ∀ x, ‖F n x‖ < R := by
  obtain ⟨x,_,hx⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hf.norm.continuousOn
  have hε : 0 < R-‖f x‖ := sub_pos.mpr (hR x)
  filter_upwards [(Metric.tendstoUniformly_iff.mp hconv) (R-‖f x‖) hε] with n hn
  intro y
  have hd := hn y
  rw [dist_eq_norm,norm_sub_rev] at hd
  have hmax : ‖f y‖ ≤ ‖f x‖ := hx (mem_univ y)
  have hb := norm_le_norm_sub_add (F n y) (f y)
  linarith

theorem actual_strict_support (c : ℕ → ℝ)
    (hc : ∀ n, ActualTip (n+17) (c n)) :
    ∀ᶠ n in atTop, StrictSupport (c n) (n+17) := by
  obtain ⟨k₀,⟨hk₀,hroot⟩,_⟩ := exists_unique_limiting_parameter
  have hi := ActualCrestSupport.actual_support_iterates_tendsto hk₀ hroot c hc
  have hQ : Continuous (complexMap k₀) := by unfold complexMap; fun_prop
  have hm : ∀ m ∈ Finset.range 5, ∀ᶠ n in atTop, ∀ z : initialDisk,
      ‖((normalizedReturn (c n) (n+17))^[m]) z‖ < 23/20 := by
    intro m hm
    have hm4 : m ≤ 4 := by have := Finset.mem_range.mp hm; omega
    exact eventually_norm_lt ((hQ.iterate m).comp continuous_subtype_val)
      (fun z => (whole_support_bounds hk₀ z.property).1 m hm4) (hi m hm4).1
  filter_upwards [(eventually_all_finset (Finset.range 5)).mpr hm,
    ActualCrestSupport.actual_support_bounds c hc] with n hn hs
  intro z hz
  exact ⟨fun m hm => hn m (Finset.mem_range.mpr (by omega)) ⟨z,hz⟩,
    (hs z hz).2⟩

/-- The same threshold works for every admissible actual parameter. -/
theorem eventually_all_strict_support :
    ∀ᶠ n : ℕ in atTop, ∀ c : ℝ, ActualTip (n+17) c → StrictSupport c (n+17) := by
  classical
  have hselect : ∀ n : ℕ, ∃ c : ℝ, ActualTip (n+17) c ∧
      ((∃ d : ℝ, ActualTip (n+17) d ∧ ¬ StrictSupport d (n+17)) →
        ¬ StrictSupport c (n+17)) := by
    intro n
    by_cases h : ∃ d : ℝ, ActualTip (n+17) d ∧ ¬ StrictSupport d (n+17)
    · obtain ⟨c,hc,hbad⟩ := h
      exact ⟨c,hc,fun _ => hbad⟩
    · obtain ⟨c,hc⟩ := exists_actual_tip (n+17) (by omega)
      exact ⟨c,hc,fun hh => (h hh).elim⟩
  choose c hc hbad using hselect
  filter_upwards [actual_strict_support c hc] with n hn
  intro d hd
  by_contra h
  exact hbad n ⟨d,hd,h⟩ hn

theorem support_in_parent {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (hS : StrictSupport c p) {z : ℂ} (hz : z ∈ initialDisk)
    {m : ℕ} (hm : m ≤ 3) :
    ((normalizedReturn c p)^[m]) z ∈ parentSource c p := by
  apply actual_parent_exhaustion hp hc ((hS z hz).1 m (by omega)).le
  simpa only [iterate_succ_apply'] using (hS z hz).1 (m+1) (by omega)

/-- Each complete closed upper semicircle remains simple through all
four images.  The only possible signed-fiber collision after the first
map would join its two real endpoints; their unequal magnitudes exclude it. -/
theorem full_arc_iterate_injective {p : ℕ} (hp : 17 ≤ p) {c s : ℝ}
    (hc : ActualTip p c) (hS : StrictSupport c p) (F : Family p c)
    (hs : s ∈ Icc (1/16 : ℝ) (133/2000)) {m : ℕ} (hm : m ≤ 4) :
    InjOn (fun u : ℝ => ((normalizedReturn c p)^[m]) (circlePoint s u))
      (Icc (-1 : ℝ) 1) := by
  have hsR : s ∈ Radius := ⟨hs.1,by linarith [hs.2]⟩
  have hb (u : ℝ) (hu : u ∈ Icc (-1 : ℝ) 1) :=
    hS (circlePoint s u) (circlePoint_initialDisk hs hu)
  have h0 : Injective (circlePoint s) := circlePoint_injective (by linarith [hs.1])
  have h1 : InjOn (fun u : ℝ => normalizedReturn c p (circlePoint s u))
      (Icc (-1 : ℝ) 1) := by
    intro u hu v hv he
    rcases (actual_return_collision_iff hp hc
      ((hb u hu).1 0 (by norm_num) |>.le.trans (by norm_num))
      ((hb v hv).1 0 (by norm_num) |>.le.trans (by norm_num))).mp he with he | he
    · exact h0 he
    · have hr := congrArg Complex.re he
      simp only [iterate_zero,id_eq,Complex.neg_re] at hr
      linarith [circlePoint_re_neg hsR hu,circlePoint_re_neg hsR hv]
  have h2 : InjOn (fun u : ℝ => ((normalizedReturn c p)^[2]) (circlePoint s u))
      (Icc (-1 : ℝ) 1) := by
    intro u hu v hv he
    rcases (actual_return_collision_iff hp hc
      ((hb u hu).1 1 (by norm_num) |>.le.trans (by norm_num))
      ((hb v hv).1 1 (by norm_num) |>.le.trans (by norm_num))).mp he with he | he
    · exact h1 hu hv he
    · exact (first_arc_no_opposites hp hc F hsR hu hv he).elim
  have h3 : InjOn (fun u : ℝ => ((normalizedReturn c p)^[3]) (circlePoint s u))
      (Icc (-1 : ℝ) 1) := by
    intro u hu v hv he
    rcases (actual_return_collision_iff hp hc
      ((hb u hu).1 2 (by norm_num) |>.le.trans (by norm_num))
      ((hb v hv).1 2 (by norm_num) |>.le.trans (by norm_num))).mp he with he | he
    · exact h2 hu hv he
    · have hr := congrArg Complex.re he
      simp only [Complex.neg_re] at hr
      linarith [(hb u hu).2.1,(hb v hv).2.1]
  have h4 : InjOn (fun u : ℝ => ((normalizedReturn c p)^[4]) (circlePoint s u))
      (Icc (-1 : ℝ) 1) := by
    intro u hu v hv he
    rcases (actual_return_collision_iff hp hc
      ((hb u hu).1 3 (by norm_num) |>.le.trans (by norm_num))
      ((hb v hv).1 3 (by norm_num) |>.le.trans (by norm_num))).mp he with he | he
    · exact h3 hu hv he
    · have hr := congrArg Complex.re he
      simp only [Complex.neg_re] at hr
      linarith [(hb u hu).2.2,(hb v hv).2.2]
  interval_cases m
  · exact h0.injOn
  · exact h1
  · exact h2
  · exact h3
  · exact h4

/-- After the first return, all later real contacts occur at the one
actual crossing. There are no additional contacts hidden along the arc. -/
theorem full_arc_real_contacts {p : ℕ} (hp : 17 ≤ p) {c s u : ℝ}
    (hc : ActualTip p c) (hS : StrictSupport c p) (F : Family p c)
    (hs : s ∈ Icc (1/16 : ℝ) (133/2000)) (hu : u ∈ Ioo (-1 : ℝ) 1) :
    ((((normalizedReturn c p)^[2]) (circlePoint s u)).im = 0 ↔ u = realAngle F s) ∧
    ((((normalizedReturn c p)^[3]) (circlePoint s u)).im = 0 ↔ u = realAngle F s) ∧
    ((((normalizedReturn c p)^[4]) (circlePoint s u)).im = 0 ↔ u = realAngle F s) := by
  have hsR : s ∈ Radius := ⟨hs.1,by linarith [hs.2]⟩
  have hz := circlePoint_initialDisk hs ⟨hu.1.le,hu.2.le⟩
  have hb := hS (circlePoint s u) hz
  have hi := actual_first_arc_im_pos hp hc hsR hu
  have h2 : (((normalizedReturn c p)^[2]) (circlePoint s u)).im = 0 ↔
      (normalizedReturn c p (circlePoint s u)).re = 0 := by
    change (normalizedReturn c p (normalizedReturn c p (circlePoint s u))).im = 0 ↔ _
    have he : (normalizedReturn c p (normalizedReturn c p (circlePoint s u))).im = 0 ↔
        (normalizedReturn c p (circlePoint s u)).re = 0 ∨
        (normalizedReturn c p (circlePoint s u)).im = 0 := by
      simpa using actual_im_sign hp hc ((hb.1 1 (by norm_num)).le)
    rw [he]
    simp only [ne_of_gt hi,or_false]
  have h3 : (((normalizedReturn c p)^[3]) (circlePoint s u)).im = 0 ↔
      (((normalizedReturn c p)^[2]) (circlePoint s u)).im = 0 := by
    change (normalizedReturn c p (((normalizedReturn c p)^[2]) (circlePoint s u))).im = 0 ↔ _
    rw [actual_im_sign hp hc ((hb.1 2 (by norm_num)).le)]
    simp only [ne_of_gt hb.2.1,false_or]
  have h4 : (((normalizedReturn c p)^[4]) (circlePoint s u)).im = 0 ↔
      (((normalizedReturn c p)^[3]) (circlePoint s u)).im = 0 := by
    change (normalizedReturn c p (((normalizedReturn c p)^[3]) (circlePoint s u))).im = 0 ↔ _
    rw [actual_im_sign hp hc ((hb.1 3 (by norm_num)).le)]
    simp only [ne_of_lt hb.2.2,false_or]
  have he := h2.trans (actual_first_re_zero_iff hp hc F hsR ⟨hu.1.le,hu.2.le⟩)
  exact ⟨he,h3.trans he,h4.trans (h3.trans he)⟩

theorem crossing_second_re_gt_one {p : ℕ} (hp : 17 ≤ p) {c s : ℝ}
    (hc : ActualTip p c) (hS : StrictSupport c p) (F : Family p c)
    (hs : s ∈ Icc (1/16 : ℝ) (133/2000)) :
    1 < (((normalizedReturn c p)^[2]) (point F s)).re := by
  have hsR : s ∈ Radius := ⟨hs.1,by linarith [hs.2]⟩
  have ha := realAngle_mem F s
  have he : point F s = circlePoint s (realAngle F s) := by
    simp only [point,Family.point,realAngle,radiusProjection_eq hsR]
  have hz : point F s ∈ initialDisk := by
    rw [he]
    exact circlePoint_initialDisk hs ⟨by linarith [ha.1],by linarith [ha.2]⟩
  let z := normalizedReturn c p (point F s)
  have hzr : z.re = 0 := by
    dsimp only [z]
    rw [he]
    exact realAngle_crossing F hsR
  have hzi : 0 < z.im := by
    dsimp only [z]
    simpa only [point,radiusProjection_eq hsR,Family.point] using F.positive ⟨s,hsR⟩
  have hzn : ‖z‖ ≤ 3/2 := ((hS (point F s) hz).1 1 (by norm_num)).le.trans (by norm_num)
  have hneg := actual_secant_re_neg hp hc hzn (show ‖(0 : ℂ)‖ ≤ 3/2 by norm_num)
  have h := congrArg Complex.re (normalized_difference c p (by omega) hc.2.1.ne' z 0)
  rw [normalized_return_zero c p hc.2.1.ne'] at h
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0),sub_zero,pow_two,
    Complex.sub_re,Complex.one_re,Complex.mul_re,Complex.mul_im,hzr,
    zero_mul,mul_zero,zero_sub] at h
  have hpos : 0 < z.im*z.im := mul_pos hzi hzi
  have hprod : 0 < -(z.im*z.im)*(normalizedSecant c p z 0).re :=
    mul_pos_of_neg_of_neg (neg_neg_of_pos hpos) (by linarith)
  change 1 < (normalizedReturn c p z).re
  linarith

/-- The literal source and target slits differ. In normalized coordinates
they are [-1,1] and [H²(0),1], respectively. -/
def sourceSlit : Set ℂ := {z | z.im = 0 ∧ z.re ∈ Icc (-1 : ℝ) 1}

def targetSlit (c : ℝ) (p : ℕ) : Set ℂ :=
  {z | z.im = 0 ∧ z.re ∈ Icc (((normalizedReturn c p)^[2]) 0).re 1}

def slitSource (c : ℝ) (p : ℕ) : Set ℂ := parentSource c p \ sourceSlit

def slitTarget (c : ℝ) (p : ℕ) : Set ℂ :=
  Metric.ball 0 (23/20) \ targetSlit c p

theorem actual_second_critical_bounds {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    (((normalizedReturn c p)^[2]) 0).re ∈ Ioo (-1 : ℝ) 0 := by
  have he : ((normalizedReturn c p)^[2]) 0 = normalizedReturn c p 1 := by
    change normalizedReturn c p (normalizedReturn c p 0) = _
    rw [normalized_return_zero c p hc.2.1.ne']
  have hr := (Complex.abs_re_le_norm
    (normalizedReturn c p 1-complexMap (kappa p c) 1)).trans
      (actual_return_error_small hp hc (show ‖(1 : ℂ)‖ ≤ 3/2 by norm_num))
  norm_num [complexMap] at hr
  rw [he]
  have hk := hc.2.2.2.1
  constructor <;> linarith [hk.1,hk.2,(abs_le.mp hr).1,(abs_le.mp hr).2]

/-- The real source interval maps into exactly the real target range.
This verifies the real endpoints of every complete ancestor curve. -/
theorem sourceSlit_mapsTo_target {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) :
    MapsTo (normalizedReturn c p) sourceSlit (targetSlit c p) := by
  intro z hz
  have hx : z.re ∈ Icc (-1 : ℝ) 1 := hz.2
  have hreal : z = (z.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa only [Complex.ofReal_im] using hz.1
  have hxabs : |z.re| ≤ 1 := abs_le.mpr hx
  have hxd : |z.re| ∈ Icc (0 : ℝ) (3/2) :=
    ⟨abs_nonneg _,hxabs.trans (by norm_num)⟩
  have heven : normalizedReturn c p ((|z.re| : ℝ) : ℂ) =
      normalizedReturn c p (z.re : ℂ) := by
    by_cases h : 0 ≤ z.re
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg (lt_of_not_ge h),Complex.ofReal_neg]
      exact ThreeReturnDomain.normalized_return_even c p (by omega) _
  have hanti := (actual_return_real_strictAnti hp hc).antitoneOn
  have hlo := hanti hxd (show (1 : ℝ) ∈ Icc (0 : ℝ) (3/2) by
    constructor <;> norm_num) hxabs
  have hup := hanti (show (0 : ℝ) ∈ Icc (0 : ℝ) (3/2) by
    constructor <;> norm_num) hxd (abs_nonneg z.re)
  have hsecond : normalizedReturn c p 1 = ((normalizedReturn c p)^[2]) 0 := by
    change normalizedReturn c p 1 = normalizedReturn c p (normalizedReturn c p 0)
    rw [normalized_return_zero c p hc.2.1.ne']
  simp only [Complex.ofReal_zero,Complex.ofReal_one] at hlo hup
  rw [heven,hsecond] at hlo
  rw [heven,normalized_return_zero c p hc.2.1.ne',Complex.one_re] at hup
  change (normalizedReturn c p z).im = 0 ∧
    (((normalizedReturn c p)^[2]) 0).re ≤ (normalizedReturn c p z).re ∧
    (normalizedReturn c p z).re ≤ 1
  rw [hreal]
  exact ⟨normalizedReturn_real c z.re p,hlo,hup⟩

theorem targetSlit_subset_sourceSlit {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : targetSlit c p ⊆ sourceSlit := by
  intro z hz
  exact ⟨hz.1,((actual_second_critical_bounds hp hc).1.le.trans hz.2.1),hz.2.2⟩

theorem sourceSlit_iterate_mem {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : z ∈ sourceSlit) (m : ℕ) :
    ((normalizedReturn c p)^[m]) z ∈ sourceSlit := by
  induction m with
  | zero => exact hz
  | succ m ih =>
    rw [iterate_succ_apply']
    exact targetSlit_subset_sourceSlit hp hc (sourceSlit_mapsTo_target hp hc ih)

theorem sourceSlit_positive_iterate_target {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : z ∈ sourceSlit) {m : ℕ} (hm : 1 ≤ m) :
    ((normalizedReturn c p)^[m]) z ∈ targetSlit c p := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  rw [iterate_succ_apply']
  exact sourceSlit_mapsTo_target hp hc (sourceSlit_iterate_mem hp hc hz n)

/-- Both endpoints of the full circle are on the literal source slit,
and every positive iterate endpoint is on the literal target slit. -/
theorem full_arc_endpoint_slits {p : ℕ} (hp : 17 ≤ p) {c s : ℝ}
    (hc : ActualTip p c) (hs : s ∈ Icc (1/16 : ℝ) (133/2000))
    {u : ℝ} (hu : u = -1 ∨ u = 1) :
    (∀ m : ℕ, ((normalizedReturn c p)^[m]) (circlePoint s u) ∈ sourceSlit) ∧
    (∀ m : ℕ, 1 ≤ m → ((normalizedReturn c p)^[m]) (circlePoint s u) ∈
      targetSlit c p) := by
  have hz : circlePoint s u ∈ sourceSlit := by
    rcases hu with rfl | rfl <;>
      simp only [sourceSlit,mem_setOf_eq,circlePoint,Complex.add_im,Complex.add_re,
        Complex.ofReal_im,Complex.ofReal_re,Complex.mul_re,Complex.mul_im,
        Complex.I_re,Complex.I_im,neg_sq,one_pow,sub_self,Real.sqrt_zero,
        mul_zero,add_zero,mul_neg_one,mul_one]
    all_goals constructor
    all_goals constructor <;> linarith [hs.1,hs.2]
  exact ⟨sourceSlit_iterate_mem hp hc hz,
    fun _ hm => sourceSlit_positive_iterate_target hp hc hz hm⟩

theorem crossing_third_below_target {p : ℕ} (hp : 17 ≤ p) {c s : ℝ}
    (hc : ActualTip p c) (F : Family p c)
    (hs : s ∈ Icc (1/16 : ℝ) (133/2000)) (hg : terminalGate F s) :
    (((normalizedReturn c p)^[3]) (point F s)).re <
      (((normalizedReturn c p)^[2]) 0).re := by
  have hq := (actual_endpoint_gates hp hc hs
    (show (1037/2000 : ℝ) ∈ Ioo (518/1000 : ℝ) (519/1000) by
      constructor <;> norm_num)).2.2.2.2.1
  have h2 := congrArg Complex.re (actualOrbit_cast c 0 p 2)
  have h4 := congrArg Complex.re (actualOrbit_cast c 0 p 4)
  simp only [Complex.ofReal_re,Complex.ofReal_zero] at h2 h4
  change -actualOrbit c p 0 2 < actualOrbit c p (qEndpoint s) 2 ∧
    actualOrbit c p (qEndpoint s) 2 < actualOrbit c p 0 4 at hq
  change -1 < (((normalizedReturn c p)^[3]) (point F s)).re ∧
    (((normalizedReturn c p)^[3]) (point F s)).re <
      -(((normalizedReturn c p)^[4]) 0).re at hg
  linarith [hq.1,hq.2,hg.2]

/-- The first three full upper arcs avoid the target slit. The second
real contact is beyond its right end, and the third is to its left. -/
theorem full_arc_target_membership {p : ℕ} (hp : 17 ≤ p) {c s u : ℝ}
    (hc : ActualTip p c) (hS : StrictSupport c p) (F : Family p c)
    (hs : s ∈ Icc (1/16 : ℝ) (133/2000)) (hg : terminalGate F s)
    (hu : u ∈ Ioo (-1 : ℝ) 1) :
    ∀ m ∈ Icc (1 : ℕ) 3, ((normalizedReturn c p)^[m]) (circlePoint s u) ∈
      slitTarget c p := by
  have hsR : s ∈ Radius := ⟨hs.1,by linarith [hs.2]⟩
  have hz := circlePoint_initialDisk hs ⟨hu.1.le,hu.2.le⟩
  have hb := hS (circlePoint s u) hz
  have he : circlePoint s (realAngle F s) = point F s := by
    simp only [point,Family.point,realAngle,radiusProjection_eq hsR]
  have hcontact := full_arc_real_contacts hp hc hS F hs hu
  intro m hm
  rcases hm with ⟨hm1,hm3⟩
  refine ⟨?_,?_⟩
  · simpa only [Metric.mem_ball,dist_zero_right] using hb.1 m (by omega)
  · intro hslit
    have him := hslit.1
    have hre := hslit.2
    interval_cases m
    · exact (ne_of_gt (actual_first_arc_im_pos hp hc hsR hu)) him
    · have hua := hcontact.1.mp him
      rw [hua,he] at hre
      exact not_lt_of_ge hre.2 (crossing_second_re_gt_one hp hc hS F hs)
    · have hua := hcontact.2.1.mp him
      rw [hua,he] at hre
      exact not_lt_of_ge hre.1 (crossing_third_below_target hp hc F hs hg)

/-- Restricting for returns one through three keeps the whole upper
arc. The fourth source removes exactly its unique real crossing. -/
theorem full_arc_source_membership {p : ℕ} (hp : 17 ≤ p) {c s u : ℝ}
    (hc : ActualTip p c) (hS : StrictSupport c p) (F : Family p c)
    (hs : s ∈ Icc (1/16 : ℝ) (133/2000)) (hg : terminalGate F s)
    (hu : u ∈ Ioo (-1 : ℝ) 1) :
    (∀ m ≤ 2, ((normalizedReturn c p)^[m]) (circlePoint s u) ∈ slitSource c p) ∧
    (((normalizedReturn c p)^[3]) (circlePoint s u) ∈ slitSource c p ↔
      u ≠ realAngle F s) := by
  have hsR : s ∈ Radius := ⟨hs.1,by linarith [hs.2]⟩
  have hz := circlePoint_initialDisk hs ⟨hu.1.le,hu.2.le⟩
  have he : circlePoint s (realAngle F s) = point F s := by
    simp only [point,Family.point,realAngle,radiusProjection_eq hsR]
  have hcontact := full_arc_real_contacts hp hc hS F hs hu
  constructor
  · intro m hm
    refine ⟨support_in_parent hp hc hS hz (by omega),?_⟩
    intro hslit
    have him := hslit.1
    have hre := hslit.2
    interval_cases m
    · exact (ne_of_gt (circlePoint_im_pos hsR hu)) him
    · exact (ne_of_gt (actual_first_arc_im_pos hp hc hsR hu)) him
    · have hua := hcontact.1.mp him
      rw [hua,he] at hre
      exact not_lt_of_ge hre.2 (crossing_second_re_gt_one hp hc hS F hs)
  · constructor
    · intro hmem hua
      apply hmem.2
      refine ⟨hcontact.2.1.mpr hua,?_⟩
      rw [hua,he]
      have ha := actual_fourth_critical_bounds hp hc
      change -1 ≤ terminal F s ∧ terminal F s ≤ 1
      exact ⟨hg.1.le,by linarith [hg.2,ha.1]⟩
    · intro hua
      refine ⟨support_in_parent hp hc hS hz (by norm_num),?_⟩
      intro hslit
      exact hua (hcontact.2.1.mp hslit.1)

/-- Exact signs on the component attached to q. Every displayed strict
inequality is on a complete open arc, not a sample of its points. -/
theorem q_side_fourfold_signs {p : ℕ} (hp : 17 ≤ p) {c s u : ℝ}
    (hc : ActualTip p c) (hS : StrictSupport c p) (F : Family p c)
    (hs : s ∈ Icc (1/16 : ℝ) (133/2000))
    (hu : u ∈ Ioo (realAngle F s) 1) :
    0 < (normalizedReturn c p (circlePoint s u)).re ∧
    0 < (normalizedReturn c p (circlePoint s u)).im ∧
    (((normalizedReturn c p)^[2]) (circlePoint s u)).im < 0 ∧
    0 < (((normalizedReturn c p)^[3]) (circlePoint s u)).im ∧
    0 < (((normalizedReturn c p)^[4]) (circlePoint s u)).im := by
  have hsR : s ∈ Radius := ⟨hs.1,by linarith [hs.2]⟩
  have hu0 : u ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [(realAngle_mem F s).1,hu.1],hu.2⟩
  have hz := circlePoint_initialDisk hs ⟨hu0.1.le,hu0.2.le⟩
  have hb := hS (circlePoint s u) hz
  have h1r := actual_q_side_re_pos hp hc F hsR ⟨hu0.1.le,hu0.2.le⟩ hu.1
  have h1i := actual_first_arc_im_pos hp hc hsR hu0
  have h2i : (((normalizedReturn c p)^[2]) (circlePoint s u)).im < 0 :=
    actual_im_neg_of_pos_pos hp hc ((hb.1 1 (by norm_num)).le) h1r h1i
  have h3i : 0 < (((normalizedReturn c p)^[3]) (circlePoint s u)).im :=
    actual_im_pos_of_pos_neg hp hc ((hb.1 2 (by norm_num)).le) hb.2.1 h2i
  have h4i : 0 < (((normalizedReturn c p)^[4]) (circlePoint s u)).im :=
    actual_im_pos_of_neg_pos hp hc ((hb.1 3 (by norm_num)).le) hb.2.2 h3i
  exact ⟨h1r,h1i,h2i,h3i,h4i⟩

/-- The q component is parametrized continuously from its real endpoint
to the unique upper crossing. Its trace is the ordinary circular arc. -/
def qArc {p : ℕ} {c : ℝ} (F : Family p c) (s t : ℝ) : ℂ :=
  circlePoint s (1+t*(realAngle F s-1))

theorem qArc_continuous {p : ℕ} {c : ℝ} (F : Family p c) (s : ℝ) :
    Continuous (qArc F s) := by
  unfold qArc circlePoint
  fun_prop

theorem qArc_zero {p : ℕ} {c : ℝ} (F : Family p c) (s : ℝ) :
    qArc F s 0 = (qEndpoint s : ℂ) := by
  simp [qArc,circlePoint,qEndpoint]
  ring

theorem qArc_one {p : ℕ} {c s : ℝ} (F : Family p c) (hs : s ∈ Radius) :
    qArc F s 1 = point F s := by
  simp [qArc,point,Family.point,realAngle,radiusProjection_eq hs]

theorem qArc_parameter_mem {p : ℕ} {c s t : ℝ} (F : Family p c)
    (ht : t ∈ Ioo (0 : ℝ) 1) :
    1+t*(realAngle F s-1) ∈ Ioo (realAngle F s) 1 := by
  have ha := (realAngle_mem F s).2
  have hA : 0 < 1-realAngle F s := by linarith
  have hleft := mul_pos (show 0 < 1-t by linarith [ht.2]) hA
  have hright := mul_pos ht.1 hA
  constructor <;> nlinarith

theorem qArc_parameter_mem_closed {p : ℕ} {c s t : ℝ} (F : Family p c)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    1+t*(realAngle F s-1) ∈ Icc (realAngle F s) 1 := by
  have ha := (realAngle_mem F s).2
  have hA : 0 ≤ 1-realAngle F s := by linarith
  have hleft := mul_nonneg (show 0 ≤ 1-t by linarith [ht.2]) hA
  have hright := mul_nonneg ht.1 hA
  constructor <;> nlinarith

theorem closed_q_side_first_sum_pos {p : ℕ} (hp : 17 ≤ p) {c s u : ℝ}
    (hc : ActualTip p c) (F : Family p c) (hs : s ∈ Radius)
    (hu : u ∈ Icc (realAngle F s) 1) :
    0 < (normalizedReturn c p (circlePoint s u)).re +
      (normalizedReturn c p (circlePoint s u)).im := by
  have ham := realAngle_mem F s
  have hu0 : u ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [ham.1,hu.1],hu.2⟩
  have hir : 0 ≤ (normalizedReturn c p (circlePoint s u)).im := by
    rcases eq_or_lt_of_le hu.2 with h | h
    · rw [h]
      have he : circlePoint s 1 = (qEndpoint s : ℂ) := by simp [circlePoint,qEndpoint]; ring
      rw [he,normalizedReturn_real]
    · exact (actual_first_arc_im_pos hp hc hs ⟨by linarith [ham.1,hu.1],h⟩).le
  rcases eq_or_lt_of_le hu.1 with h | h
  · rw [← h,realAngle_crossing F hs]
    simpa only [zero_add] using actual_first_arc_im_pos hp hc hs
      ⟨by linarith [ham.1],by linarith [ham.2]⟩
  · have hr := actual_q_side_re_pos hp hc F hs hu0 h
    linarith

/-- The closed q-side trace lies in a strict linear half-plane after
the first map. This includes both endpoints and supports an open
injectivity neighborhood for the complete fourth image. -/
theorem qArc_closed_support {p : ℕ} (hp : 17 ≤ p) {c s t : ℝ}
    (hc : ActualTip p c) (F : Family p c)
    (hs : s ∈ Icc (1/16 : ℝ) (133/2000)) (ht : t ∈ Icc (0 : ℝ) 1) :
    qArc F s t ∈ initialDisk ∧ (qArc F s t).re < 0 ∧
    0 < (normalizedReturn c p (qArc F s t)).re +
      (normalizedReturn c p (qArc F s t)).im := by
  have hsR : s ∈ Radius := ⟨hs.1,by linarith [hs.2]⟩
  have hu := qArc_parameter_mem_closed (s := s) F ht
  have ha := realAngle_mem F s
  have hu0 : 1+t*(realAngle F s-1) ∈ Icc (-1 : ℝ) 1 :=
    ⟨by linarith [ha.1,hu.1],hu.2⟩
  exact ⟨circlePoint_initialDisk hs hu0,circlePoint_re_neg hsR hu0,
    closed_q_side_first_sum_pos hp hc F hsR hu⟩

theorem qArc_fourth_im_pos {p : ℕ} (hp : 17 ≤ p) {c s t : ℝ}
    (hc : ActualTip p c) (hS : StrictSupport c p) (F : Family p c)
    (hs : s ∈ Icc (1/16 : ℝ) (133/2000)) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < (((normalizedReturn c p)^[4]) (qArc F s t)).im :=
  (q_side_fourfold_signs hp hc hS F hs (qArc_parameter_mem F ht)).2.2.2.2

theorem qArc_fourth_endpoints {p : ℕ} (hp : 17 ≤ p) {c s α : ℝ}
    (hc : ActualTip p c) (F : Family p c)
    (hs : s ∈ Icc (1/16 : ℝ) (133/2000))
    (hα : α ∈ Ioo (518/1000 : ℝ) (519/1000)) (hg : terminalGate F s) :
    (((normalizedReturn c p)^[4]) (qArc F s 0)).im = 0 ∧
    (((normalizedReturn c p)^[4]) (qArc F s 0)).re ∈
      Ioo (actualOrbit c p 0 6) α ∧
    (((normalizedReturn c p)^[4]) (qArc F s 1)).im = 0 ∧
    (((normalizedReturn c p)^[4]) (qArc F s 1)).re ∈
      Ioo (((normalizedReturn c p)^[2]) 0).re
        (((normalizedReturn c p)^[5]) 0).re := by
  have hq := (actual_endpoint_gates hp hc hs hα).2.2.2.2.2.2.2
  have he := actualOrbit_cast c (qEndpoint s) p 4
  have ht := actual_fourth_terminal_gate hp hc F ⟨hs.1,by linarith [hs.2]⟩ hg
  rw [qArc_zero,qArc_one F ⟨hs.1,by linarith [hs.2]⟩]
  rw [← he]
  exact ⟨rfl,hq,ht⟩

/-- The whole-source membership is also an inclusion in the archive's
literal physical return component, at every stage before the fourth map. -/
theorem physical_support_in_archived_parent {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (hS : StrictSupport c p) {z : ℂ} (hz : z ∈ initialDisk)
    {m : ℕ} (hm : m ≤ 3) :
    ((quadraticMap c)^[m*p]) ((criticalValue c p : ℂ)*z) ∈
      archivedParentSource c p := by
  rw [← normalized_iterate_scale c p hc.2.1.ne']
  apply physical_parent_subset_archived c p hc.2.1 (actual_parent_restriction hp hc)
    (actual_parent_scale_bound hp hc)
  exact ⟨((normalizedReturn c p)^[m]) z,support_in_parent hp hc hS hz hm,rfl⟩

theorem physical_qArc_fourth_im_pos {p : ℕ} (hp : 17 ≤ p) {c s t : ℝ}
    (hc : ActualTip p c) (hS : StrictSupport c p) (F : Family p c)
    (hs : s ∈ Icc (1/16 : ℝ) (133/2000)) (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 < (((quadraticMap c)^[4*p]) ((criticalValue c p : ℂ)*qArc F s t)).im := by
  rw [← normalized_iterate_scale c p hc.2.1.ne']
  simpa only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero] using
    mul_pos hc.2.1 (qArc_fourth_im_pos hp hc hS F hs ht)

/-- Uniform genuine four-stage survival for the literal maps.  The
complete semicircle survives the first three source restrictions; the
fourth cuts it exactly at the classified crossing, and its q component
maps to the upper half-plane.  No support or path conclusion is assumed. -/
theorem eventually_actual_fourfold_survival :
    ∀ᶠ n : ℕ in atTop, ∀ c : ℝ, ActualTip (n+17) c →
      ∀ F : Family (n+17) c, ∀ s ∈ Icc (1/16 : ℝ) (133/2000),
        terminalGate F s →
        (∀ u ∈ Ioo (-1 : ℝ) 1,
          (∀ m ≤ 2, ((normalizedReturn c (n+17))^[m]) (circlePoint s u) ∈
            slitSource c (n+17)) ∧
          ((((normalizedReturn c (n+17))^[3]) (circlePoint s u) ∈
            slitSource c (n+17)) ↔ u ≠ realAngle F s) ∧
          (∀ m ∈ Icc (1 : ℕ) 3,
            ((normalizedReturn c (n+17))^[m]) (circlePoint s u) ∈
              slitTarget c (n+17))) ∧
        (∀ t ∈ Ioo (0 : ℝ) 1,
          0 < (((quadraticMap c)^[4*(n+17)])
            ((criticalValue c (n+17) : ℂ)*qArc F s t)).im) := by
  filter_upwards [eventually_all_strict_support] with n hn
  intro c hc F s hs hg
  have hS := hn c hc
  refine ⟨?_,fun t ht => physical_qArc_fourth_im_pos (by omega) hc hS F hs ht⟩
  intro u hu
  have hsrc := full_arc_source_membership (by omega) hc hS F hs hg hu
  exact ⟨hsrc.1,hsrc.2,full_arc_target_membership (by omega) hc hS F hs hg hu⟩

end
end ActualCrestPaths
