import ActualCrestSupport
import ActualCrestCrossingWindow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Complete actual crest arcs: real-intersection census and disjointness

The exact fibers of the literal normalized polynomial return are used on
the entire semicircle, rather than just at its selected crossing.  Together
with the complete-support bounds, they locate every real intersection of
each of the first four images.  On the selected closed subarcs the fourth
image is injective jointly in radius and angular parameter, including both
endpoints.  The assertions hold uniformly for all sufficiently large
periods and all admissible actual signed-tip parameters.
-/

namespace ActualCrestArcCensus

open Set Function Filter ComplexConjugate
open NearTwoTip NearTwoShooting LimitingCrestQuadraticReturn LimitingCrest
open LoopsLimitingCrestParameter QuadraticCrestDividedDifference
open ActualCrestCrossingWindow

noncomputable section

private theorem actual_band {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) : c ∈ Icc (-2 : ℝ) 0 := by
  have hb := parameter_band hp hc.1
  exact ⟨hb.1, by linarith [hb.2]⟩

private theorem actual_small {p : ℕ} {c : ℝ} (hc : ActualTip p c) :
    criticalValue c p ≤ 12/(4 : ℝ)^p := by
  simpa only [scale, one_div_pow, mul_one_div] using hc.2.2.1

private theorem actual_collision {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z w : ℂ} (hz : ‖z‖ ≤ 23/20)
    (hw : ‖w‖ ≤ 23/20) :
    normalizedReturn c p z = normalizedReturn c p w ↔ z = w ∨ z = -w :=
  normalized_return_collision_iff c p (by omega) (actual_band hp hc)
    hc.2.1 (actual_small hc) hc.2.2.2.1 hz hw

private theorem iterate_conj (c : ℝ) (n : ℕ) (z : ℂ) :
    ((quadraticMap c)^[n]) (conj z) = conj (((quadraticMap c)^[n]) z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply', ih]
    simp [quadraticMap]

private theorem normalizedReturn_conj (c : ℝ) (p : ℕ) (z : ℂ) :
    normalizedReturn c p (conj z) = conj (normalizedReturn c p z) := by
  have hm : (criticalValue c p : ℂ)*conj z =
      conj ((criticalValue c p : ℂ)*z) := by simp
  unfold normalizedReturn
  rw [hm, iterate_conj]
  simp

/-- Inside the certified disk, the only preimages of the real axis under
the actual high-degree normalized return lie on the two coordinate axes. -/
theorem normalized_return_real_iff {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) {z : ℂ} (hz : ‖z‖ ≤ 23/20) :
    (normalizedReturn c p z).im = 0 ↔ z.im = 0 ∨ z.re = 0 := by
  constructor
  · intro him
    have he : normalizedReturn c p z = normalizedReturn c p (conj z) := by
      rw [normalizedReturn_conj, Complex.conj_eq_iff_im.mpr him]
    rcases (actual_collision hp hc hz (by simpa using hz)).mp he with he | he
    · left
      have hi := congrArg Complex.im he
      simp only [Complex.conj_im] at hi
      linarith
    · right
      have hr := congrArg Complex.re he
      simp only [Complex.neg_re, Complex.conj_re] at hr
      linarith
  · rintro (him | hre)
    · have he : z = (z.re : ℂ) := by
        apply Complex.ext <;> simp [him]
      rw [he]
      exact normalizedReturn_real c _ p
    · have he : z = (z.im : ℂ)*Complex.I := by
        apply Complex.ext <;> simp [hre]
      rw [he]
      exact normalizedReturn_imaginary c _ p (by omega)

/-- Every point of the complete upper semicircle belongs to the entire
input support on which the four actual iterates are controlled. -/
theorem circlePoint_mem_initialDisk (s : Radius) {u : ℝ}
    (hu : u ∈ Icc (-1 : ℝ) 1) : circlePoint s u ∈ initialDisk := by
  change ‖circlePoint s u+(3/4 : ℂ)‖ ≤ 133/2000
  rw [circle_radius (by linarith [s.property.1]) hu]
  exact s.property.2

private theorem initialDisk_negative_re {z : ℂ} (hz : z ∈ initialDisk) : z.re < 0 := by
  have h := (Complex.re_le_norm (z+(3/4 : ℂ))).trans hz
  norm_num at h
  linarith

private theorem circlePoint_real_iff (s : Radius) {u : ℝ}
    (hu : u ∈ Icc (-1 : ℝ) 1) :
    (circlePoint s u).im = 0 ↔ u = -1 ∨ u = 1 := by
  have hs : 0 < (s : ℝ) := by linarith [s.property.1]
  have hsq : 0 ≤ 1-u^2 := by nlinarith [sq_le_sq' hu.1 hu.2]
  constructor
  · intro h
    have hm : (s : ℝ)*Real.sqrt (1-u^2) = 0 := by
      simpa [circlePoint] using h
    have hr := (mul_eq_zero.mp hm).resolve_left (ne_of_gt hs)
    have he := Real.sq_sqrt hsq
    rw [hr] at he
    have hf : (u-1)*(u+1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hf with hf | hf
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  · rintro (rfl | rfl) <;> norm_num [circlePoint]

private theorem family_angle_full {p : ℕ} {c : ℝ} (F : Family p c) (s : Radius) :
    F.angle s ∈ Icc (-1 : ℝ) 1 := by
  constructor <;> linarith [(F.angle_mem s).1, (F.angle_mem s).2]

/-- The first image of a complete actual upper semicircle meets the real
axis precisely at its two original real endpoints. -/
theorem first_image_real_iff {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (s : Radius) {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    (normalizedReturn c p (circlePoint s u)).im = 0 ↔ u = -1 ∨ u = 1 := by
  rw [normalized_return_real_iff hp hc (circlePoint_full_disk s.property hu)]
  have hn := initialDisk_negative_re (circlePoint_mem_initialDisk s hu)
  constructor
  · rintro (h | h)
    · exact (circlePoint_real_iff s hu).mp h
    · exact (ne_of_lt hn h).elim
  · intro h
    exact Or.inl ((circlePoint_real_iff s hu).mpr h)

/-- The unique selected crossing is the only purely imaginary point of
the first image on the entire upper semicircle. -/
theorem first_image_re_zero_iff {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (F : Family p c) (s : Radius) {u : ℝ}
    (hu : u ∈ Icc (-1 : ℝ) 1) :
    (normalizedReturn c p (circlePoint s u)).re = 0 ↔ u = F.angle s := by
  constructor
  · intro h
    exact actual_full_crossing_unique hp hc s.property hu (family_angle_full F s)
      h (F.crossing s)
  · rintro rfl
    exact F.crossing s

/-- On the entire selected side of the crossing, including its original
real endpoint, the first actual image has strictly positive real part. -/
theorem first_image_re_pos {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (F : Family p c) (s : Radius) {u : ℝ}
    (hu : u ∈ Ioc (F.angle s) 1) :
    0 < (normalizedReturn c p (circlePoint s u)).re := by
  let f : ℝ → ℝ := fun v => (normalizedReturn c p (circlePoint s v)).re
  have hf : Continuous f := by
    have hcircle : Continuous (circlePoint (s : ℝ)) := by unfold circlePoint; fun_prop
    exact Complex.continuous_re.comp ((normalizedReturn_continuous c p).comp hcircle)
  have hne (v : ℝ) (hv : v ∈ Ioc (F.angle s) 1) : f v ≠ 0 := by
    intro h
    have hv1 : v ∈ Icc (-1 : ℝ) 1 :=
      ⟨by linarith [(F.angle_mem s).1, hv.1], hv.2⟩
    have he := (first_image_re_zero_iff hp hc F s hv1).mp h
    exact (ne_of_gt hv.1) he
  have hw : (1/100 : ℝ) ∈ Ioc (F.angle s) 1 :=
    ⟨(F.angle_mem s).2, by norm_num⟩
  have hg := actual_crossing_growth hp hc s.property
    ⟨(F.angle_mem s).1.le, (F.angle_mem s).2.le⟩
    (show (1/100 : ℝ) ∈ Icc (-1/100 : ℝ) (1/100) by constructor <;> norm_num)
    (F.angle_mem s).2.le
  rw [F.crossing s] at hg
  have hwpos : 0 < f (1/100) := by
    dsimp [f]
    linarith [(F.angle_mem s).2]
  exact (isPreconnected_Ioc : IsPreconnected (Ioc (F.angle s) (1 : ℝ))).lt_of_ne
    hf.continuousOn hne ⟨1/100, hw, hwpos⟩ hu

private theorem first_image_re_nonneg {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (F : Family p c) (s : Radius) {u : ℝ}
    (hu : u ∈ Icc (F.angle s) 1) :
    0 ≤ (normalizedReturn c p (circlePoint s u)).re := by
  rcases eq_or_lt_of_le hu.1 with he | he
  · rw [← he, F.crossing s]
  · exact (first_image_re_pos hp hc F s ⟨he, hu.2⟩).le

/-- At each of the second, third, and fourth actual images, a complete
upper semicircle meets the real axis exactly at its two endpoints and
at the unique selected crest crossing. -/
theorem full_semicircle_real_census {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (F : Family p c)
    (hB : ∀ z ∈ initialDisk,
      (∀ m ≤ 4, ‖((normalizedReturn c p)^[m]) z‖ ≤ 23/20) ∧
        0 < (((normalizedReturn c p)^[2]) z).re ∧
        (((normalizedReturn c p)^[3]) z).re < 0)
    (s : Radius) {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
    ∀ m : ℕ, 2 ≤ m → m ≤ 4 →
      (((normalizedReturn c p)^[m]) (circlePoint s u)).im = 0 ↔
        u = -1 ∨ u = F.angle s ∨ u = 1 := by
  let H := normalizedReturn c p
  let z := circlePoint s u
  have hb := hB z (circlePoint_mem_initialDisk s hu)
  have h1 : (H z).im = 0 ↔ u = -1 ∨ u = 1 := first_image_real_iff hp hc s hu
  have hcross : (H z).re = 0 ↔ u = F.angle s :=
    first_image_re_zero_iff hp hc F s hu
  have h2 : ((H^[2]) z).im = 0 ↔ u = -1 ∨ u = F.angle s ∨ u = 1 := by
    change (H (H z)).im = 0 ↔ _
    rw [normalized_return_real_iff hp hc (by simpa only [iterate_one] using hb.1 1 (by omega)),
      h1, hcross]
    tauto
  have h3 : ((H^[3]) z).im = 0 ↔ u = -1 ∨ u = F.angle s ∨ u = 1 := by
    change (H ((H^[2]) z)).im = 0 ↔ _
    rw [normalized_return_real_iff hp hc (hb.1 2 (by omega)), h2]
    have hn : ((H^[2]) z).re ≠ 0 := ne_of_gt hb.2.1
    simp only [hn, or_false]
  have h4 : ((H^[4]) z).im = 0 ↔ u = -1 ∨ u = F.angle s ∨ u = 1 := by
    change (H ((H^[3]) z)).im = 0 ↔ _
    rw [normalized_return_real_iff hp hc (hb.1 3 (by omega)), h3]
    have hn : ((H^[3]) z).re ≠ 0 := ne_of_lt hb.2.2
    simp only [hn, or_false]
  intro m hm hm'
  interval_cases m <;> assumption

/-- The actual fourth images of the selected closed arcs have no
collisions, either along an individual arc or between different radii.
Both the crest endpoints and the original real endpoints are included. -/
theorem selected_closed_arc_collision_iff {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (F : Family p c)
    (hB : ∀ z ∈ initialDisk,
      (∀ m ≤ 4, ‖((normalizedReturn c p)^[m]) z‖ ≤ 23/20) ∧
        0 < (((normalizedReturn c p)^[2]) z).re ∧
        (((normalizedReturn c p)^[3]) z).re < 0)
    (s t : Radius) {u v : ℝ}
    (hu : u ∈ Icc (F.angle s) 1) (hv : v ∈ Icc (F.angle t) 1) :
    ((normalizedReturn c p)^[4]) (circlePoint s u) =
      ((normalizedReturn c p)^[4]) (circlePoint t v) ↔ s = t ∧ u = v := by
  let H := normalizedReturn c p
  let z := circlePoint s u
  let w := circlePoint t v
  have hu1 : u ∈ Icc (-1 : ℝ) 1 :=
    ⟨by linarith [(F.angle_mem s).1, hu.1], hu.2⟩
  have hv1 : v ∈ Icc (-1 : ℝ) 1 :=
    ⟨by linarith [(F.angle_mem t).1, hv.1], hv.2⟩
  have hzD := circlePoint_mem_initialDisk s hu1
  have hwD := circlePoint_mem_initialDisk t hv1
  have hzB := hB z hzD
  have hwB := hB w hwD
  constructor
  · intro he
    have h3 : (H^[3]) z = (H^[3]) w := by
      rcases (actual_collision hp hc (hzB.1 3 (by omega))
        (hwB.1 3 (by omega))).mp he with h | h
      · exact h
      · have hr := congrArg Complex.re h
        simp only [Complex.neg_re] at hr
        exact (by linarith [hzB.2.2, hwB.2.2] : False).elim
    have h2 : (H^[2]) z = (H^[2]) w := by
      rcases (actual_collision hp hc (hzB.1 2 (by omega))
        (hwB.1 2 (by omega))).mp h3 with h | h
      · exact h
      · have hr := congrArg Complex.re h
        simp only [Complex.neg_re] at hr
        exact (by linarith [hzB.2.1, hwB.2.1] : False).elim
    have h1 : H z = H w := by
      rcases (actual_collision hp hc
        (by simpa only [iterate_one] using hzB.1 1 (by omega))
        (by simpa only [iterate_one] using hwB.1 1 (by omega))).mp h2 with h | h
      · exact h
      · have hr := congrArg Complex.re h
        have hi := congrArg Complex.im h
        simp only [Complex.neg_re] at hr
        simp only [Complex.neg_im] at hi
        have hzpos := first_image_re_nonneg hp hc F s hu
        have hwpos := first_image_re_nonneg hp hc F t hv
        have hz0 : (H z).re = 0 := by linarith
        have hw0 : (H w).re = 0 := by linarith
        have hue := (first_image_re_zero_iff hp hc F s hu1).mp hz0
        have hve := (first_image_re_zero_iff hp hc F t hv1).mp hw0
        have hzIm : 0 < (H z).im := by simpa only [H, z, hue] using F.positive s
        have hwIm : 0 < (H w).im := by simpa only [H, w, hve] using F.positive t
        exact (by linarith : False).elim
    have h0 : z = w := by
      rcases (actual_collision hp hc (circlePoint_full_disk s.property hu1)
        (circlePoint_full_disk t.property hv1)).mp h1 with h | h
      · exact h
      · have hr := congrArg Complex.re h
        simp only [Complex.neg_re] at hr
        have hzneg := initialDisk_negative_re hzD
        have hwneg := initialDisk_negative_re hwD
        exact (by linarith : False).elim
    have hst : s = t := by
      apply Subtype.ext
      have hn := congrArg (fun a : ℂ => ‖a+(3/4 : ℂ)‖) h0
      dsimp only [z, w] at hn
      simpa only [circle_radius (by linarith [s.property.1] : 0 ≤ (s : ℝ)) hu1,
        circle_radius (by linarith [t.property.1] : 0 ≤ (t : ℝ)) hv1] using hn
    refine ⟨hst, ?_⟩
    have hr := congrArg Complex.re h0
    simp only [z, w, circlePoint, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero] at hr
    have hspos : 0 < (s : ℝ) := by linarith [s.property.1]
    rw [← hst] at hr
    exact mul_left_cancel₀ (ne_of_gt hspos) (by linarith only [hr])
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The full selected closed leaf after four literal polynomial returns. -/
def finalClosedLeaf {p : ℕ} {c : ℝ} (F : Family p c) (s : Radius) : Set ℂ :=
  (fun u : ℝ => ((normalizedReturn c p)^[4]) (circlePoint s u)) '' Icc (F.angle s) 1

/-- Distinct selected closed leaves of the actual fourth image are
disjoint, including their real endpoints. -/
theorem finalClosedLeaf_disjoint {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (F : Family p c)
    (hB : ∀ z ∈ initialDisk,
      (∀ m ≤ 4, ‖((normalizedReturn c p)^[m]) z‖ ≤ 23/20) ∧
        0 < (((normalizedReturn c p)^[2]) z).re ∧
        (((normalizedReturn c p)^[3]) z).re < 0)
    {s t : Radius} (hst : s ≠ t) :
    Disjoint (finalClosedLeaf F s) (finalClosedLeaf F t) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨u, hu, rfl⟩ ⟨v, hv, he⟩
  exact hst ((selected_closed_arc_collision_iff hp hc F hB s t hu hv).mp he.symm).1

/-- Angle parametrization of the actual input semicircle, in radians. -/
def angularPoint (s t : ℝ) : ℂ := circlePoint s (Real.cos t)

/-- On `[0,π]` this is the usual upper circular parametrization. -/
theorem angularPoint_formula (s : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) Real.pi) :
    angularPoint s t = ((-3/4+s*Real.cos t : ℝ) : ℂ) +
      ((s*Real.sin t : ℝ) : ℂ)*Complex.I := by
  unfold angularPoint circlePoint
  rw [← Real.sin_eq_sqrt_one_sub_cos_sq ht.1 ht.2]

private theorem angularPoint_norm_sub_le (s : Radius) {x y : ℝ}
    (hx : x ∈ Icc (0 : ℝ) Real.pi) (hy : y ∈ Icc (0 : ℝ) Real.pi) :
    ‖angularPoint s x-angularPoint s y‖ ≤ |x-y| := by
  have hs : 0 ≤ (s : ℝ) := by linarith [s.property.1]
  have he : angularPoint s x-angularPoint s y =
      (((s : ℝ)*(Real.cos x-Real.cos y) : ℝ) : ℂ) +
        (((s : ℝ)*(Real.sin x-Real.sin y) : ℝ) : ℂ)*Complex.I := by
    rw [angularPoint_formula (s : ℝ) hx, angularPoint_formula (s : ℝ) hy]
    push_cast
    ring
  rw [he]
  calc
    ‖((((s : ℝ)*(Real.cos x-Real.cos y) : ℝ) : ℂ) +
      (((s : ℝ)*(Real.sin x-Real.sin y) : ℝ) : ℂ)*Complex.I)‖ ≤
        ‖(((s : ℝ)*(Real.cos x-Real.cos y) : ℝ) : ℂ)‖ +
          ‖(((s : ℝ)*(Real.sin x-Real.sin y) : ℝ) : ℂ)*Complex.I‖ := norm_add_le _ _
    _ = (s : ℝ)*|Real.cos x-Real.cos y|+(s : ℝ)*|Real.sin x-Real.sin y| := by
      simp [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hs]
    _ ≤ (s : ℝ)*|x-y|+(s : ℝ)*|x-y| :=
      add_le_add (mul_le_mul_of_nonneg_left (Real.abs_cos_sub_cos_le x y) hs)
        (mul_le_mul_of_nonneg_left (Real.abs_sin_sub_sin_le x y) hs)
    _ ≤ |x-y| := by
      have hb := mul_le_mul_of_nonneg_right s.property.2 (abs_nonneg (x-y))
      nlinarith [abs_nonneg (x-y)]

private theorem actual_iterates_norm_sub_le {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c)
    (hB : ∀ z ∈ initialDisk,
      (∀ m ≤ 4, ‖((normalizedReturn c p)^[m]) z‖ ≤ 23/20) ∧
        0 < (((normalizedReturn c p)^[2]) z).re ∧
        (((normalizedReturn c p)^[3]) z).re < 0)
    {z w : ℂ} (hz : z ∈ initialDisk) (hw : w ∈ initialDisk) :
    ∀ m : ℕ, m ≤ 4 →
      ‖((normalizedReturn c p)^[m]) z-((normalizedReturn c p)^[m]) w‖ ≤
        (5 : ℝ)^m*‖z-w‖ := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    have hm' : m ≤ 4 := by omega
    have hb := normalized_return_norm_sub_le c p (by omega) (actual_band hp hc)
      hc.2.1 (actual_small hc) hc.2.2.2.1 ((hB z hz).1 m hm') ((hB w hw).1 m hm')
    rw [iterate_succ_apply', iterate_succ_apply']
    calc
      _ ≤ 5*‖((normalizedReturn c p)^[m]) z-((normalizedReturn c p)^[m]) w‖ := hb
      _ ≤ 5*((5 : ℝ)^m*‖z-w‖) := mul_le_mul_of_nonneg_left (ih hm') (by norm_num)
      _ = (5 : ℝ)^(m+1)*‖z-w‖ := by rw [pow_succ]; ring

/-- The entire actual fourth image of each upper semicircle has a
uniform Lipschitz parametrization in radians. This includes both endpoints. -/
theorem full_fourth_image_lipschitz {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c)
    (hB : ∀ z ∈ initialDisk,
      (∀ m ≤ 4, ‖((normalizedReturn c p)^[m]) z‖ ≤ 23/20) ∧
        0 < (((normalizedReturn c p)^[2]) z).re ∧
        (((normalizedReturn c p)^[3]) z).re < 0)
    (s : Radius) :
    LipschitzOnWith 625 (fun t : ℝ => ((normalizedReturn c p)^[4]) (angularPoint s t))
      (Icc (0 : ℝ) Real.pi) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hxD := circlePoint_mem_initialDisk s
    (show Real.cos x ∈ Icc (-1 : ℝ) 1 from ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩)
  have hyD := circlePoint_mem_initialDisk s
    (show Real.cos y ∈ Icc (-1 : ℝ) 1 from ⟨Real.neg_one_le_cos y, Real.cos_le_one y⟩)
  have hb := actual_iterates_norm_sub_le hp hc hB hxD hyD 4 (by omega)
  norm_num only [show (5 : ℝ)^4 = 625 by norm_num] at hb
  rw [dist_eq_norm, NNReal.coe_ofNat, Real.dist_eq]
  exact hb.trans (mul_le_mul_of_nonneg_left (angularPoint_norm_sub_le s hx hy) (by norm_num))

/-- The selected actual fourth-image arcs are rectifiable, with
bounded variation on their complete closed angular parameter intervals. -/
theorem selected_fourth_image_boundedVariation {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (F : Family p c)
    (hB : ∀ z ∈ initialDisk,
      (∀ m ≤ 4, ‖((normalizedReturn c p)^[m]) z‖ ≤ 23/20) ∧
        0 < (((normalizedReturn c p)^[2]) z).re ∧
        (((normalizedReturn c p)^[3]) z).re < 0)
    (s : Radius) :
    BoundedVariationOn (fun t : ℝ => ((normalizedReturn c p)^[4]) (angularPoint s t))
      (Icc (0 : ℝ) (Real.arccos (F.angle s))) := by
  have hid : BoundedVariationOn (fun t : ℝ => t) (Icc (0 : ℝ) Real.pi) :=
    monotoneOn_id.boundedVariationOn (fun x hx => by
      rw [abs_of_nonneg hx.1]
      exact hx.2)
  have hall := (full_fourth_image_lipschitz hp hc hB s).comp_boundedVariationOn
    (mapsTo_id _) hid
  apply hall.mono
  intro t ht
  exact ⟨ht.1, ht.2.trans (Real.arccos_le_pi _)⟩

/-- Exact complete-angle census for every actual second, third, and
fourth image: only `0`, the selected crossing angle, and `π` are real. -/
theorem full_angle_real_census {p : ℕ} (hp : 17 ≤ p) {c : ℝ}
    (hc : ActualTip p c) (F : Family p c)
    (hB : ∀ z ∈ initialDisk,
      (∀ m ≤ 4, ‖((normalizedReturn c p)^[m]) z‖ ≤ 23/20) ∧
        0 < (((normalizedReturn c p)^[2]) z).re ∧
        (((normalizedReturn c p)^[3]) z).re < 0)
    (s : Radius) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) Real.pi)
    {m : ℕ} (hm : 2 ≤ m) (hm' : m ≤ 4) :
    (((normalizedReturn c p)^[m]) (angularPoint s t)).im = 0 ↔
      t = 0 ∨ t = Real.arccos (F.angle s) ∨ t = Real.pi := by
  have hu : Real.cos t ∈ Icc (-1 : ℝ) 1 := ⟨Real.neg_one_le_cos t, Real.cos_le_one t⟩
  have hneg : Real.cos t = -1 ↔ t = Real.pi := by
    constructor
    · intro h
      have he := congrArg Real.arccos h
      simpa only [Real.arccos_cos ht.1 ht.2, Real.arccos_neg_one] using he
    · rintro rfl
      exact Real.cos_pi
  have hpos : Real.cos t = 1 ↔ t = 0 := by
    constructor
    · intro h
      have he := congrArg Real.arccos h
      simpa only [Real.arccos_cos ht.1 ht.2, Real.arccos_one] using he
    · rintro rfl
      exact Real.cos_zero
  have hcross : Real.cos t = F.angle s ↔ t = Real.arccos (F.angle s) := by
    constructor
    · intro h
      have he := congrArg Real.arccos h
      simpa only [Real.arccos_cos ht.1 ht.2] using he
    · rintro rfl
      exact Real.cos_arccos (family_angle_full F s).1 (family_angle_full F s).2
  change (((normalizedReturn c p)^[m]) (circlePoint s (Real.cos t))).im = 0 ↔ _
  rw [full_semicircle_real_census hp hc F hB s hu m hm hm', hneg, hpos, hcross]
  tauto

/-- One threshold gives the complete-angle real census for every
admissible actual parameter and every radius simultaneously. -/
theorem eventually_all_actual_tips_real_census :
    ∀ᶠ n : ℕ in atTop, ∀ c : ℝ, ActualTip (n+17) c →
      ∀ F : Family (n+17) c, ∀ s : Radius, ∀ t ∈ Icc (0 : ℝ) Real.pi,
        ∀ m : ℕ, 2 ≤ m → m ≤ 4 →
          (((normalizedReturn c (n+17))^[m]) (angularPoint s t)).im = 0 ↔
            t = 0 ∨ t = Real.arccos (F.angle s) ∨ t = Real.pi := by
  filter_upwards [ActualCrestSupport.eventually_all_actual_tips_support] with n hn
  intro c hc F s t ht m hm hm'
  exact full_angle_real_census (by omega) hc F (hn c hc).1 s ht hm hm'

/-- One threshold gives collision-free actual closed leaves for every
admissible parameter, jointly in the radial and angular coordinates. -/
theorem eventually_all_actual_tips_closed_arc_injective :
    ∀ᶠ n : ℕ in atTop, ∀ c : ℝ, ActualTip (n+17) c →
      ∀ F : Family (n+17) c, ∀ s t : Radius,
        ∀ u ∈ Icc (F.angle s) 1, ∀ v ∈ Icc (F.angle t) 1,
          ((normalizedReturn c (n+17))^[4]) (circlePoint s u) =
            ((normalizedReturn c (n+17))^[4]) (circlePoint t v) ↔ s = t ∧ u = v := by
  filter_upwards [ActualCrestSupport.eventually_all_actual_tips_support] with n hn
  intro c hc F s t u hu v hv
  exact selected_closed_arc_collision_iff (by omega) hc F (hn c hc).1 s t hu hv

end
end ActualCrestArcCensus
