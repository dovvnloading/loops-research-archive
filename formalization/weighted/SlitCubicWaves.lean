import SlitCubicEdges
import SlitCubicClosedChart
import MarkedSlitTransport
import SlitPotentialReflection

/-!
# Actual parent Waves from reflected cubic rectangle horizontals

The construction follows one horizontal line across the cubic period
rectangle in the lower sheet and returns in the upper sheet. The two
copies meet at the actual left real-ray preimage.
-/

namespace SlitCubicWaves

open Set Filter Function MeasureTheory MarkedSlitTransport
open SlitCubicCalibration SlitCubicBoundary SlitCubicBoundaryRange SlitCubicEdges
open SlitCubicClosedChart SlitCubicRectangle
open scoped Topology
noncomputable section

def rectanglePoint (B y : ℝ) (t : Parameter) : ℂ :=
  (B*|2*(t:ℝ)-1|:ℝ)+(y:ℂ)*Complex.I

@[simp] theorem rectanglePoint_re (B y : ℝ) (t : Parameter) :
    (rectanglePoint B y t).re = B*|2*(t:ℝ)-1| := by simp [rectanglePoint]

@[simp] theorem rectanglePoint_im (B y : ℝ) (t : Parameter) :
    (rectanglePoint B y t).im = y := by simp [rectanglePoint]

theorem rectanglePoint_continuous (B y : ℝ) : Continuous (rectanglePoint B y) := by
  unfold rectanglePoint
  fun_prop

theorem rectanglePoint_re_mem_Icc {B y : ℝ} (hB : 0 < B) (t : Parameter) :
    (rectanglePoint B y t).re ∈ Icc 0 B := by
  rw [rectanglePoint_re]
  have ha : |2*(t:ℝ)-1| ≤ 1 := abs_le.mpr ⟨by linarith [t.property.1], by linarith [t.property.2]⟩
  exact ⟨mul_nonneg hB.le (abs_nonneg _), by nlinarith⟩

theorem rectanglePoint_re_lt {B y : ℝ} (hB : 0 < B) {t : Parameter}
    (ht : t ∈ parameterInterior) : (rectanglePoint B y t).re < B := by
  rw [rectanglePoint_re]
  have ha : |2*(t:ℝ)-1| < 1 := abs_lt.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  nlinarith

theorem rectanglePoint_re_pos {B y : ℝ} (hB : 0 < B) {t : Parameter}
    (ht : (t:ℝ) ≠ 1/2) : 0 < (rectanglePoint B y t).re := by
  rw [rectanglePoint_re]
  apply mul_pos hB (abs_pos.mpr ?_)
  intro he
  apply ht
  linarith

@[simp] theorem rectanglePoint_initial (B y : ℝ) :
    rectanglePoint B y initial = (B:ℂ)+(y:ℂ)*Complex.I := by
  simp [rectanglePoint,initial]

@[simp] theorem rectanglePoint_terminal (B y : ℝ) :
    rectanglePoint B y terminal = (B:ℂ)+(y:ℂ)*Complex.I := by
  norm_num [rectanglePoint,terminal]

@[simp] theorem rectanglePoint_middle (B y : ℝ) :
    rectanglePoint B y middle = (y:ℂ)*Complex.I := by
  norm_num [rectanglePoint,middle]

def rawCurve (G : ℂ → ℂ) (B y : ℝ) (t : Parameter) : ℂ :=
  if (t:ℝ) ≤ 1/2 then starRingEnd ℂ (G (rectanglePoint B y t))
  else G (rectanglePoint B y t)

theorem rawCurve_continuous {G : ℂ → ℂ} {B y : ℝ}
    (hG : Continuous (fun t : Parameter => G (rectanglePoint B y t)))
    (hleft : (G ((y:ℂ)*Complex.I)).im = 0) : Continuous (rawCurve G B y) := by
  apply continuous_if_le continuous_subtype_val continuous_const
    ((Complex.continuous_conj.comp hG).continuousOn) hG.continuousOn
  intro t ht
  have he : rectanglePoint B y t = (y:ℂ)*Complex.I := by
    simp [rectanglePoint,ht]
  rw [he]
  apply Complex.ext <;> simp [he,hleft]

theorem fold_rawCurve {G : ℂ → ℂ} {B y : ℝ} (t : Parameter)
    (hG : 0 ≤ (G (rectanglePoint B y t)).im) :
    SlitPotentialReflection.fold (rawCurve G B y t) = G (rectanglePoint B y t) := by
  unfold rawCurve
  split_ifs
  · apply Complex.ext <;> simp [SlitPotentialReflection.fold,abs_of_nonneg hG]
  · exact SlitPotentialReflection.fold_eq_self hG


private theorem rectanglePoint_mem_band {a b c y : ℝ} (hab : a < b) (hbc : b < c)
    (hy : y ∈ Ioo (-height a b c) 0) (t : Parameter) :
    rectanglePoint (period a b c) y t ∈ closedHorizontalBand (period a b c) (height a b c) := by
  exact ⟨(rectanglePoint_re_mem_Icc (period_pos hab hbc) t).1,
    (rectanglePoint_re_mem_Icc (period_pos hab hbc) t).2, by simpa only [rectanglePoint_im,mem_Ioo] using hy⟩

/-- The complete reflected horizontal leaf in the actual slit plane. -/
def curve {a b c y : ℝ} (hab : a < b) (hbc : b < c)
    (hy : y ∈ Ioo (-height a b c) 0) : Curve :=
  ⟨rawCurve (closedInverse a b c) (period a b c) y,
    rawCurve_continuous
      ((closedInverse_continuousOn hab hbc).comp_continuous
        (rectanglePoint_continuous _ _) (rectanglePoint_mem_band hab hbc hy))
      (closedInverse_left_edge hab hbc hy).1⟩

@[simp] theorem curve_apply {a b c y : ℝ} (hab : a < b) (hbc : b < c)
    (hy : y ∈ Ioo (-height a b c) 0) (t : Parameter) :
    curve hab hbc hy t = rawCurve (closedInverse a b c) (period a b c) y t := rfl

theorem tail_fold_curve {a b c y : ℝ} (hab : a < b) (hbc : b < c)
    (hy : y ∈ Ioo (-height a b c) 0) (t : Parameter) :
    tail a b c (SlitPotentialReflection.fold (curve hab hbc hy t)) =
      rectanglePoint (period a b c) y t := by
  rw [curve_apply,fold_rawCurve t (closedInverse_mem_source hab hbc (rectanglePoint_mem_band hab hbc hy t)).1]
  exact tail_closedInverse hab hbc (rectanglePoint_mem_band hab hbc hy t)

@[simp] theorem curve_initial {a b c y : ℝ} (hab : a < b) (hbc : b < c)
    (hy : y ∈ Ioo (-height a b c) 0) :
    curve hab hbc hy initial =
      closedInverse a b c ((period a b c:ℂ)+(y:ℂ)*Complex.I) := by
  rw [curve_apply,rawCurve,if_pos (show (initial:ℝ) ≤ 1/2 by norm_num [initial]),
    rectanglePoint_initial]
  apply Complex.ext <;> simp [(closedInverse_right_edge hab hbc hy).1]

@[simp] theorem curve_terminal {a b c y : ℝ} (hab : a < b) (hbc : b < c)
    (hy : y ∈ Ioo (-height a b c) 0) :
    curve hab hbc hy terminal =
      closedInverse a b c ((period a b c:ℂ)+(y:ℂ)*Complex.I) := by
  rw [curve_apply,rawCurve,if_neg (show ¬(terminal:ℝ) ≤ 1/2 by norm_num [terminal]),
    rectanglePoint_terminal]

@[simp] theorem curve_middle {a b c y : ℝ} (hab : a < b) (hbc : b < c)
    (hy : y ∈ Ioo (-height a b c) 0) :
    curve hab hbc hy middle = closedInverse a b c ((y:ℂ)*Complex.I) := by
  rw [curve_apply,rawCurve,if_pos (show (middle:ℝ) ≤ 1/2 by norm_num [middle]),
    rectanglePoint_middle]
  apply Complex.ext <;> simp [(closedInverse_left_edge hab hbc hy).1]

theorem curve_below {a b c y : ℝ} (hab : a < b) (hbc : b < c)
    (hy : y ∈ Ioo (-height a b c) 0) {t : Parameter}
    (ht0 : 0 < (t:ℝ)) (hth : (t:ℝ) < 1/2) : (curve hab hbc hy t).im < 0 := by
  have ht : t ∈ parameterInterior := ⟨ht0,by linarith⟩
  have hp := closedInverse_mem_upper hab hbc (w := rectanglePoint (period a b c) y t)
    ⟨rectanglePoint_re_pos (period_pos hab hbc) (by linarith),
      rectanglePoint_re_lt (period_pos hab hbc) ht, by simpa only [rectanglePoint_im,mem_Ioo] using hy⟩
  simpa only [curve_apply,rawCurve,if_pos hth.le,Complex.conj_im] using neg_neg_of_pos (show 0 < (closedInverse a b c (rectanglePoint (period a b c) y t)).im from hp)

theorem curve_above {a b c y : ℝ} (hab : a < b) (hbc : b < c)
    (hy : y ∈ Ioo (-height a b c) 0) {t : Parameter}
    (hth : 1/2 < (t:ℝ)) (ht1 : (t:ℝ) < 1) : 0 < (curve hab hbc hy t).im := by
  have ht : t ∈ parameterInterior := ⟨by linarith,ht1⟩
  have hp := closedInverse_mem_upper hab hbc (w := rectanglePoint (period a b c) y t)
    ⟨rectanglePoint_re_pos (period_pos hab hbc) (by linarith),
      rectanglePoint_re_lt (period_pos hab hbc) ht, by simpa only [rectanglePoint_im,mem_Ioo] using hy⟩
  simpa only [curve_apply,rawCurve,if_neg (not_le.mpr hth)] using (show 0 < (closedInverse a b c (rectanglePoint (period a b c) y t)).im from hp)

theorem curve_simple {a b c y : ℝ} (hab : a < b) (hbc : b < c)
    (hy : y ∈ Ioo (-height a b c) 0) : Simple (curve hab hbc hy) := by
  intro s hs t ht heq
  have hpoint := congrArg (fun z => tail a b c (SlitPotentialReflection.fold z)) heq
  rw [tail_fold_curve,tail_fold_curve] at hpoint
  have hr := congrArg Complex.re hpoint
  simp only [rectanglePoint_re] at hr
  have ha : |2*(s:ℝ)-1| = |2*(t:ℝ)-1| := mul_left_cancel₀ (period_pos hab hbc).ne' hr
  by_cases hsle : (s:ℝ) ≤ 1/2
  · by_cases htle : (t:ℝ) ≤ 1/2
    · rw [abs_of_nonpos (by linarith : 2*(s:ℝ)-1 ≤ 0),
        abs_of_nonpos (by linarith : 2*(t:ℝ)-1 ≤ 0)] at ha
      apply Subtype.ext
      linarith
    · have hsn : (curve hab hbc hy s).im ≤ 0 := by
        simp only [curve_apply,rawCurve,if_pos hsle,Complex.conj_im]
        exact neg_nonpos.mpr (closedInverse_mem_source hab hbc (rectanglePoint_mem_band hab hbc hy s)).1
      have htp := curve_above hab hbc hy (lt_of_not_ge htle) ht.2
      rw [heq] at hsn
      linarith
  · by_cases htle : (t:ℝ) ≤ 1/2
    · have htn : (curve hab hbc hy t).im ≤ 0 := by
        simp only [curve_apply,rawCurve,if_pos htle,Complex.conj_im]
        exact neg_nonpos.mpr (closedInverse_mem_source hab hbc (rectanglePoint_mem_band hab hbc hy t)).1
      have hsp := curve_above hab hbc hy (lt_of_not_ge hsle) hs.2
      rw [heq] at hsp
      linarith
    · rw [abs_of_nonneg (by linarith : 0 ≤ 2*(s:ℝ)-1),
        abs_of_nonneg (by linarith : 0 ≤ 2*(t:ℝ)-1)] at ha
      apply Subtype.ext
      linarith

theorem curve_leftReference {a b c y : ℝ} (hab : a < b) (hbc : b < c)
    (hy : y ∈ Ioo (-height a b c) 0) : LeftReference a (curve hab hbc hy) where
  simple := curve_simple hab hbc hy
  below := fun _ ht0 hth => curve_below hab hbc hy ht0 hth
  crossing_re := by simpa only [curve_middle] using (closedInverse_left_edge hab hbc hy).2
  crossing_im := by simpa only [curve_middle] using (closedInverse_left_edge hab hbc hy).1
  above := fun _ hth ht1 => curve_above hab hbc hy hth ht1

/-- Every actual leaf point lies on one of the two closed inverse-horizontal segments. -/
theorem trace_curve_subset_segments {a b c y : ℝ} (hab : a < b) (hbc : b < c)
    (hy : y ∈ Ioo (-height a b c) 0) :
    trace (curve hab hbc hy) ⊆
      (fun x : ℝ => closedInverse a b c ((x:ℂ)+(y:ℂ)*Complex.I)) '' Icc 0 (period a b c) ∪
      (fun x : ℝ => starRingEnd ℂ (closedInverse a b c ((x:ℂ)+(y:ℂ)*Complex.I))) ''
        Icc 0 (period a b c) := by
  rintro z ⟨t,rfl⟩
  have hx := rectanglePoint_re_mem_Icc (y := y) (period_pos hab hbc) t
  rw [rectanglePoint_re] at hx
  change rawCurve _ _ _ t ∈ _
  unfold rawCurve
  split_ifs
  · exact Or.inr ⟨_,hx,rfl⟩
  · exact Or.inl ⟨_,hx,rfl⟩

theorem curve_interior_in_cutPlane {a b c y : ℝ} (hab : a < b) (hbc : b < c)
    (hy : y ∈ Ioo (-height a b c) 0) {t : Parameter} (ht : t ∈ parameterInterior) :
    (curve hab hbc hy t).im ≠ 0 ∨ (curve hab hbc hy t).re < a := by
  rcases lt_trichotomy (t:ℝ) (1/2) with h | h | h
  · exact Or.inl (curve_below hab hbc hy ht.1 h).ne
  · have he : t = middle := Subtype.ext h
    subst t
    exact Or.inr (by simpa only [curve_middle] using (closedInverse_left_edge hab hbc hy).2)
  · exact Or.inl (curve_above hab hbc hy h ht.2).ne'

theorem curve_avoids (M : Marking) {y : ℝ}
    (hy : y ∈ Ioo (-height M.left M.first M.second) 0)
    {t : Parameter} (ht : t ∈ parameterInterior) :
    curve M.left_lt_first M.first_lt_second hy t ∉ M.slit := by
  intro hz
  rcases curve_interior_in_cutPlane M.left_lt_first M.first_lt_second hy ht with h | h
  · exact h hz.1
  · exact (not_lt_of_ge hz.2.1) h

theorem curve_parentLeaf (M : Marking) {y : ℝ}
    (hy : y ∈ Ioo (-height M.left M.first M.second) 0) :
    ParentLeaf M univ (curve M.left_lt_first M.first_lt_second hy) where
  simple := curve_simple M.left_lt_first M.first_lt_second hy
  first_end := by
    rw [curve_initial]
    exact closedInverse_right_edge M.left_lt_first M.first_lt_second hy
  last_end := by
    rw [curve_terminal]
    exact closedInverse_right_edge M.left_lt_first M.first_lt_second hy
  lower := ⟨1/2,by norm_num, fun _ ht0 hth =>
    curve_below M.left_lt_first M.first_lt_second hy ht0 hth⟩
  upper := ⟨1/2,by norm_num, fun _ hth ht1 =>
    curve_above M.left_lt_first M.first_lt_second hy (by linarith) ht1⟩
  inside := fun _ _ => mem_univ _
  avoids := fun _ ht => curve_avoids M hy ht
  left_class := by
    refine ⟨curve M.left_lt_first M.first_lt_second hy,
      curve_leftReference M.left_lt_first M.first_lt_second hy, ?_⟩
    refine ⟨⟨fun p => curve M.left_lt_first M.first_lt_second hy p.2,
      (curve M.left_lt_first M.first_lt_second hy).continuous.comp continuous_snd⟩,
      fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl,?_⟩
    exact fun _ _ ht => curve_avoids M hy ht

/-- All inverse-horizontal heights, with no deletion at any interior height. -/
def family (M : Marking) : Set Curve :=
  range (fun y : Ioo (-height M.left M.first M.second) 0 =>
    curve M.left_lt_first M.first_lt_second y.property)

theorem family_disjoint (M : Marking) :
    ∀ γ ∈ family M, ∀ η ∈ family M, γ ≠ η →
      Disjoint (interiorTrace γ) (interiorTrace η) := by
  rintro γ ⟨y,rfl⟩ η ⟨v,rfl⟩ hne
  apply Set.disjoint_left.mpr
  rintro z ⟨s,_,hs⟩ ⟨t,_,ht⟩
  have he := congrArg (fun w => tail M.left M.first M.second (SlitPotentialReflection.fold w))
    (hs.trans ht.symm)
  rw [tail_fold_curve,tail_fold_curve] at he
  have hy := congrArg Complex.im he
  simp only [rectanglePoint_im] at hy
  have hyv : y = v := Subtype.ext hy
  subst v
  exact hne rfl

private theorem exists_upper_parameter {B x y : ℝ} (hB : 0 < B)
    (hx : x ∈ Ioo 0 B) :
    ∃ t : Parameter, t ∈ parameterInterior ∧ 1/2 < (t:ℝ) ∧
      rectanglePoint B y t = (x:ℂ)+(y:ℂ)*Complex.I := by
  have hq0 : 0 < x/B := div_pos hx.1 hB
  have hq1 : x/B < 1 := (div_lt_one hB).mpr hx.2
  refine ⟨⟨(1+x/B)/2,by constructor <;> linarith⟩,
    ⟨by dsimp; linarith,by dsimp; linarith⟩,by dsimp; linarith,?_⟩
  apply Complex.ext
  · simp only [rectanglePoint_re,Complex.add_re,Complex.ofReal_re,Complex.mul_I_re,
      Complex.ofReal_im,neg_zero,add_zero]
    rw [show 2*((1+x/B)/2)-1 = x/B by ring,abs_of_pos hq0]
    field_simp
  · simp

private theorem exists_lower_parameter {B x y : ℝ} (hB : 0 < B)
    (hx : x ∈ Ioo 0 B) :
    ∃ t : Parameter, t ∈ parameterInterior ∧ (t:ℝ) < 1/2 ∧
      rectanglePoint B y t = (x:ℂ)+(y:ℂ)*Complex.I := by
  have hq0 : 0 < x/B := div_pos hx.1 hB
  have hq1 : x/B < 1 := (div_lt_one hB).mpr hx.2
  refine ⟨⟨(1-x/B)/2,by constructor <;> linarith⟩,
    ⟨by dsimp; linarith,by dsimp; linarith⟩,by dsimp; linarith,?_⟩
  apply Complex.ext
  · simp only [rectanglePoint_re,Complex.add_re,Complex.ofReal_re,Complex.mul_I_re,
      Complex.ofReal_im,neg_zero,add_zero]
    rw [show 2*((1-x/B)/2)-1 = -(x/B) by ring,abs_neg,abs_of_pos hq0]
    field_simp
  · simp

private theorem upper_mem_support_family (M : Marking) {z : ℂ} (hz : 0 < z.im) :
    z ∈ support (family M) := by
  have hw := tail_mem_openRectangle M.left_lt_first M.first_lt_second hz
  have hy : (tail M.left M.first M.second z).im ∈
      Ioo (-height M.left M.first M.second) 0 := ⟨hw.2.2.1,hw.2.2.2⟩
  obtain ⟨t,ht,hth,hpoint⟩ := exists_upper_parameter
    (y := (tail M.left M.first M.second z).im)
    (period_pos M.left_lt_first M.first_lt_second) ⟨hw.1,hw.2.1⟩
  have hpoint' : rectanglePoint (period M.left M.first M.second)
      (tail M.left M.first M.second z).im t = tail M.left M.first M.second z := by
    rw [hpoint]
    exact Complex.re_add_im _
  simp only [MarkedSlitTransport.support,mem_iUnion]
  refine ⟨curve M.left_lt_first M.first_lt_second hy,⟨⟨_,hy⟩,rfl⟩,t,ht,?_⟩
  rw [curve_apply,rawCurve,if_neg (not_le.mpr hth),hpoint']
  exact closedInverse_tail M.left_lt_first M.first_lt_second
    (upper_subset_closedSource M.left_lt_first M.first_lt_second hz)

private theorem lower_mem_support_family (M : Marking) {z : ℂ} (hz : z.im < 0) :
    z ∈ support (family M) := by
  have hz' : 0 < (starRingEnd ℂ z).im := by simpa using neg_pos.mpr hz
  have hw := tail_mem_openRectangle M.left_lt_first M.first_lt_second hz'
  have hy : (tail M.left M.first M.second (starRingEnd ℂ z)).im ∈
      Ioo (-height M.left M.first M.second) 0 := ⟨hw.2.2.1,hw.2.2.2⟩
  obtain ⟨t,ht,hth,hpoint⟩ := exists_lower_parameter
    (y := (tail M.left M.first M.second (starRingEnd ℂ z)).im)
    (period_pos M.left_lt_first M.first_lt_second) ⟨hw.1,hw.2.1⟩
  have hpoint' : rectanglePoint (period M.left M.first M.second)
      (tail M.left M.first M.second (starRingEnd ℂ z)).im t =
        tail M.left M.first M.second (starRingEnd ℂ z) := by
    rw [hpoint]
    exact Complex.re_add_im _
  simp only [MarkedSlitTransport.support,mem_iUnion]
  refine ⟨curve M.left_lt_first M.first_lt_second hy,⟨⟨_,hy⟩,rfl⟩,t,ht,?_⟩
  rw [curve_apply,rawCurve,if_pos hth.le,hpoint',
    closedInverse_tail M.left_lt_first M.first_lt_second
      (upper_subset_closedSource M.left_lt_first M.first_lt_second hz')]
  simp

private theorem real_left_mem_support_family (M : Marking) {x : ℝ} (hx : x < M.left) :
    (x:ℂ) ∈ support (family M) := by
  have hy := tail_im_mem_Ioo_left M.left_lt_first M.first_lt_second hx
  have hz : tail M.left M.first M.second (x:ℂ) =
      ((tail M.left M.first M.second (x:ℂ)).im:ℂ)*Complex.I := by
    apply Complex.ext
    · simpa using tail_re_left M.left_lt_first M.first_lt_second hx.le
    · simp
  simp only [MarkedSlitTransport.support,mem_iUnion]
  refine ⟨curve M.left_lt_first M.first_lt_second hy,⟨⟨_,hy⟩,rfl⟩,middle,
    ⟨by norm_num [middle],by norm_num [middle]⟩,?_⟩
  rw [curve_middle,←hz]
  exact closedInverse_tail M.left_lt_first M.first_lt_second
    (real_left_mem_closedSource M.left_lt_first M.first_lt_second hx)

/-- The complete family fills the plane cut along the real ray from the left pole. -/
theorem support_family (M : Marking) :
    support (family M) = {z : ℂ | z.im ≠ 0 ∨ z.re < M.left} := by
  ext z
  constructor
  · simp only [MarkedSlitTransport.support,mem_iUnion]
    rintro ⟨γ,⟨y,rfl⟩,t,ht,rfl⟩
    exact curve_interior_in_cutPlane M.left_lt_first M.first_lt_second y.property ht
  · intro hz
    by_cases hi : z.im = 0
    · have hr : z.re < M.left := hz.resolve_left (not_not.mpr hi)
      have he : (z.re:ℂ) = z := by apply Complex.ext <;> simp [hi]
      rw [←he]
      exact real_left_mem_support_family M hr
    · rcases lt_or_gt_of_ne hi with hneg | hpos
      · exact lower_mem_support_family M hneg
      · exact upper_mem_support_family M hpos

/-- An actual Borel parent Wave attaining every inverse-horizontal height. -/
theorem family_parentWave (M : Marking) : ParentWave M univ (family M) where
  borel := by
    rw [support_family]
    apply IsOpen.measurableSet
    exact (isOpen_ne_fun Complex.continuous_im continuous_const).union
      (isOpen_lt Complex.continuous_re continuous_const)
  leaf := by
    rintro γ ⟨y,rfl⟩
    exact curve_parentLeaf M y.property
  disjoint := family_disjoint M

end
end SlitCubicWaves
