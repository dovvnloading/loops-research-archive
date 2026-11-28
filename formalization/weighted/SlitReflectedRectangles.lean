import SlitCubicWaves
import SlitPairableWaves
import Mathlib.Topology.Sets.Compacts

/-!
# Reflected rectangle horizontals as geometric pairable Waves

The construction uses the actual closed inverse on a rectangle band.
Joint continuity gives a countable compact exhaustion of the full
support, so no measurable-family premise or omitted height is needed.
-/

namespace SlitReflectedRectangles

open Set Function Filter MeasureTheory MarkedSlitTransport
open SlitCubicWaves SlitCubicClosedChart SlitCubicRectangle SlitPairableWaves
open scoped Topology

noncomputable section

structure InverseData (B A : ℝ) where
  toFun : ℂ → ℂ
  width_pos : 0 < B
  height_pos : 0 < A
  continuous : ContinuousOn toFun (closedHorizontalBand B A)
  injective : InjOn toFun (closedHorizontalBand B A)
  upper : ∀ w ∈ openRectangle B A, 0 < (toFun w).im
  left_real : ∀ y ∈ Ioo (-A) 0, (toFun ((y : ℂ)*Complex.I)).im = 0
  right_real : ∀ y ∈ Ioo (-A) 0, (toFun ((B : ℂ)+(y : ℂ)*Complex.I)).im = 0

instance {B A : ℝ} : CoeFun (InverseData B A) (fun _ => ℂ → ℂ) := ⟨InverseData.toFun⟩

variable {B A : ℝ} (C : InverseData B A)

theorem nonneg_of_mem_band {w : ℂ} (hw : w ∈ closedHorizontalBand B A) :
    0 ≤ (C w).im := by
  by_cases h0 : w.re = 0
  · have he : w = (w.im : ℂ)*Complex.I := by apply Complex.ext <;> simp [h0]
    rw [he,C.left_real _ ⟨hw.2.2.1,hw.2.2.2⟩]
  by_cases hB : w.re = B
  · have he : w = (B : ℂ)+(w.im : ℂ)*Complex.I := by apply Complex.ext <;> simp [hB]
    rw [he,C.right_real _ ⟨hw.2.2.1,hw.2.2.2⟩]
  exact (C.upper w ⟨lt_of_le_of_ne hw.1 (Ne.symm h0),lt_of_le_of_ne hw.2.1 hB,
    hw.2.2.1,hw.2.2.2⟩).le

include C in
theorem rectanglePoint_mem_band {y : ℝ} (hy : y ∈ Ioo (-A) 0) (t : Parameter) :
    rectanglePoint B y t ∈ closedHorizontalBand B A :=
  ⟨(rectanglePoint_re_mem_Icc C.width_pos t).1,(rectanglePoint_re_mem_Icc C.width_pos t).2,
    by simpa only [rectanglePoint_im] using hy.1,by simpa only [rectanglePoint_im] using hy.2⟩

def curve {y : ℝ} (hy : y ∈ Ioo (-A) 0) : Curve :=
  ⟨rawCurve C B y,rawCurve_continuous
    (C.continuous.comp_continuous (rectanglePoint_continuous _ _) (rectanglePoint_mem_band C hy))
    (C.left_real y hy)⟩

@[simp] theorem curve_apply {y : ℝ} (hy : y ∈ Ioo (-A) 0) (t : Parameter) :
    curve C hy t = rawCurve C B y t := rfl

theorem fold_curve {y : ℝ} (hy : y ∈ Ioo (-A) 0) (t : Parameter) :
    SlitPotentialReflection.fold (curve C hy t) = C (rectanglePoint B y t) :=
  fold_rawCurve t (nonneg_of_mem_band C (rectanglePoint_mem_band C hy t))

@[simp] theorem curve_initial {y : ℝ} (hy : y ∈ Ioo (-A) 0) :
    curve C hy initial = C ((B : ℂ)+(y : ℂ)*Complex.I) := by
  rw [curve_apply,rawCurve,if_pos (show (initial : ℝ) ≤ 1/2 by norm_num [initial]),rectanglePoint_initial]
  apply Complex.ext <;> simp [C.right_real y hy]

@[simp] theorem curve_terminal {y : ℝ} (hy : y ∈ Ioo (-A) 0) :
    curve C hy terminal = C ((B : ℂ)+(y : ℂ)*Complex.I) := by
  rw [curve_apply,rawCurve,if_neg (show ¬(terminal : ℝ) ≤ 1/2 by norm_num [terminal]),rectanglePoint_terminal]

@[simp] theorem curve_middle {y : ℝ} (hy : y ∈ Ioo (-A) 0) :
    curve C hy middle = C ((y : ℂ)*Complex.I) := by
  rw [curve_apply,rawCurve,if_pos (show (middle : ℝ) ≤ 1/2 by norm_num [middle]),rectanglePoint_middle]
  apply Complex.ext <;> simp [C.left_real y hy]

theorem curve_below {y : ℝ} (hy : y ∈ Ioo (-A) 0) {t : Parameter}
    (ht0 : 0 < (t : ℝ)) (hth : (t : ℝ) < 1/2) : (curve C hy t).im < 0 := by
  have hp := C.upper (rectanglePoint B y t)
    ⟨rectanglePoint_re_pos C.width_pos (by linarith),
      rectanglePoint_re_lt C.width_pos ⟨ht0,by linarith⟩,
      by simpa only [rectanglePoint_im] using hy.1,by simpa only [rectanglePoint_im] using hy.2⟩
  simpa only [curve_apply,rawCurve,if_pos hth.le,Complex.conj_im] using neg_neg_of_pos hp

theorem curve_above {y : ℝ} (hy : y ∈ Ioo (-A) 0) {t : Parameter}
    (hth : 1/2 < (t : ℝ)) (ht1 : (t : ℝ) < 1) : 0 < (curve C hy t).im := by
  have hp := C.upper (rectanglePoint B y t)
    ⟨rectanglePoint_re_pos C.width_pos (by linarith),
      rectanglePoint_re_lt C.width_pos ⟨by linarith,ht1⟩,
      by simpa only [rectanglePoint_im] using hy.1,by simpa only [rectanglePoint_im] using hy.2⟩
  simpa only [curve_apply,rawCurve,if_neg (not_le.mpr hth)] using hp

theorem curve_simple {y : ℝ} (hy : y ∈ Ioo (-A) 0) : Simple (curve C hy) := by
  intro s hs t ht heq
  have hfold := congrArg SlitPotentialReflection.fold heq
  rw [fold_curve,fold_curve] at hfold
  have he := C.injective (rectanglePoint_mem_band C hy s) (rectanglePoint_mem_band C hy t) hfold
  have hr := congrArg Complex.re he
  simp only [rectanglePoint_re] at hr
  have ha := mul_left_cancel₀ C.width_pos.ne' hr
  by_cases hsle : (s : ℝ) ≤ 1/2
  · by_cases htle : (t : ℝ) ≤ 1/2
    · rw [abs_of_nonpos (by linarith : 2*(s : ℝ)-1 ≤ 0),
        abs_of_nonpos (by linarith : 2*(t : ℝ)-1 ≤ 0)] at ha
      apply Subtype.ext
      linarith
    · have hsn : (curve C hy s).im ≤ 0 := by
        simp only [curve_apply,rawCurve,if_pos hsle,Complex.conj_im]
        exact neg_nonpos.mpr (nonneg_of_mem_band C (rectanglePoint_mem_band C hy s))
      have htp := curve_above C hy (lt_of_not_ge htle) ht.2
      rw [heq] at hsn
      linarith
  · by_cases htle : (t : ℝ) ≤ 1/2
    · have htn : (curve C hy t).im ≤ 0 := by
        simp only [curve_apply,rawCurve,if_pos htle,Complex.conj_im]
        exact neg_nonpos.mpr (nonneg_of_mem_band C (rectanglePoint_mem_band C hy t))
      have hsp := curve_above C hy (lt_of_not_ge hsle) hs.2
      rw [heq] at hsp
      linarith
    · rw [abs_of_nonneg (by linarith : 0 ≤ 2*(s : ℝ)-1),
        abs_of_nonneg (by linarith : 0 ≤ 2*(t : ℝ)-1)] at ha
      apply Subtype.ext
      linarith

theorem curve_mem_source {V : Set ℂ}
    (hV : MapsTo C (closedHorizontalBand B A) V) (hconj : MapsTo (starRingEnd ℂ) V V)
    {y : ℝ} (hy : y ∈ Ioo (-A) 0) (t : Parameter) : curve C hy t ∈ V := by
  have hz := hV (rectanglePoint_mem_band C hy t)
  rw [curve_apply,rawCurve]
  split_ifs
  · exact hconj hz
  · exact hz

theorem curve_leftReference (M : Marking) {y : ℝ} (hy : y ∈ Ioo (-A) 0)
    (hleft : (C ((y : ℂ)*Complex.I)).re < M.left) : LeftReference M.left (curve C hy) where
  simple := curve_simple C hy
  below := fun _ ht0 hth => curve_below C hy ht0 hth
  crossing_re := by simpa only [curve_middle] using hleft
  crossing_im := by simpa only [curve_middle] using C.left_real y hy
  above := fun _ hth ht1 => curve_above C hy hth ht1

theorem curve_avoids (M : Marking) {y : ℝ} (hy : y ∈ Ioo (-A) 0)
    (hleft : (C ((y : ℂ)*Complex.I)).re < M.left)
    {t : Parameter} (ht : t ∈ parameterInterior) : curve C hy t ∉ M.slit := by
  intro hslit
  rcases lt_trichotomy (t : ℝ) (1/2) with h | h | h
  · have hm := curve_below C hy ht.1 h
    exact (ne_of_lt hm) hslit.1
  · have he : t = middle := Subtype.ext h
    subst t
    rw [curve_middle] at hslit
    exact (not_lt_of_ge hslit.2.1) hleft
  · have hm := curve_above C hy h ht.2
    exact (ne_of_gt hm) hslit.1

theorem curve_parentLeaf (M : Marking) {V : Set ℂ}
    (hV : MapsTo C (closedHorizontalBand B A) V) (hconj : MapsTo (starRingEnd ℂ) V V)
    {y : ℝ} (hy : y ∈ Ioo (-A) 0)
    (hleft : (C ((y : ℂ)*Complex.I)).re < M.left)
    (hright : M.ends (C ((B : ℂ)+(y : ℂ)*Complex.I))) : ParentLeaf M V (curve C hy) where
  simple := curve_simple C hy
  first_end := by simpa only [curve_initial] using hright
  last_end := by simpa only [curve_terminal] using hright
  lower := ⟨1/2,by norm_num,fun _ ht0 hth => curve_below C hy ht0 hth⟩
  upper := ⟨1/2,by norm_num,fun _ hth ht1 => curve_above C hy (by linarith) ht1⟩
  inside := fun _ _ => curve_mem_source C hV hconj hy _
  avoids := fun _ ht => curve_avoids C M hy hleft ht
  left_class := by
    refine ⟨curve C hy,curve_leftReference C M hy hleft,?_⟩
    refine ⟨⟨fun p => curve C hy p.2,(curve C hy).continuous.comp continuous_snd⟩,
      fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl,?_⟩
    exact fun _ _ ht => curve_avoids C M hy hleft ht

theorem curve_temporalPair {V T J₀ J₁ : Set ℂ}
    (hV : MapsTo C (closedHorizontalBand B A) V) (hconj : MapsTo (starRingEnd ℂ) V V)
    (hT : ∀ z ∈ T, z.im = 0) {y : ℝ} (hy : y ∈ Ioo (-A) 0)
    (hleft : C ((y : ℂ)*Complex.I) ∈ T ∩ J₀)
    (hright : C ((B : ℂ)+(y : ℂ)*Complex.I) ∈ T ∩ J₁) :
    TemporalPair V T J₀ J₁ (curve C hy) middle middle where
  first_interior := ⟨by norm_num [middle],by norm_num [middle]⟩
  last_interior := ⟨by norm_num [middle],by norm_num [middle]⟩
  ordered := le_rfl
  initial_contact := ⟨curve_mem_source C hV hconj hy initial,by simpa only [curve_initial,mem_inter_iff] using hright⟩
  terminal_contact := ⟨curve_mem_source C hV hconj hy terminal,by simpa only [curve_terminal,mem_inter_iff] using hright⟩
  first_contact := ⟨curve_mem_source C hV hconj hy middle,by simpa only [curve_middle,mem_inter_iff] using hleft⟩
  last_contact := ⟨curve_mem_source C hV hconj hy middle,by simpa only [curve_middle,mem_inter_iff] using hleft⟩
  first_open := by
    intro r hr
    refine ⟨curve_mem_source C hV hconj hy r,?_⟩
    intro hmem
    have hb := curve_below C hy (show 0 < (r : ℝ) from hr.1) (show (r : ℝ) < 1/2 from hr.2)
    exact hb.ne (hT _ hmem)
  last_open := by
    intro r hr
    refine ⟨curve_mem_source C hV hconj hy r,?_⟩
    intro hmem
    have hb := curve_above C hy (show 1/2 < (r : ℝ) from hr.1) (show (r : ℝ) < 1 from hr.2)
    exact hb.ne' (hT _ hmem)
  first_lower := by
    refine ⟨1/2,by norm_num,?_⟩
    intro r hr0 hr1
    exact curve_below C hy (by change 1/2-1/2 < (r : ℝ) at hr0; linarith)
      (show (r : ℝ) < 1/2 from hr1)
  last_upper := by
    refine ⟨1/2,by norm_num,?_⟩
    intro r hr0 hr1
    exact curve_above C hy (show 1/2 < (r : ℝ) from hr0)
      (by change (r : ℝ) < 1/2+1/2 at hr1; linarith)

def family : Set Curve := range (fun y : Ioo (-A) 0 => curve C y.property)

theorem family_disjoint : ∀ γ ∈ family C, ∀ η ∈ family C, γ ≠ η →
    Disjoint (interiorTrace γ) (interiorTrace η) := by
  rintro γ ⟨y,rfl⟩ η ⟨v,rfl⟩ hne
  apply disjoint_left.mpr
  rintro z ⟨s,_,hs⟩ ⟨t,_,ht⟩
  have hf := congrArg SlitPotentialReflection.fold (hs.trans ht.symm)
  rw [fold_curve,fold_curve] at hf
  have he := C.injective (rectanglePoint_mem_band C y.property s)
    (rectanglePoint_mem_band C v.property t) hf
  have hi := congrArg Complex.im he
  simp only [rectanglePoint_im] at hi
  have hy : y = v := Subtype.ext hi
  subst v
  exact hne rfl

private def openParameter (t : Ioo (0 : ℝ) 1) : Parameter := ⟨t,⟨t.property.1.le,t.property.2.le⟩⟩

private theorem openParameter_continuous : Continuous openParameter := by
  unfold openParameter
  fun_prop

private theorem joint_curve_continuous :
    Continuous (fun q : Ioo (-A) 0 × Ioo (0 : ℝ) 1 => curve C q.1.property (openParameter q.2)) := by
  let P : Ioo (-A) 0 × Ioo (0 : ℝ) 1 → ℂ :=
    fun q => rectanglePoint B q.1 (openParameter q.2)
  have hP : Continuous P := by unfold P rectanglePoint openParameter; fun_prop
  have hGP : Continuous (fun q => C (P q)) := C.continuous.comp_continuous hP
    (fun q => rectanglePoint_mem_band C q.1.property (openParameter q.2))
  change Continuous (fun q => if (q.2 : ℝ) ≤ 1/2 then starRingEnd ℂ (C (P q)) else C (P q))
  apply continuous_if_le (continuous_subtype_val.comp continuous_snd) continuous_const
    (Complex.continuous_conj.comp hGP).continuousOn hGP.continuousOn
  intro q hq
  change (q.2 : ℝ) = 1/2 at hq
  have he : P q = (q.1 : ℂ)*Complex.I := by simp [P,rectanglePoint,openParameter,hq]
  apply Complex.ext <;> simp [he,C.left_real _ q.1.property]

/-- Every height is retained; joint continuity makes the support a
countable union of compact images, hence Borel. -/
theorem family_support_measurable : MeasurableSet (MarkedSlitTransport.support (family C)) := by
  letI : LocallyCompactSpace (Ioo (-A) 0) := isOpen_Ioo.locallyCompactSpace
  letI : LocallyCompactSpace (Ioo (0 : ℝ) 1) := isOpen_Ioo.locallyCompactSpace
  have he : MarkedSlitTransport.support (family C) =
      range (fun q : Ioo (-A) 0 × Ioo (0 : ℝ) 1 => curve C q.1.property (openParameter q.2)) := by
    ext z
    simp only [MarkedSlitTransport.support,mem_iUnion,mem_range]
    constructor
    · rintro ⟨γ,⟨y,rfl⟩,t,ht,rfl⟩
      exact ⟨(y,⟨t,ht⟩),rfl⟩
    · rintro ⟨⟨y,t⟩,rfl⟩
      exact ⟨curve C y.property,⟨y,rfl⟩,openParameter t,t.property,rfl⟩
  rw [he]
  obtain ⟨K,hK,hcov⟩ := isSigmaCompact_range (joint_curve_continuous C)
  rw [← hcov]
  exact MeasurableSet.iUnion (fun n => (hK n).measurableSet)

theorem family_parentWave (M : Marking) {V : Set ℂ}
    (hV : MapsTo C (closedHorizontalBand B A) V) (hconj : MapsTo (starRingEnd ℂ) V V)
    (hleft : ∀ y ∈ Ioo (-A) 0, (C ((y : ℂ)*Complex.I)).re < M.left)
    (hright : ∀ y ∈ Ioo (-A) 0, M.ends (C ((B : ℂ)+(y : ℂ)*Complex.I))) :
    ParentWave M V (family C) where
  borel := family_support_measurable C
  leaf := by
    rintro γ ⟨y,rfl⟩
    exact curve_parentLeaf C M hV hconj y.property (hleft y y.property) (hright y y.property)
  disjoint := family_disjoint C

theorem family_pairableWave (M : Marking) {V T J₀ J₁ : Set ℂ}
    (hV : MapsTo C (closedHorizontalBand B A) V) (hconj : MapsTo (starRingEnd ℂ) V V)
    (hT : ∀ z ∈ T, z.im = 0)
    (hleft : ∀ y ∈ Ioo (-A) 0, (C ((y : ℂ)*Complex.I)).re < M.left ∧ C ((y : ℂ)*Complex.I) ∈ T ∩ J₀)
    (hright : ∀ y ∈ Ioo (-A) 0, M.ends (C ((B : ℂ)+(y : ℂ)*Complex.I)) ∧ C ((B : ℂ)+(y : ℂ)*Complex.I) ∈ T ∩ J₁) :
    PairableWave M V V T J₀ J₁ (family C) where
  toParentWave := family_parentWave C M hV hconj (fun y hy => (hleft y hy).1)
    (fun y hy => (hright y hy).1)
  pair := by
    rintro γ ⟨y,rfl⟩
    exact ⟨middle,middle,curve_temporalPair C hV hconj hT y.property
      (hleft y y.property).2 (hright y y.property).2⟩

theorem trace_curve_subset_segments {y : ℝ} (hy : y ∈ Ioo (-A) 0) :
    trace (curve C hy) ⊆
      (fun x : ℝ => C ((x : ℂ)+(y : ℂ)*Complex.I)) '' Icc 0 B ∪
      (fun x : ℝ => starRingEnd ℂ (C ((x : ℂ)+(y : ℂ)*Complex.I))) '' Icc 0 B := by
  rintro z ⟨t,rfl⟩
  have hx := rectanglePoint_re_mem_Icc (y := y) C.width_pos t
  rw [rectanglePoint_re] at hx
  change rawCurve _ _ _ t ∈ _
  unfold rawCurve
  split_ifs
  · exact Or.inr ⟨_,hx,rfl⟩
  · exact Or.inl ⟨_,hx,rfl⟩

end
end SlitReflectedRectangles
