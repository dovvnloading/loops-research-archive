import SlitDiskMarking
import SlitCubicWaves

/-!
# Actual finite-disk parent Waves

The complete reflected inverse-horizontal cubic family is pulled back by
the explicit squared Cayley inverse.  The construction retains every
height, proves the physical bank and left-relative-class conditions, and
identifies its Borel support by the actual coordinate homeomorphism.
-/

namespace SlitDiskWaves

open Set Function MeasureTheory MarkedSlitTransport
open SlitCubicCalibration SlitCubicBoundary SlitCubicBoundaryRange
open SlitDiskMarking
open scoped Topology
noncomputable section

variable {R : ℝ} (hR : 0 < R) (M : Marking)
  (hleft : -R < M.left) (hright : M.right < R)
local notation "N" => transformedMarking hR M hleft hright

theorem plane_curve_mem_slit {y : ℝ} (hy : y ∈ Ioo (-height (N).left (N).first (N).second) 0)
    (t : Parameter) : SlitCubicWaves.curve (N).left_lt_first (N).first_lt_second hy t ∈
      SlitDiskCayley.slit := by
  by_cases ht0 : t = initial
  · subst t
    left
    rw [SlitCubicWaves.curve_initial]
    exact lt_trans (SlitCubicClosedChart.closedInverse_right_edge
      (N).left_lt_first (N).first_lt_second hy).2.2
      (transformedMarking_second_neg hR M hleft hright)
  by_cases ht1 : t = terminal
  · subst t
    left
    rw [SlitCubicWaves.curve_terminal]
    exact lt_trans (SlitCubicClosedChart.closedInverse_right_edge
      (N).left_lt_first (N).first_lt_second hy).2.2
      (transformedMarking_second_neg hR M hleft hright)
  have ht : t ∈ parameterInterior := by
    constructor
    · by_contra hn
      apply ht0
      apply Subtype.ext
      change (t:ℝ) = 0
      linarith [t.property.1]
    · by_contra hn
      apply ht1
      apply Subtype.ext
      change (t:ℝ) = 1
      linarith [t.property.2]
  rcases SlitCubicWaves.curve_interior_in_cutPlane
    (N).left_lt_first (N).first_lt_second hy ht with hi | hr
  · exact Or.inr hi
  · exact Or.inl (lt_trans hr (transformedMarking_left_neg hR M hleft hright))

/-- A physical leaf in the finite disk, given by the explicit Cayley inverse. -/
def curve {y : ℝ} (hy : y ∈ Ioo (-height (N).left (N).first (N).second) 0) : Curve :=
  ⟨fun t => SlitDiskCayley.inverse R
      (SlitCubicWaves.curve (N).left_lt_first (N).first_lt_second hy t),
    (SlitDiskCayley.inverse_differentiableOn R).continuousOn.comp_continuous
      (SlitCubicWaves.curve (N).left_lt_first (N).first_lt_second hy).continuous
      (plane_curve_mem_slit hR M hleft hright hy)⟩

@[simp] theorem curve_apply {y : ℝ} (hy : y ∈ Ioo (-height (N).left (N).first (N).second) 0)
    (t : Parameter) : curve hR M hleft hright hy t = SlitDiskCayley.inverse R
      (SlitCubicWaves.curve (N).left_lt_first (N).first_lt_second hy t) := rfl

theorem curve_mem_disk {y : ℝ} (hy : y ∈ Ioo (-height (N).left (N).first (N).second) 0)
    (t : Parameter) : curve hR M hleft hright hy t ∈ SlitDiskCayley.disk R :=
  SlitDiskCayley.inverse_mem_disk hR (plane_curve_mem_slit hR M hleft hright hy t)

theorem curve_mem_ball {y : ℝ} (hy : y ∈ Ioo (-height (N).left (N).first (N).second) 0)
    (t : Parameter) : curve hR M hleft hright hy t ∈ Metric.ball 0 R := by
  simpa only [Metric.mem_ball,dist_zero_right,SlitDiskCayley.disk,mem_setOf_eq] using curve_mem_disk hR M hleft hright hy t

@[simp] theorem map_curve_apply {y : ℝ} (hy : y ∈ Ioo (-height (N).left (N).first (N).second) 0)
    (t : Parameter) : SlitDiskCayley.map R (curve hR M hleft hright hy t) =
      SlitCubicWaves.curve (N).left_lt_first (N).first_lt_second hy t :=
  SlitDiskCayley.map_inverse hR (plane_curve_mem_slit hR M hleft hright hy t)

theorem curve_simple {y : ℝ} (hy : y ∈ Ioo (-height (N).left (N).first (N).second) 0) :
    Simple (curve hR M hleft hright hy) := by
  intro s hs t ht he
  apply SlitCubicWaves.curve_simple (N).left_lt_first (N).first_lt_second hy hs ht
  simpa only [map_curve_apply] using congrArg (SlitDiskCayley.map R) he

/-- The full finite-disk family, parametrized by every interior rectangle height. -/
def family : Set Curve :=
  range (fun y : Ioo (-height (N).left (N).first (N).second) 0 =>
    curve hR M hleft hright y.property)

theorem support_plane_subset_slit :
    support (SlitCubicWaves.family N) ⊆ SlitDiskCayley.slit := by
  rw [SlitCubicWaves.support_family]
  intro z hz
  rcases hz with hi | hr
  · exact Or.inr hi
  · exact Or.inl (lt_trans hr (transformedMarking_left_neg hR M hleft hright))

theorem support_family_eq_image :
    support (family hR M hleft hright) =
      SlitDiskCayley.inverse R '' support (SlitCubicWaves.family N) := by
  ext z
  constructor
  · simp only [MarkedSlitTransport.support,mem_iUnion]
    rintro ⟨γ,⟨y,rfl⟩,t,ht,rfl⟩
    refine ⟨SlitCubicWaves.curve (N).left_lt_first (N).first_lt_second y.property t,?_,rfl⟩
    simp only [mem_iUnion]
    exact ⟨SlitCubicWaves.curve (N).left_lt_first (N).first_lt_second y.property,
      ⟨y,rfl⟩,t,ht,rfl⟩
  · rintro ⟨w,hw,rfl⟩
    simp only [MarkedSlitTransport.support,mem_iUnion] at hw ⊢
    rcases hw with ⟨γ,⟨y,rfl⟩,t,ht,rfl⟩
    exact ⟨curve hR M hleft hright y.property,⟨y,rfl⟩,t,ht,rfl⟩

/-- The support is identified through the actual disk chart, with no measurable-family premise. -/
theorem support_family_eq_preimage :
    support (family hR M hleft hright) = SlitDiskCayley.disk R ∩
      SlitDiskCayley.map R ⁻¹' support (SlitCubicWaves.family N) := by
  rw [support_family_eq_image]
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    have hs := support_plane_subset_slit hR M hleft hright hw
    refine ⟨SlitDiskCayley.inverse_mem_disk hR hs,?_⟩
    simpa only [mem_preimage,SlitDiskCayley.map_inverse hR hs] using hw
  · rintro ⟨hz,hw⟩
    exact ⟨SlitDiskCayley.map R z,hw,SlitDiskCayley.inverse_map hR hz⟩

theorem support_family_isOpen : IsOpen (support (family hR M hleft hright)) := by
  rw [support_family_eq_preimage]
  apply (SlitDiskCayley.map_differentiableOn hR).continuousOn.isOpen_inter_preimage
    (SlitDiskCayley.disk_open R)
  rw [SlitCubicWaves.support_family]
  exact (isOpen_ne_fun Complex.continuous_im continuous_const).union
    (isOpen_lt Complex.continuous_re continuous_const)

theorem family_disjoint :
    ∀ γ ∈ family hR M hleft hright, ∀ η ∈ family hR M hleft hright, γ ≠ η →
      Disjoint (interiorTrace γ) (interiorTrace η) := by
  rintro γ ⟨y,rfl⟩ η ⟨v,rfl⟩ hne
  apply Set.disjoint_left.mpr
  rintro z ⟨s,_,hs⟩ ⟨t,_,ht⟩
  have he := congrArg (SlitDiskCayley.map R) (hs.trans ht.symm)
  rw [map_curve_apply,map_curve_apply] at he
  have he' := congrArg (fun w => tail (N).left (N).first (N).second (SlitPotentialReflection.fold w)) he
  rw [SlitCubicWaves.tail_fold_curve,SlitCubicWaves.tail_fold_curve] at he'
  have hy := congrArg Complex.im he'
  simp only [SlitCubicWaves.rectanglePoint_im] at hy
  have hyv : y = v := Subtype.ext hy
  subst v
  exact hne rfl

/-- The physical trace lies on the two actual disk inverse-horizontal segments. -/
theorem trace_curve_subset_segments {y : ℝ}
    (hy : y ∈ Ioo (-height (N).left (N).first (N).second) 0) :
    trace (curve hR M hleft hright hy) ⊆
      (fun x : ℝ => SlitDiskCayley.inverse R
        (SlitCubicClosedChart.closedInverse (N).left (N).first (N).second ((x:ℂ)+(y:ℂ)*Complex.I))) ''
          Icc 0 (period (N).left (N).first (N).second) ∪
      (fun x : ℝ => SlitDiskCayley.inverse R (starRingEnd ℂ
        (SlitCubicClosedChart.closedInverse (N).left (N).first (N).second ((x:ℂ)+(y:ℂ)*Complex.I)))) ''
          Icc 0 (period (N).left (N).first (N).second) := by
  rintro z ⟨t,rfl⟩
  have hs := SlitCubicWaves.trace_curve_subset_segments
    (N).left_lt_first (N).first_lt_second hy ⟨t,rfl⟩
  rcases hs with ⟨x,hx,he⟩ | ⟨x,hx,he⟩
  · exact Or.inl ⟨x,hx,congrArg (SlitDiskCayley.inverse R) he⟩
  · exact Or.inr ⟨x,hx,congrArg (SlitDiskCayley.inverse R) he⟩

theorem curve_leftReference {y : ℝ}
    (hy : y ∈ Ioo (-height (N).left (N).first (N).second) 0) :
    LeftReference M.left (curve hR M hleft hright hy) where
  simple := curve_simple hR M hleft hright hy
  below := fun t ht0 hth => SlitDiskCayley.inverse_im_neg hR
    (plane_curve_mem_slit hR M hleft hright hy t)
    (SlitCubicWaves.curve_below (N).left_lt_first (N).first_lt_second hy ht0 hth)
  crossing_re := by
    apply (SlitDiskCayley.inverse_re_lt_iff hR
      (plane_curve_mem_slit hR M hleft hright hy middle)
      (SlitCubicWaves.curve_leftReference (N).left_lt_first (N).first_lt_second hy).crossing_im
      (marking_left_mem_Ioo M hleft hright)).mpr
    exact (SlitCubicWaves.curve_leftReference (N).left_lt_first (N).first_lt_second hy).crossing_re
  crossing_im := SlitDiskCayley.inverse_real hR
    (plane_curve_mem_slit hR M hleft hright hy middle)
    (SlitCubicWaves.curve_leftReference (N).left_lt_first (N).first_lt_second hy).crossing_im
  above := fun t hth ht1 => SlitDiskCayley.inverse_im_pos hR
    (plane_curve_mem_slit hR M hleft hright hy t)
    (SlitCubicWaves.curve_above (N).left_lt_first (N).first_lt_second hy hth ht1)

theorem curve_interior_in_cutPlane {y : ℝ}
    (hy : y ∈ Ioo (-height (N).left (N).first (N).second) 0)
    {t : Parameter} (ht : t ∈ parameterInterior) :
    (curve hR M hleft hright hy t).im ≠ 0 ∨
      (curve hR M hleft hright hy t).re < M.left := by
  have href := curve_leftReference hR M hleft hright hy
  rcases lt_trichotomy (t:ℝ) (1/2) with h | h | h
  · exact Or.inl (href.below t ht.1 h).ne
  · have he : t = middle := Subtype.ext h
    subst t
    exact Or.inr href.crossing_re
  · exact Or.inl (href.above t h ht.2).ne'

theorem curve_avoids {y : ℝ} (hy : y ∈ Ioo (-height (N).left (N).first (N).second) 0)
    {t : Parameter} (ht : t ∈ parameterInterior) :
    curve hR M hleft hright hy t ∉ M.slit := by
  intro hz
  rcases curve_interior_in_cutPlane hR M hleft hright hy ht with hi | hr
  · exact hi hz.1
  · exact (not_lt_of_ge hz.2.1) hr

theorem curve_parentLeaf {y : ℝ} (hy : y ∈ Ioo (-height (N).left (N).first (N).second) 0) :
    ParentLeaf M (Metric.ball 0 R) (curve hR M hleft hright hy) where
  simple := curve_simple hR M hleft hright hy
  first_end := by
    have he := (SlitCubicWaves.curve_parentLeaf N hy).first_end
    have hs := plane_curve_mem_slit hR M hleft hright hy initial
    exact ⟨SlitDiskCayley.inverse_real hR hs he.1,
      (SlitDiskCayley.lt_inverse_re_iff hR hs he.1 (marking_first_mem_Ioo M hleft hright)).mpr he.2.1,
      (SlitDiskCayley.inverse_re_lt_iff hR hs he.1 (marking_second_mem_Ioo M hleft hright)).mpr he.2.2⟩
  last_end := by
    have he := (SlitCubicWaves.curve_parentLeaf N hy).last_end
    have hs := plane_curve_mem_slit hR M hleft hright hy terminal
    exact ⟨SlitDiskCayley.inverse_real hR hs he.1,
      (SlitDiskCayley.lt_inverse_re_iff hR hs he.1 (marking_first_mem_Ioo M hleft hright)).mpr he.2.1,
      (SlitDiskCayley.inverse_re_lt_iff hR hs he.1 (marking_second_mem_Ioo M hleft hright)).mpr he.2.2⟩
  lower := ⟨1/2,by norm_num,fun t ht0 hth =>
    (curve_leftReference hR M hleft hright hy).below t ht0 hth⟩
  upper := ⟨1/2,by norm_num,fun t hth ht1 =>
    (curve_leftReference hR M hleft hright hy).above t (by linarith) ht1⟩
  inside := fun t _ => curve_mem_ball hR M hleft hright hy t
  avoids := fun _ ht => curve_avoids hR M hleft hright hy ht
  left_class := by
    refine ⟨curve hR M hleft hright hy,curve_leftReference hR M hleft hright hy,?_⟩
    refine ⟨⟨fun p => curve hR M hleft hright hy p.2,
      (curve hR M hleft hright hy).continuous.comp continuous_snd⟩,
      fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl,?_⟩
    exact fun _ _ ht => curve_avoids hR M hleft hright hy ht

/-- A literal finite-disk parent Wave, with every extremal horizontal height retained. -/
theorem family_parentWave :
    ParentWave M (Metric.ball 0 R) (family hR M hleft hright) where
  borel := (support_family_isOpen hR M hleft hright).measurableSet
  leaf := by
    rintro γ ⟨y,rfl⟩
    exact curve_parentLeaf hR M hleft hright y.property
  disjoint := family_disjoint hR M hleft hright

/-- The entire closed horizontal band has its physical cubic preimage inside the Cayley slit. -/
theorem closedInverse_mem_slit {w : ℂ}
    (hw : w ∈ SlitCubicClosedChart.closedHorizontalBand
      (period (N).left (N).first (N).second) (height (N).left (N).first (N).second)) :
    SlitCubicClosedChart.closedInverse (N).left (N).first (N).second w ∈
      SlitDiskCayley.slit := by
  let z := SlitCubicClosedChart.closedInverse (N).left (N).first (N).second w
  have hz : z ∈ SlitCubicClosedChart.closedSource (N).left (N).first (N).second :=
    SlitCubicClosedChart.closedInverse_mem_source (N).left_lt_first (N).first_lt_second hw
  change z ∈ SlitDiskCayley.slit
  by_cases hi : z.im = 0
  · left
    have he : (z.re:ℂ) = z := by apply Complex.ext <;> simp [hi]
    have hr : (z.re:ℂ) ∈ SlitCubicClosedChart.closedSource (N).left (N).first (N).second := by
      rw [he]
      exact hz
    rcases SlitCubicClosedChart.real_closedSource_cases
      (N).left_lt_first (N).first_lt_second hr with ha | hbc
    · exact lt_trans ha (transformedMarking_left_neg hR M hleft hright)
    · exact lt_trans hbc.2 (transformedMarking_second_neg hR M hleft hright)
  · exact Or.inr hi

theorem inverse_closedInverse_continuousOn :
    ContinuousOn (fun w => SlitDiskCayley.inverse R
      (SlitCubicClosedChart.closedInverse (N).left (N).first (N).second w))
      (SlitCubicClosedChart.closedHorizontalBand
        (period (N).left (N).first (N).second) (height (N).left (N).first (N).second)) :=
  (SlitDiskCayley.inverse_differentiableOn R).continuousOn.comp
    (SlitCubicClosedChart.closedInverse_continuousOn (N).left_lt_first (N).first_lt_second)
    (fun _ hw => closedInverse_mem_slit hR M hleft hright hw)

/-- The lower segment is exactly the conjugate of the actual disk inverse-horizontal segment. -/
theorem trace_curve_subset_conjugate_segments {y : ℝ}
    (hy : y ∈ Ioo (-height (N).left (N).first (N).second) 0) :
    trace (curve hR M hleft hright hy) ⊆
      (fun x : ℝ => SlitDiskCayley.inverse R
        (SlitCubicClosedChart.closedInverse (N).left (N).first (N).second ((x:ℂ)+(y:ℂ)*Complex.I))) ''
          Icc 0 (period (N).left (N).first (N).second) ∪
      (fun x : ℝ => starRingEnd ℂ (SlitDiskCayley.inverse R
        (SlitCubicClosedChart.closedInverse (N).left (N).first (N).second ((x:ℂ)+(y:ℂ)*Complex.I)))) ''
          Icc 0 (period (N).left (N).first (N).second) := by
  intro z hz
  rcases trace_curve_subset_segments hR M hleft hright hy hz with hs | hs
  · exact Or.inl hs
  · rcases hs with ⟨x,hx,rfl⟩
    refine Or.inr ⟨x,hx,?_⟩
    symm
    apply SlitDiskCayley.inverse_conj hR
    apply closedInverse_mem_slit hR M hleft hright
    simpa only [SlitCubicClosedChart.closedHorizontalBand,mem_setOf_eq,
      Complex.add_re,Complex.ofReal_re,Complex.mul_I_re,Complex.ofReal_im,neg_zero,add_zero,
      Complex.add_im,Complex.mul_I_im,zero_add] using ⟨hx.1,hx.2,hy.1,hy.2⟩

end
end SlitDiskWaves
