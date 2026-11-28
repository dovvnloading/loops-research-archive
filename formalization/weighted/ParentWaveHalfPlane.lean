import SlitWaveFinite
import SlitWaveLimit
import ParentWaveLeftCrossing
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Folding a complete parent leaf at its left seam

The auxiliary condenser uses every continuous path in the closed upper
half-plane from the actual ending atom to the left exterior ray. Its
width is the same all-density Hausdorff-trace modulus used for the parent.
The factor one half comes from two disjoint portions of each literal
parent trace and a reflected admissible metric.
-/

namespace ParentWaveHalfPlane

open Set Function MeasureTheory Measure Metric
open MarkedSlitTransport SlitWaveModulus
open scoped ENNReal NNReal Topology

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- Reflection of the lower half-plane onto the upper half-plane. -/
def fold (z : ℂ) : ℂ := ⟨z.re, |z.im|⟩

@[simp] theorem fold_re (z : ℂ) : (fold z).re = z.re := rfl
@[simp] theorem fold_im (z : ℂ) : (fold z).im = |z.im| := rfl

theorem fold_of_nonneg {z : ℂ} (hz : 0 ≤ z.im) : fold z = z := by
  apply Complex.ext <;> simp [fold, abs_of_nonneg hz]

theorem fold_of_nonpos {z : ℂ} (hz : z.im ≤ 0) : fold z = Complex.conjLIE z := by
  apply Complex.ext <;> simp [fold, abs_of_nonpos hz]

theorem fold_lipschitz : LipschitzWith 1 fold := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  have h := abs_abs_sub_abs_le_abs_sub z.im w.im
  have hs : (|z.im|-|w.im|)^2 ≤ (z.im-w.im)^2 := by
    nlinarith [sq_abs (|z.im|-|w.im|), sq_abs (z.im-w.im),
      abs_nonneg (|z.im|-|w.im|), abs_nonneg (z.im-w.im)]
  have hnorm : ‖fold z-fold w‖^2 ≤ ‖z-w‖^2 := by
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im, fold_re, fold_im]
    nlinarith
  nlinarith [norm_nonneg (fold z-fold w), norm_nonneg (z-w)]

theorem fold_continuous : Continuous fold := fold_lipschitz.continuous

/-- Hausdorff length decreases under any one-Lipschitz map, also for
nonrectifiable traces and densities taking the value infinity. -/
theorem lineLength_image_le_of_lipschitz {f : ℂ → ℂ}
    (hf : LipschitzWith 1 f) {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ)
    (S : Set ℂ) :
    lineLength ρ (f '' S) ≤ lineLength (fun z => ρ (f z)) S := by
  have hm : (μH[1] : Measure ℂ).restrict (f '' S) ≤
      Measure.map f ((μH[1] : Measure ℂ).restrict S) := by
    apply Measure.le_iff.mpr
    intro T hT
    rw [Measure.restrict_apply hT, Measure.map_apply hf.continuous.measurable hT,
      Measure.restrict_apply (hf.continuous.measurable hT)]
    have he : f '' (f ⁻¹' T ∩ S) = T ∩ f '' S := by
      ext z
      constructor
      · rintro ⟨x,⟨hx,hS⟩,rfl⟩
        exact ⟨hx,⟨x,hS,rfl⟩⟩
      · rintro ⟨hz,x,hS,rfl⟩
        exact ⟨x,⟨hz,hS⟩,rfl⟩
    have h := hf.hausdorffMeasure_image_le (d := 1) (by norm_num)
      (f ⁻¹' T ∩ S)
    rw [he] at h
    simpa using h
  exact (lintegral_mono' hm le_rfl).trans_eq
    (lintegral_map hρ hf.continuous.measurable)

def prefixParameter (s t : Parameter) : Parameter :=
  ⟨(s : ℝ)*(t : ℝ), mul_nonneg s.2.1 t.2.1,
    (mul_le_mul_of_nonneg_left t.2.2 s.2.1).trans (by simpa using s.2.2)⟩

def suffixParameter (s t : Parameter) : Parameter :=
  ⟨1-(1-(s : ℝ))*(t : ℝ), by
    have h := mul_le_mul_of_nonneg_left t.2.2 (by linarith [s.2.2] : 0 ≤ 1-(s : ℝ))
    constructor
    · nlinarith [s.2.1]
    · nlinarith [mul_nonneg (by linarith [s.2.2] : 0 ≤ 1-(s : ℝ)) t.2.1]⟩

def leftPart (γ : Curve) (s : Parameter) : Curve :=
  ⟨fun t => γ (prefixParameter s t), γ.continuous.comp (by
    apply Continuous.subtype_mk
    exact continuous_const.mul continuous_subtype_val)⟩

def suffix (γ : Curve) (s : Parameter) : Curve :=
  ⟨fun t => γ (suffixParameter s t), γ.continuous.comp (by
    apply Continuous.subtype_mk
    exact continuous_const.sub (continuous_const.mul continuous_subtype_val))⟩

def folded (γ : Curve) : Curve := ⟨fun t => fold (γ t), fold_continuous.comp γ.continuous⟩

theorem trace_folded (γ : Curve) : trace (folded γ) = fold '' trace γ := by
  ext z
  simp [trace, folded]

theorem trace_prefix_subset (γ : Curve) (s : Parameter) : trace (leftPart γ s) ⊆ trace γ := by
  rintro z ⟨t,rfl⟩
  exact ⟨prefixParameter s t,rfl⟩

theorem trace_suffix_subset (γ : Curve) (s : Parameter) : trace (suffix γ s) ⊆ trace γ := by
  rintro z ⟨t,rfl⟩
  exact ⟨suffixParameter s t,rfl⟩

theorem prefixParameter_le (s t : Parameter) : prefixParameter s t ≤ s := by
  change (s : ℝ)*(t : ℝ) ≤ s
  simpa using mul_le_mul_of_nonneg_left t.2.2 s.2.1

theorem le_suffixParameter (s t : Parameter) : s ≤ suffixParameter s t := by
  change (s : ℝ) ≤ 1-(1-(s : ℝ))*(t : ℝ)
  have h := mul_le_mul_of_nonneg_left t.2.2 (by linarith [s.2.2] : 0 ≤ 1-(s : ℝ))
  nlinarith

private theorem parameterInterior_of_ne_endpoints {t : Parameter}
    (h0 : t ≠ initial) (h1 : t ≠ terminal) : t ∈ parameterInterior := by
  constructor
  · apply lt_of_le_of_ne t.2.1
    intro he
    apply h0
    exact Subtype.ext he.symm
  · apply lt_of_le_of_ne t.2.2
    intro he
    apply h1
    exact Subtype.ext he

/-- Simplicity is used on the actual trace, before either portion is folded. -/
theorem prefix_suffix_inter_subset {γ : Curve} (hγ : Simple γ) (s : Parameter) :
    trace (leftPart γ s) ∩ trace (suffix γ s) ⊆
      {γ initial, γ terminal, γ s} := by
  rintro z ⟨⟨t,ht⟩,⟨u,hu⟩⟩
  change γ (prefixParameter s t) = z at ht
  change γ (suffixParameter s u) = z at hu
  by_cases h0 : prefixParameter s t = initial
  · simp [← ht,h0]
  by_cases h1 : prefixParameter s t = terminal
  · simp [← ht,h1]
  by_cases k0 : suffixParameter s u = initial
  · simp [← hu,k0]
  by_cases k1 : suffixParameter s u = terminal
  · simp [← hu,k1]
  have he := hγ (parameterInterior_of_ne_endpoints h0 h1)
    (parameterInterior_of_ne_endpoints k0 k1) (ht.trans hu.symm)
  have hs : prefixParameter s t = s := le_antisymm (prefixParameter_le s t)
    (he ▸ le_suffixParameter s u)
  simp [← ht,hs]

theorem lineLength_prefix_add_suffix_le {γ : Curve} (hγ : Simple γ)
    (s : Parameter) (ρ : ℂ → ℝ≥0∞) :
    lineLength ρ (trace (leftPart γ s)) + lineLength ρ (trace (suffix γ s)) ≤
      lineLength ρ (trace γ) := by
  letI : NullSingletonClass (μH[1] : Measure ℂ) :=
    nullSingletonClass_hausdorff ℂ (by norm_num)
  let P := trace (leftPart γ s)
  let Q := trace (suffix γ s)
  have hQ : MeasurableSet Q := (trace_isCompact _).measurableSet
  have hnull : (μH[1] : Measure ℂ) (P ∩ Q) = 0 :=
    measure_mono_null (prefix_suffix_inter_subset hγ s)
      ((Set.finite_singleton (γ s)).insert (γ terminal) |>.insert (γ initial) |>.measure_zero _)
  have hinter : (∫⁻ z in P ∩ Q, ρ z ∂μH[1]) = 0 := by
    rw [Measure.restrict_eq_zero.mpr hnull, lintegral_zero_measure]
  have he := lintegral_inter_add_sdiff (μ := (μH[1] : Measure ℂ)) ρ P hQ
  rw [hinter,zero_add] at he
  change (∫⁻ z in P, ρ z ∂μH[1]) + (∫⁻ z in Q, ρ z ∂μH[1]) ≤ _
  rw [← he, ← lintegral_union hQ disjoint_sdiff_left]
  apply lintegral_mono_set
  exact union_subset ((sdiff_subset).trans (trace_prefix_subset γ s)) (trace_suffix_subset γ s)

/-- All continuous half-plane paths, including non-simple and
nonrectifiable ones, with the actual electrode and the actual left ray. -/
structure HalfPlaneLeaf (M : Marking) (γ : Curve) : Prop where
  first_end : M.ends (γ initial)
  last_im : (γ terminal).im = 0
  last_re : (γ terminal).re < M.left
  upper : ∀ t, 0 ≤ (γ t).im

def halfPlaneTraces (M : Marking) : Set (Set ℂ) :=
  trace '' {γ | HalfPlaneLeaf M γ}

def halfPlaneWidth (M : Marking) : ℝ≥0∞ := modulus (halfPlaneTraces M)

theorem folded_prefix_leaf {M : Marking} {D : Set ℂ} {γ : Curve}
    (hγ : ParentLeaf M D γ) {s : Parameter}
    (hs : (γ s).im = 0 ∧ (γ s).re < M.left) :
    HalfPlaneLeaf M (folded (leftPart γ s)) := by
  have h0 : prefixParameter s initial = initial := by
    apply Subtype.ext
    simp [prefixParameter,initial]
  have h1 : prefixParameter s terminal = s := by
    apply Subtype.ext
    simp [prefixParameter,terminal]
  constructor
  · change M.ends (fold (γ (prefixParameter s initial)))
    rw [h0,fold_of_nonneg (by rw [hγ.first_end.1])]
    exact hγ.first_end
  · simpa only [folded,leftPart,ContinuousMap.coe_mk,h1,fold_im,hs.1,abs_zero]
  · simpa only [folded,leftPart,ContinuousMap.coe_mk,h1,fold_re] using hs.2
  · intro t
    exact abs_nonneg _

theorem folded_suffix_leaf {M : Marking} {D : Set ℂ} {γ : Curve}
    (hγ : ParentLeaf M D γ) {s : Parameter}
    (hs : (γ s).im = 0 ∧ (γ s).re < M.left) :
    HalfPlaneLeaf M (folded (suffix γ s)) := by
  have h0 : suffixParameter s initial = terminal := by
    apply Subtype.ext
    simp [suffixParameter,initial,terminal]
  have h1 : suffixParameter s terminal = s := by
    apply Subtype.ext
    simp [suffixParameter,terminal]
  constructor
  · change M.ends (fold (γ (suffixParameter s initial)))
    rw [h0,fold_of_nonneg (by rw [hγ.last_end.1])]
    exact hγ.last_end
  · simpa only [folded,suffix,ContinuousMap.coe_mk,h1,fold_im,hs.1,abs_zero]
  · simpa only [folded,suffix,ContinuousMap.coe_mk,h1,fold_re] using hs.2
  · intro t
    exact abs_nonneg _

/-- A half-plane metric is folded onto both physical halves and divided
by two. Every selected parent leaf uses two unit-cost portions. -/
def parentDensity (ρ : ℂ → ℝ≥0∞) (z : ℂ) : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ * ρ (fold z)

theorem parentDensity_measurable {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    Measurable (parentDensity ρ) := measurable_const.mul (hρ.comp fold_continuous.measurable)

theorem parentDensity_length {M : Marking} {D : Set ℂ} {γ : Curve}
    (hγ : ParentLeaf M D γ) {s : Parameter}
    (hs : (γ s).im = 0 ∧ (γ s).re < M.left)
    {ρ : ℂ → ℝ≥0∞} (hρ : Admissible (halfPlaneTraces M) ρ) :
    1 ≤ lineLength (parentDensity ρ) (trace γ) := by
  have hP := hρ.2 _ ⟨_,folded_prefix_leaf hγ hs,rfl⟩
  have hQ := hρ.2 _ ⟨_,folded_suffix_leaf hγ hs,rfl⟩
  rw [trace_folded] at hP hQ
  have hP' := hP.trans (lineLength_image_le_of_lipschitz fold_lipschitz hρ.1 _)
  have hQ' := hQ.trans (lineLength_image_le_of_lipschitz fold_lipschitz hρ.1 _)
  have hsum : (2 : ℝ≥0∞) ≤ lineLength (fun z => ρ (fold z)) (trace γ) := by
    calc
      (2 : ℝ≥0∞) = 1+1 := by norm_num
      _ ≤ lineLength (fun z => ρ (fold z)) (trace (leftPart γ s)) +
          lineLength (fun z => ρ (fold z)) (trace (suffix γ s)) := add_le_add hP' hQ'
      _ ≤ _ := lineLength_prefix_add_suffix_le hγ.simple s _
  unfold parentDensity
  rw [lineLength_const_mul (ρ := fun z => ρ (fold z)) _
    (hρ.1.comp fold_continuous.measurable)]
  calc
    (1 : ℝ≥0∞) = (2 : ℝ≥0∞)⁻¹*2 :=
      (ENNReal.inv_mul_cancel (by norm_num) (by norm_num)).symm
    _ ≤ _ := mul_le_mul_left' hsum _

theorem fold_area_le {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    area (fun z => ρ (fold z)) ≤ area ρ+area ρ := by
  calc
    area (fun z => ρ (fold z)) ≤
        ∫⁻ z : ℂ, (ρ z)^2 + (ρ (Complex.conjLIE z))^2 := by
      apply lintegral_mono
      intro z
      change ρ (fold z)^2 ≤ ρ z^2+ρ (Complex.conjLIE z)^2
      by_cases hz : 0 ≤ z.im
      · rw [fold_of_nonneg hz]
        exact le_add_right le_rfl
      · rw [fold_of_nonpos (le_of_lt (lt_of_not_ge hz))]
        exact le_add_left le_rfl
    _ = area ρ+area ρ := by
      rw [lintegral_add_left (hρ.pow_const 2),
        Complex.conjLIE.measurePreserving.lintegral_comp (hρ.pow_const 2)]
      rfl

/-- Reflection doubles the candidate area, while the two source portions
permit division of its density by two. -/
theorem parentDensity_area_le {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    area (parentDensity ρ) ≤ (2 : ℝ≥0∞)⁻¹*area ρ := by
  calc
    area (parentDensity ρ) = (2 : ℝ≥0∞)⁻¹^2 * area (fun z => ρ (fold z)) := by
      unfold area parentDensity
      simp_rw [mul_pow]
      exact lintegral_const_mul _ ((hρ.comp fold_continuous.measurable).pow_const 2)
    _ ≤ (2 : ℝ≥0∞)⁻¹^2 * (area ρ+area ρ) := mul_le_mul_left' (fold_area_le hρ) _
    _ = (2 : ℝ≥0∞)⁻¹*area ρ := by
      rw [← two_mul, ← mul_assoc]
      congr 1
      rw [pow_two,mul_assoc,ENNReal.inv_mul_cancel (by norm_num) (by norm_num),mul_one]

/-- The complete all-density parent bound once its actual left crossing
has been supplied. No crossing simplicity is imposed after folding. -/
theorem parentWave_modulus_le_halfPlane_of_seam {M : Marking} {D : Set ℂ}
    {Γ : Set Curve} (hΓ : ParentWave M D Γ)
    (hseam : ∀ γ ∈ Γ, ∃ s : Parameter, (γ s).im = 0 ∧ (γ s).re < M.left) :
    modulus (traces Γ) ≤ (2 : ℝ≥0∞)⁻¹*halfPlaneWidth M := by
  unfold halfPlaneWidth modulus
  rw [ENNReal.mul_iInf_of_ne (by norm_num) (by norm_num)]
  apply le_iInf
  intro ρ
  rw [ENNReal.mul_iInf_of_ne (by norm_num) (by norm_num)]
  apply le_iInf
  intro hρ
  apply le_trans (b := area (parentDensity ρ))
  · change modulus (traces Γ) ≤ area (parentDensity ρ)
    apply modulus_le_area
    refine ⟨parentDensity_measurable hρ.1, ?_⟩
    rintro S ⟨γ,hγ,rfl⟩
    obtain ⟨s,hs⟩ := hseam γ hγ
    exact parentDensity_length (hΓ.leaf γ hγ) hs hρ
  · exact parentDensity_area_le hρ.1

/-- The complete actual parent family has a factor-one-half condenser
bound. Its left-seam condition is derived from its supplied relative
homotopy, rather than added to its definition. -/
theorem parentWave_modulus_le_halfPlane {M : Marking} {D : Set ℂ}
    {Γ : Set Curve} (hΓ : ParentWave M D Γ) :
    modulus (traces Γ) ≤ (2 : ℝ≥0∞)⁻¹*halfPlaneWidth M := by
  apply parentWave_modulus_le_halfPlane_of_seam hΓ
  intro γ hγ
  obtain ⟨s,_,hs⟩ := ParentWaveLeftCrossing.parentLeaf_exists_left_real (hΓ.leaf γ hγ)
  exact ⟨s,hs⟩

/-- Uniform control of the unrestricted canonical parent supremum over
all Borel laminations, in every ambient domain. -/
theorem parent_width_le_halfPlane (M : Marking) (D : Set ℂ) :
    SlitWaveLimit.width M D ≤ (2 : ℝ≥0∞)⁻¹*halfPlaneWidth M := by
  apply iSup₂_le
  intro Γ hΓ
  exact parentWave_modulus_le_halfPlane hΓ

def leftGap (M : Marking) : ℝ := M.first-M.left

theorem leftGap_pos (M : Marking) : 0 < leftGap M := sub_pos.mpr M.left_lt_first

def halfPlaneDensity (M : Marking) : ℂ → ℝ≥0∞ :=
  (closedBall (0 : ℂ) (SlitWaveFinite.endBound M+leftGap M)).indicator
    (fun _ => ENNReal.ofReal (1/leftGap M))

theorem halfPlaneDensity_measurable (M : Marking) : Measurable (halfPlaneDensity M) :=
  measurable_const.indicator isClosed_closedBall.measurableSet

theorem halfPlaneDensity_admissible (M : Marking) :
    Admissible (halfPlaneTraces M) (halfPlaneDensity M) := by
  refine ⟨halfPlaneDensity_measurable M,?_⟩
  rintro S ⟨γ,hγ,rfl⟩
  have hend : γ initial = ((γ initial).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using hγ.first_end.1
  have hbound : ‖γ initial‖ ≤ SlitWaveFinite.endBound M := by
    rw [hend,Complex.norm_real,Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> unfold SlitWaveFinite.endBound <;>
      linarith [hγ.first_end.2.1,hγ.first_end.2.2,
        neg_abs_le M.first,le_abs_self M.second,abs_nonneg M.first,abs_nonneg M.second]
  have hfar : leftGap M ≤ dist (γ initial) (γ terminal) := by
    have hd := (le_abs_self ((γ initial).re-(γ terminal).re)).trans
      (by simpa only [Complex.sub_re] using Complex.abs_re_le_norm (γ initial-γ terminal))
    rw [dist_eq_norm]
    unfold leftGap
    linarith [hγ.first_end.2.1,hγ.last_re]
  have hH := SlitWaveFinite.hausdorff_bounded_length (trace_isPreconnected γ)
    (show γ initial ∈ trace γ from ⟨initial,rfl⟩)
    (show γ terminal ∈ trace γ from ⟨terminal,rfl⟩) hbound hfar
  unfold lineLength halfPlaneDensity
  rw [lintegral_indicator_const isClosed_closedBall.measurableSet,
    Measure.restrict_apply isClosed_closedBall.measurableSet,inter_comm]
  calc
    (1 : ℝ≥0∞) = ENNReal.ofReal (1/leftGap M)*ENNReal.ofReal (leftGap M) := by
      rw [← ENNReal.ofReal_mul (one_div_pos.mpr (leftGap_pos M)).le]
      simp [(leftGap_pos M).ne']
    _ ≤ _ := mul_le_mul_left' hH _

theorem halfPlaneDensity_area_ne_top (M : Marking) : area (halfPlaneDensity M) ≠ ⊤ := by
  have heq : (fun z : ℂ => halfPlaneDensity M z ^ (2 : ℕ)) =
      (closedBall (0 : ℂ) (SlitWaveFinite.endBound M+leftGap M)).indicator
        (fun _ => ENNReal.ofReal (1/leftGap M)^2) := by
    funext z
    by_cases hz : z ∈ closedBall (0 : ℂ) (SlitWaveFinite.endBound M+leftGap M) <;>
      simp [halfPlaneDensity,hz]
  unfold area
  rw [heq,lintegral_indicator_const isClosed_closedBall.measurableSet]
  exact ENNReal.mul_ne_top (by simp) measure_closedBall_lt_top.ne

/-- The half-plane comparison is finite for every strictly ordered physical
marking. It has no unproved regularity or attainment premise. -/
theorem halfPlaneWidth_ne_top (M : Marking) : halfPlaneWidth M ≠ ⊤ :=
  ne_top_of_le_ne_top (halfPlaneDensity_area_ne_top M)
    (modulus_le_area (halfPlaneDensity_admissible M))

end
end ParentWaveHalfPlane
