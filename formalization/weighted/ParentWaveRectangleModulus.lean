import ParentWaveReflectionModulus
import CollarMetricEnergy

/-!
# The modulus of the literal horizontal rectangle foliation

The curves are their full Hausdorff-measured geometric traces. The
calculation applies to arbitrary measurable extended densities, using
the planar measure and the modulus in `SlitWaveModulus`.
-/

namespace ParentWaveRectangleModulus

open Set Function MeasureTheory Filter MarkedSlitTransport SlitWaveModulus
open CollarCapacityLower
open scoped ENNReal NNReal Topology

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- Horizontal translation of the real axis preserves distance. -/
theorem horizontal_isometry (y : ℝ) : Isometry (CollarCapacityLower.horizontal y) := by
  apply Isometry.of_dist_eq
  intro x z
  simp [CollarCapacityLower.horizontal,dist_eq_norm,← Complex.ofReal_sub]

/-- The literal weighted Hausdorff length on a horizontal trace is its
one-dimensional Lebesgue integral; no regularity of the density is needed. -/
theorem lineLength_horizontal (ρ : ℂ → ℝ≥0∞) (y : ℝ) (S : Set ℝ) :
    lineLength ρ (CollarCapacityLower.horizontal y '' S) = ∫⁻ x in S,ρ (CollarCapacityLower.horizontal y x) := by
  have he := (horizontal_isometry y).isClosedEmbedding.measurableEmbedding
  have hmap := (horizontal_isometry y).map_hausdorffMeasure
    (Or.inl (by norm_num : (0 : ℝ) ≤ 1))
  rw [hausdorffMeasure_real] at hmap
  have hsub : CollarCapacityLower.horizontal y '' S ⊆ range (CollarCapacityLower.horizontal y) := image_subset_range _ _
  unfold lineLength
  rw [← Measure.restrict_restrict_of_subset hsub,← hmap,he.restrict_map,
    preimage_image_eq S (horizontal_isometry y).injective,he.lintegral_map]

/-- The closed horizontal segment, with its original affine parameter. -/
def rectangleCurve (R y : ℝ) : Curve :=
  ⟨fun t => CollarCapacityLower.horizontal y (R * (t : ℝ)),
    (horizontal_lipschitz y).continuous.comp (by fun_prop)⟩

@[simp] theorem rectangleCurve_initial (R y : ℝ) :
    rectangleCurve R y initial = CollarCapacityLower.horizontal y 0 := by
  simp [rectangleCurve,initial]

@[simp] theorem rectangleCurve_terminal (R y : ℝ) :
    rectangleCurve R y terminal = CollarCapacityLower.horizontal y R := by
  simp [rectangleCurve,terminal]

/-- The geometric trace is the complete horizontal segment. -/
theorem rectangleCurve_trace {R : ℝ} (hR : 0 < R) (y : ℝ) :
    trace (rectangleCurve R y) = CollarCapacityLower.horizontal y '' Icc 0 R := by
  ext z
  constructor
  · rintro ⟨t,rfl⟩
    exact ⟨R * (t : ℝ),⟨mul_nonneg hR.le t.2.1,
      by nlinarith [t.2.2]⟩,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    refine ⟨⟨x/R,⟨div_nonneg hx.1 hR.le,(div_le_one hR).mpr hx.2⟩⟩,?_⟩
    change CollarCapacityLower.horizontal y (R*(x/R)) = CollarCapacityLower.horizontal y x
    congr 1
    field_simp

/-- Distinct points of the parameter interval stay distinct on a segment. -/
theorem rectangleCurve_injective {R : ℝ} (hR : 0 < R) (y : ℝ) :
    Injective (rectangleCurve R y) := by
  intro s t h
  apply Subtype.ext
  have he := (horizontal_isometry y).injective h
  exact mul_left_cancel₀ hR.ne' he

/-- The family contains one full segment at every interior height. -/
def rectangleFamily (R a b : ℝ) : Set Curve := rectangleCurve R '' Ioo a b

/-- The support includes the two vertical sides and excludes the two
horizontal sides, precisely as the family of full traces does. -/
def rectangle (R a b : ℝ) : Set ℂ :=
  {z | z.re ∈ Icc 0 R ∧ z.im ∈ Ioo a b}

theorem rectangle_measurable (R a b : ℝ) : MeasurableSet (rectangle R a b) :=
  (Complex.measurable_re measurableSet_Icc).inter
    (Complex.measurable_im measurableSet_Ioo)

/-- Every point of every segment belongs to the exact rectangle support. -/
theorem rectangleCurve_mem {R a b y : ℝ} (hR : 0 < R) (hy : y ∈ Ioo a b)
    (t : Parameter) : rectangleCurve R y t ∈ rectangle R a b := by
  have hx : R*(t:ℝ) ∈ Icc 0 R :=
    ⟨mul_nonneg hR.le t.2.1,by nlinarith [t.2.2]⟩
  simpa [rectangle,rectangleCurve,CollarCapacityLower.horizontal] using And.intro hx hy

/-- The union of full traces is exactly the rectangle support. -/
theorem rectangleFamily_support {R : ℝ} (hR : 0 < R) (a b : ℝ) :
    ParentWaveReflection.upperSupport (rectangleFamily R a b) = rectangle R a b := by
  ext z
  simp only [ParentWaveReflection.upperSupport,mem_iUnion]
  constructor
  · rintro ⟨γ,⟨y,hy,rfl⟩,hz⟩
    rw [rectangleCurve_trace hR] at hz
    rcases hz with ⟨x,hx,rfl⟩
    simpa [rectangle,CollarCapacityLower.horizontal] using And.intro hx hy
  · intro hz
    refine ⟨rectangleCurve R z.im,⟨z.im,hz.2,rfl⟩,?_⟩
    rw [rectangleCurve_trace hR]
    refine ⟨z.re,hz.1,?_⟩
    apply Complex.ext <;> simp [CollarCapacityLower.horizontal]

/-- The area uses the literal planar Lebesgue measure. -/
theorem rectangle_volume (R a b : ℝ) :
    volume (rectangle R a b) = ENNReal.ofReal (b-a) * ENNReal.ofReal R := by
  have hpre : (fun p : ℝ × ℝ => CollarCapacityLower.horizontal p.1 p.2) ⁻¹' rectangle R a b =
      Ioo a b ×ˢ Icc 0 R := by
    ext p
    simp [rectangle,CollarCapacityLower.horizontal,and_comm]
  have he := horizontal_measurePreserving.measure_preimage
    (rectangle_measurable R a b).nullMeasurableSet
  rw [hpre] at he
  rw [← he,Measure.prod_prod]
  simp

/-- Every admissible density for the actual horizontal traces has the
sharp rectangle energy lower bound. -/
theorem rectangle_admissible_area_lower {R a b : ℝ} (hR : 0 < R)
    {ρ : ℂ → ℝ≥0∞} (hρ : Admissible (traces (rectangleFamily R a b)) ρ) :
    ENNReal.ofReal ((b-a)/R) ≤ area ρ := by
  have hslices : ∀ y ∈ Ioo a b,
      1 ≤ ∫⁻ x in Icc 0 R,ρ (CollarCapacityLower.horizontal y x) := by
    intro y hy
    have h := hρ.2 (trace (rectangleCurve R y))
      ⟨rectangleCurve R y,⟨y,hy,rfl⟩,rfl⟩
    simpa only [rectangleCurve_trace hR,lineLength_horizontal] using h
  have hslice : ∀ᵐ y : ℝ ∂volume.restrict (Ioo a b),
      ENNReal.ofReal (1/R) ≤ ∫⁻ x in Icc 0 R,(ρ (CollarCapacityLower.horizontal y x))^2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact CollarMetricEnergy.horizontal_square_integral_lower hρ.1 hR y (hslices y hy)
  have hconst : (∫⁻ _y in Ioo a b,ENNReal.ofReal (1/R)) =
      ENNReal.ofReal ((b-a)/R) := by
    rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioo,
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1/R)]
    congr 1
    ring
  have hmeas : Measurable (fun z : ℂ => (ρ z)^2) := hρ.1.pow_const 2
  calc
    ENNReal.ofReal ((b-a)/R) = ∫⁻ _y in Ioo a b,ENNReal.ofReal (1/R) := hconst.symm
    _ ≤ ∫⁻ y in Ioo a b,∫⁻ x in Icc 0 R,(ρ (CollarCapacityLower.horizontal y x))^2 :=
      lintegral_mono_ae hslice
    _ ≤ ∫⁻ y in Ioo a b,∫⁻ x : ℝ,(ρ (CollarCapacityLower.horizontal y x))^2 :=
      lintegral_mono (fun _ => setLIntegral_le_lintegral _ _)
    _ ≤ ∫⁻ y : ℝ,∫⁻ x : ℝ,(ρ (CollarCapacityLower.horizontal y x))^2 := setLIntegral_le_lintegral _ _
    _ = ∫⁻ p : ℝ × ℝ,(ρ (CollarCapacityLower.horizontal p.1 p.2))^2
        ∂((volume : Measure ℝ).prod volume) :=
      (lintegral_prod _ (hmeas.comp horizontal_measurePreserving.measurable).aemeasurable).symm
    _ = area ρ := horizontal_measurePreserving.lintegral_comp hmeas

/-- The constant extremal density on the literal rectangle support. -/
def rectangleDensity (R a b : ℝ) : ℂ → ℝ≥0∞ :=
  (rectangle R a b).indicator (fun _ => (ENNReal.ofReal R)⁻¹)

theorem rectangleDensity_measurable (R a b : ℝ) :
    Measurable (rectangleDensity R a b) :=
  measurable_const.indicator (rectangle_measurable R a b)

theorem rectangleDensity_length {R a b y : ℝ} (hR : 0 < R) (hy : y ∈ Ioo a b) :
    lineLength (rectangleDensity R a b) (trace (rectangleCurve R y)) = 1 := by
  rw [rectangleCurve_trace hR,lineLength_horizontal]
  have heq : ∀ x ∈ Icc 0 R,rectangleDensity R a b (CollarCapacityLower.horizontal y x) =
      (ENNReal.ofReal R)⁻¹ := by
    intro x hx
    have hz : CollarCapacityLower.horizontal y x ∈ rectangle R a b := by
      simpa [rectangle,CollarCapacityLower.horizontal] using And.intro hx hy
    exact indicator_of_mem hz _
  rw [setLIntegral_congr_fun measurableSet_Icc heq,lintegral_const,
    Measure.restrict_apply_univ,Real.volume_Icc,sub_zero]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hR).ne' ENNReal.ofReal_ne_top

theorem rectangleDensity_admissible {R a b : ℝ} (hR : 0 < R) :
    Admissible (traces (rectangleFamily R a b)) (rectangleDensity R a b) := by
  refine ⟨rectangleDensity_measurable R a b,?_⟩
  rintro S ⟨γ,⟨y,hy,rfl⟩,rfl⟩
  exact (rectangleDensity_length hR hy).ge

theorem rectangleDensity_area {R a b : ℝ} (hR : 0 < R) :
    area (rectangleDensity R a b) = ENNReal.ofReal ((b-a)/R) := by
  have heq : (fun z => (rectangleDensity R a b z)^2) =
      (rectangle R a b).indicator (fun _ => ((ENNReal.ofReal R)⁻¹)^2) := by
    funext z
    by_cases hz : z ∈ rectangle R a b <;> simp [rectangleDensity,hz]
  unfold area
  rw [heq,lintegral_indicator_const (rectangle_measurable R a b),rectangle_volume]
  rw [ENNReal.ofReal_div_of_pos hR,div_eq_mul_inv]
  have hfin : ENNReal.ofReal R ≠ ⊤ := ENNReal.ofReal_ne_top
  have hzero : ENNReal.ofReal R ≠ 0 := (ENNReal.ofReal_pos.mpr hR).ne'
  calc
    ((ENNReal.ofReal R)⁻¹)^2 * (ENNReal.ofReal (b-a) * ENNReal.ofReal R) =
        ENNReal.ofReal (b-a) * (ENNReal.ofReal R)⁻¹ *
          ((ENNReal.ofReal R)⁻¹ * ENNReal.ofReal R) := by ring
    _ = ENNReal.ofReal (b-a) * (ENNReal.ofReal R)⁻¹ := by
      rw [ENNReal.inv_mul_cancel hzero hfin,mul_one]

/-- Exact modulus of the full horizontal foliation, in the canonical
Hausdorff-trace definition used by the slit-wave supremum. -/
theorem rectangle_modulus {R a b : ℝ} (hR : 0 < R) :
    modulus (traces (rectangleFamily R a b)) = ENNReal.ofReal ((b-a)/R) := by
  apply le_antisymm
  · exact (modulus_le_area (rectangleDensity_admissible hR)).trans_eq
      (rectangleDensity_area hR)
  · unfold modulus
    exact le_iInf₂ (fun ρ hρ => rectangle_admissible_area_lower hR hρ)

/-- The closed target rectangle also allows crossings to touch either
horizontal side. Such contact is permitted by the all-path condenser. -/
def closedRectangle (R a b : ℝ) : Set ℂ :=
  {z | z.re ∈ Icc 0 R ∧ z.im ∈ Icc a b}

theorem closedRectangle_measurable (R a b : ℝ) :
    MeasurableSet (closedRectangle R a b) :=
  (Complex.measurable_re measurableSet_Icc).inter
    (Complex.measurable_im measurableSet_Icc)

theorem closedRectangle_volume (R a b : ℝ) :
    volume (closedRectangle R a b) = ENNReal.ofReal (b-a) * ENNReal.ofReal R := by
  have hpre : (fun p : ℝ × ℝ => CollarCapacityLower.horizontal p.1 p.2) ⁻¹'
      closedRectangle R a b = Icc a b ×ˢ Icc 0 R := by
    ext p
    simp only [mem_preimage,mem_prod]
    simp [closedRectangle,CollarCapacityLower.horizontal,and_comm]
  have he := horizontal_measurePreserving.measure_preimage
    (closedRectangle_measurable R a b).nullMeasurableSet
  rw [hpre] at he
  rw [← he,Measure.prod_prod]
  simp

/-- A crossing is an arbitrary continuous curve between the vertical
sides. Neither simplicity nor finite length is required. -/
structure RectangleCrossing (R a b : ℝ) (γ : Curve) : Prop where
  inside : ∀ t,γ t ∈ closedRectangle R a b
  first_re : (γ initial).re = 0
  last_re : (γ terminal).re = R

/-- Every intermediate real coordinate occurs on the geometric trace. -/
theorem real_interval_subset_trace {R a b : ℝ} {γ : Curve}
    (hγ : RectangleCrossing R a b γ) : Icc 0 R ⊆ Complex.re '' trace γ := by
  have hconn := (trace_isPreconnected γ).image Complex.re Complex.continuous_re.continuousOn
  apply hconn.Icc_subset
  · exact ⟨γ initial,⟨initial,rfl⟩,hγ.first_re⟩
  · exact ⟨γ terminal,⟨terminal,rfl⟩,hγ.last_re⟩

/-- The actual Hausdorff length of every continuous crossing dominates
the distance between the vertical sides. -/
theorem rectangleCrossing_length_lower {R a b : ℝ} {γ : Curve}
    (hγ : RectangleCrossing R a b γ) : ENNReal.ofReal R ≤ μH[1] (trace γ) := by
  have hre : LipschitzWith 1 Complex.re := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    simpa [dist_eq_norm,← Complex.sub_re] using Complex.abs_re_le_norm (z-w)
  calc
    ENNReal.ofReal R = (μH[1] : Measure ℝ) (Icc 0 R) := by
      rw [hausdorffMeasure_real,Real.volume_Icc,sub_zero]
    _ ≤ μH[1] (Complex.re '' trace γ) := measure_mono (real_interval_subset_trace hγ)
    _ ≤ μH[1] (trace γ) := by
      simpa using hre.hausdorffMeasure_image_le (by norm_num : (0 : ℝ) ≤ 1) (trace γ)

/-- A constant density on the closed rectangle is admissible even for
continuous crossings of infinite length or crossings along the boundary. -/
def crossingDensity (R a b : ℝ) : ℂ → ℝ≥0∞ :=
  (closedRectangle R a b).indicator (fun _ => (ENNReal.ofReal R)⁻¹)

theorem crossingDensity_admissible {R a b : ℝ} (hR : 0 < R) :
    Admissible (traces {γ | RectangleCrossing R a b γ}) (crossingDensity R a b) := by
  refine ⟨measurable_const.indicator (closedRectangle_measurable R a b),?_⟩
  rintro S ⟨γ,hγ,rfl⟩
  have heq : ∀ z ∈ trace γ,crossingDensity R a b z = (ENNReal.ofReal R)⁻¹ := by
    rintro z ⟨t,rfl⟩
    exact indicator_of_mem (hγ.inside t) _
  unfold lineLength
  rw [setLIntegral_congr_fun (trace_isCompact γ).measurableSet heq,
    lintegral_const,Measure.restrict_apply_univ]
  calc
    1 = (ENNReal.ofReal R)⁻¹ * ENNReal.ofReal R :=
      (ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hR).ne' ENNReal.ofReal_ne_top).symm
    _ ≤ (ENNReal.ofReal R)⁻¹ * μH[1] (trace γ) :=
      mul_le_mul_right (rectangleCrossing_length_lower hγ) _

theorem crossingDensity_area {R a b : ℝ} (hR : 0 < R) :
    area (crossingDensity R a b) = ENNReal.ofReal ((b-a)/R) := by
  have heq : (fun z => (crossingDensity R a b z)^2) =
      (closedRectangle R a b).indicator (fun _ => ((ENNReal.ofReal R)⁻¹)^2) := by
    funext z
    by_cases hz : z ∈ closedRectangle R a b <;> simp [crossingDensity,hz]
  unfold area
  rw [heq,lintegral_indicator_const (closedRectangle_measurable R a b),closedRectangle_volume]
  rw [ENNReal.ofReal_div_of_pos hR,div_eq_mul_inv]
  have hfin : ENNReal.ofReal R ≠ ⊤ := ENNReal.ofReal_ne_top
  have hzero : ENNReal.ofReal R ≠ 0 := (ENNReal.ofReal_pos.mpr hR).ne'
  calc
    ((ENNReal.ofReal R)⁻¹)^2 * (ENNReal.ofReal (b-a) * ENNReal.ofReal R) =
        ENNReal.ofReal (b-a) * (ENNReal.ofReal R)⁻¹ *
          ((ENNReal.ofReal R)⁻¹ * ENNReal.ofReal R) := by ring
    _ = ENNReal.ofReal (b-a) * (ENNReal.ofReal R)⁻¹ := by
      rw [ENNReal.inv_mul_cancel hzero hfin,mul_one]

/-- The full horizontal foliation is contained in the all-continuous
crossing family with exactly the same full traces. -/
theorem rectangleFamily_subset_crossings {R a b : ℝ} (hR : 0 < R) :
    rectangleFamily R a b ⊆ {γ | RectangleCrossing R a b γ} := by
  rintro γ ⟨y,hy,rfl⟩
  refine ⟨?_,?_,?_⟩
  · intro t
    have ht := rectangleCurve_mem hR hy t
    exact ⟨ht.1,⟨ht.2.1.le,ht.2.2.le⟩⟩
  · simp [rectangleCurve,initial,CollarCapacityLower.horizontal]
  · simp [rectangleCurve,terminal,CollarCapacityLower.horizontal]

/-- The foliation realizes the exact modulus of every continuous
rectangle crossing, including nonsimple and nonrectifiable competitors. -/
theorem rectangleCrossings_modulus {R a b : ℝ} (hR : 0 < R) :
    modulus (traces {γ | RectangleCrossing R a b γ}) = ENNReal.ofReal ((b-a)/R) := by
  apply le_antisymm
  · exact (modulus_le_area (crossingDensity_admissible hR)).trans_eq (crossingDensity_area hR)
  · rw [← rectangle_modulus hR]
    exact modulus_mono (image_mono (rectangleFamily_subset_crossings hR))

end
end ParentWaveRectangleModulus
