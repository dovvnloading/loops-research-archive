import ParentWaveHalfPlane
import ParentWaveReflection

/-!
# Exact metric cost of reflecting upper crossing families

Reflection and concatenation produce the literal parent laminations of
`ParentWaveReflection`. The estimates here use their Hausdorff-trace
modulus over every planar density, including extended-valued densities.
-/

namespace ParentWaveReflectionModulus

open Set Function MeasureTheory Measure Metric
open MarkedSlitTransport SlitWaveModulus ParentWaveReflection
open scoped ENNReal NNReal Topology

noncomputable section

set_option backward.isDefEq.respectTransparency false

def upper : Set ℂ := {z | 0 < z.im}

theorem upper_measurable : MeasurableSet upper :=
  (isOpen_lt continuous_const Complex.continuous_im).measurableSet

theorem upper_conj_disjoint : Disjoint upper (Complex.conjLIE '' upper) := by
  apply Set.disjoint_left.mpr
  rintro z hz ⟨w,hw,rfl⟩
  change (0 : ℝ) < w.im at hw
  change (0 : ℝ) < (Complex.conjLIE w).im at hz
  simp only [Complex.conjLIE_apply,Complex.conj_im] at hz
  linarith

/-- The two real boundary endpoints have zero one-dimensional measure;
there is no regularity restriction on the interior upper arc. -/
theorem UpperLeaf.trace_outside_upper_null {M : Marking} {γ : Curve}
    (hγ : UpperLeaf M γ) : (μH[1] : Measure ℂ) (trace γ \ upper) = 0 := by
  letI : NullSingletonClass (μH[1] : Measure ℂ) :=
    nullSingletonClass_hausdorff ℂ (by norm_num)
  apply measure_mono_null (t := {γ initial,γ terminal})
  · rintro z ⟨⟨t,rfl⟩,ht⟩
    by_cases h0 : t = initial
    · simp [h0]
    by_cases h1 : t = terminal
    · simp [h1]
    have hi : t ∈ parameterInterior := by
      constructor
      · exact lt_of_le_of_ne t.2.1 (fun he => h0 (Subtype.ext he.symm))
      · exact lt_of_le_of_ne t.2.2 (fun he => h1 (Subtype.ext he))
    exact False.elim (ht (hγ.upper t hi))
  · exact ((Set.finite_singleton (γ terminal)).insert (γ initial)).measure_zero _

theorem lineLength_conj {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) (S : Set ℂ) :
    lineLength ρ (Complex.conjLIE '' S) = lineLength (fun z => ρ (Complex.conjLIE z)) S := by
  apply le_antisymm
  · exact ParentWaveHalfPlane.lineLength_image_le_of_lipschitz
      Complex.conjLIE.isometry.lipschitz hρ S
  · have h := ParentWaveHalfPlane.lineLength_image_le_of_lipschitz
      Complex.conjLIE.isometry.lipschitz (hρ.comp Complex.conjLIE.continuous.measurable)
      (Complex.conjLIE '' S)
    simpa [Set.image_image,Complex.conjLIE_apply,Function.comp_def] using h

def upperDensity (ρ : ℂ → ℝ≥0∞) : ℂ → ℝ≥0∞ :=
  upper.indicator (fun z => ρ z+ρ (Complex.conjLIE z))

theorem upperDensity_measurable {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    Measurable (upperDensity ρ) :=
  (hρ.add (hρ.comp Complex.conjLIE.continuous.measurable)).indicator upper_measurable

theorem upperDensity_length {M : Marking} {γ : Curve} (hγ : UpperLeaf M γ)
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    lineLength (upperDensity ρ) (trace γ) =
      lineLength ρ (trace γ)+lineLength ρ (Complex.conjLIE '' trace γ) := by
  have hzero : (∫⁻ z in trace γ \ upper, (ρ z+ρ (Complex.conjLIE z)) ∂μH[1]) = 0 := by
    rw [Measure.restrict_eq_zero.mpr (UpperLeaf.trace_outside_upper_null hγ),
      lintegral_zero_measure]
  have he := lintegral_inter_add_sdiff (μ := (μH[1] : Measure ℂ))
    (fun z => ρ z+ρ (Complex.conjLIE z)) (trace γ) upper_measurable
  rw [hzero,add_zero] at he
  unfold lineLength upperDensity
  rw [lintegral_indicator upper_measurable,Measure.restrict_restrict upper_measurable,
    inter_comm,he,lintegral_add_left hρ]
  exact congrArg (fun x => (∫⁻ z in trace γ,ρ z ∂μH[1])+x) (lineLength_conj hρ _).symm

private theorem ennreal_add_sq_le (a b : ℝ≥0∞) :
    (a+b)^2 ≤ 2*(a^2+b^2) := by
  by_cases ha : a = ⊤
  · simp [ha]
  by_cases hb : b = ⊤
  · simp [hb]
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  exact_mod_cast (add_sq_le (a := a) (b := b))

theorem upperDensity_area_le {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    area (upperDensity ρ) ≤ 2*area ρ := by
  have heq : (fun z => upperDensity ρ z ^ (2 : ℕ)) =
      upper.indicator (fun z => (ρ z+ρ (Complex.conjLIE z))^2) := by
    funext z
    by_cases hz : z ∈ upper <;> simp [upperDensity,hz]
  have hconj := Complex.conjLIE.measurePreserving.setLIntegral_comp_emb
    Complex.conjLIE.toHomeomorph.measurableEmbedding (fun z => ρ z^2) upper
  have hUconj : MeasurableSet (Complex.conjLIE '' upper) :=
    (Complex.conjLIE.toHomeomorph.measurableEmbedding.measurableSet_image).mpr upper_measurable
  calc
    area (upperDensity ρ) = ∫⁻ z in upper, (ρ z+ρ (Complex.conjLIE z))^2 := by
      rw [area,heq,lintegral_indicator upper_measurable]
    _ ≤ ∫⁻ z in upper, 2*(ρ z^2+ρ (Complex.conjLIE z)^2) := by
      apply lintegral_mono
      intro z
      exact ennreal_add_sq_le _ _
    _ = 2*((∫⁻ z in upper, ρ z^2)+(∫⁻ z in Complex.conjLIE '' upper, ρ z^2)) := by
      rw [lintegral_const_mul (f := fun z => ρ z^2+ρ (Complex.conjLIE z)^2) _ ((hρ.pow_const 2).add
        ((hρ.comp Complex.conjLIE.continuous.measurable).pow_const 2)),
        lintegral_add_left (hρ.pow_const 2),hconj]
    _ ≤ 2*area ρ := by
      rw [← lintegral_union hUconj upper_conj_disjoint]
      simpa [area] using mul_le_mul_left'
        (lintegral_mono_set (μ := (volume : Measure ℂ))
          (subset_univ (upper ∪ Complex.conjLIE '' upper)) (f := fun z => ρ z^2)) 2

/-- A metric for the complete reflected parent Wave gives an upper
crossing metric with at most twice its area. -/
theorem upperDensity_admissible {M : Marking} {Γ : Set Curve} (hΓ : UpperWave M Γ)
    {ρ : ℂ → ℝ≥0∞} (hρ : Admissible (traces (reflectedFamily hΓ)) ρ) :
    Admissible (traces Γ) (upperDensity ρ) := by
  refine ⟨upperDensity_measurable hρ.1,?_⟩
  rintro S ⟨γ,hγ,rfl⟩
  have hparent := hρ.2 _
    ⟨reflectedCurve γ (hΓ.leaf γ hγ),⟨γ,hγ,rfl⟩,rfl⟩
  rw [upperDensity_length (hΓ.leaf γ hγ) hρ.1]
  have hle : lineLength ρ (trace (reflectedCurve γ (hΓ.leaf γ hγ))) ≤
      lineLength ρ (trace γ)+lineLength ρ (Complex.conjLIE '' trace γ) := by
    rw [reflectedCurve_trace]
    exact (lintegral_union_le ρ _ _).trans_eq (add_comm _ _)
  exact hparent.trans hle

/-- No optimizer is postulated: the inequality holds for each full
upper Wave and its constructed, admissible reflected parent Wave. -/
theorem upper_modulus_le_twice_reflected {M : Marking} {Γ : Set Curve}
    (hΓ : UpperWave M Γ) :
    modulus (traces Γ) ≤ 2*modulus (traces (reflectedFamily hΓ)) := by
  unfold modulus
  rw [ENNReal.mul_iInf_of_ne (by norm_num) (by norm_num)]
  apply le_iInf
  intro ρ
  rw [ENNReal.mul_iInf_of_ne (by norm_num) (by norm_num)]
  apply le_iInf
  intro hρ
  change modulus (traces Γ) ≤ 2*area ρ
  exact (modulus_le_area (upperDensity_admissible hΓ hρ)).trans
    (upperDensity_area_le hρ.1)

theorem half_upper_modulus_le_parent_width {M : Marking} {Γ : Set Curve}
    (hΓ : UpperWave M Γ) :
    (2 : ℝ≥0∞)⁻¹*modulus (traces Γ) ≤ SlitWaveLimit.width M univ := by
  calc
    (2 : ℝ≥0∞)⁻¹*modulus (traces Γ) ≤
        (2 : ℝ≥0∞)⁻¹*(2*modulus (traces (reflectedFamily hΓ))) :=
      mul_le_mul_left' (upper_modulus_le_twice_reflected hΓ) _
    _ = modulus (traces (reflectedFamily hΓ)) := by
      rw [← mul_assoc,ENNReal.inv_mul_cancel (by norm_num) (by norm_num),one_mul]
    _ ≤ _ := SlitWaveLimit.modulus_le_width (reflectedFamily_parentWave hΓ)

theorem fold_conj (z : ℂ) :
    ParentWaveHalfPlane.fold (Complex.conjLIE z) = ParentWaveHalfPlane.fold z := by
  apply Complex.ext <;> simp [ParentWaveHalfPlane.fold,Complex.conjLIE_apply]

theorem lineLength_union_of_null_inter (ρ : ℂ → ℝ≥0∞) {A B : Set ℂ}
    (hB : MeasurableSet B) (hnull : (μH[1] : Measure ℂ) (A ∩ B) = 0) :
    lineLength ρ (A ∪ B) = lineLength ρ A+lineLength ρ B := by
  have hzero : (∫⁻ z in A ∩ B,ρ z ∂μH[1]) = 0 := by
    rw [Measure.restrict_eq_zero.mpr hnull,lintegral_zero_measure]
  have he := lintegral_inter_add_sdiff (μ := (μH[1] : Measure ℂ)) ρ A hB
  rw [hzero,zero_add] at he
  have hset : A ∪ B = (A \ B) ∪ B := by
    ext z
    simp only [mem_union,mem_sdiff]
    tauto
  unfold lineLength
  rw [hset,lintegral_union hB disjoint_sdiff_left,he]

theorem UpperLeaf.conj_trace_inter_null {M : Marking} {γ : Curve}
    (hγ : UpperLeaf M γ) :
    (μH[1] : Measure ℂ) ((Complex.conjLIE '' trace γ) ∩ trace γ) = 0 := by
  apply measure_mono_null (t := trace γ \ upper) _ (UpperLeaf.trace_outside_upper_null hγ)
  rintro z ⟨⟨w,hw,rfl⟩,hz⟩
  refine ⟨hz,?_⟩
  intro hpos
  have hw0 := hγ.trace_im_nonneg hw
  change (0 : ℝ) < (Complex.conjLIE w).im at hpos
  simp only [Complex.conjLIE_apply,Complex.conj_im] at hpos
  linarith

theorem folded_parentDensity_length {M : Marking} {γ : Curve} (hγ : UpperLeaf M γ)
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    lineLength (ParentWaveHalfPlane.parentDensity ρ) (trace (reflectedCurve γ hγ)) =
      lineLength ρ (trace γ) := by
  let σ := ParentWaveHalfPlane.parentDensity ρ
  have hσ := ParentWaveHalfPlane.parentDensity_measurable hρ
  have hσconj : (fun z => σ (Complex.conjLIE z)) = σ := by
    funext z
    simp only [σ,ParentWaveHalfPlane.parentDensity,fold_conj]
  have hupper : lineLength σ (trace γ) = (2 : ℝ≥0∞)⁻¹*lineLength ρ (trace γ) := by
    calc
      lineLength σ (trace γ) = lineLength (fun z => (2 : ℝ≥0∞)⁻¹*ρ z) (trace γ) := by
        apply lintegral_congr_ae
        apply ae_restrict_of_forall_mem (trace_isCompact γ).measurableSet
        intro z hz
        change (2 : ℝ≥0∞)⁻¹*ρ (ParentWaveHalfPlane.fold z) = (2 : ℝ≥0∞)⁻¹*ρ z
        rw [ParentWaveHalfPlane.fold_of_nonneg (hγ.trace_im_nonneg hz)]
      _ = _ := lineLength_const_mul _ hρ _
  change lineLength σ _ = _
  rw [reflectedCurve_trace]
  change lineLength σ ((Complex.conjLIE '' trace γ) ∪ trace γ) = _
  rw [lineLength_union_of_null_inter σ (trace_isCompact γ).measurableSet
    (UpperLeaf.conj_trace_inter_null hγ),lineLength_conj hσ,hσconj,hupper,
    ← add_mul]
  have htwo : (2 : ℝ≥0∞)⁻¹+(2 : ℝ≥0∞)⁻¹ = 1 := by
    rw [← two_mul,ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
  rw [htwo,one_mul]

theorem folded_parentDensity_admissible {M : Marking} {Γ : Set Curve}
    (hΓ : UpperWave M Γ) {ρ : ℂ → ℝ≥0∞} (hρ : Admissible (traces Γ) ρ) :
    Admissible (traces (reflectedFamily hΓ)) (ParentWaveHalfPlane.parentDensity ρ) := by
  refine ⟨ParentWaveHalfPlane.parentDensity_measurable hρ.1,?_⟩
  rintro S ⟨η,⟨γ,hγ,rfl⟩,rfl⟩
  rw [folded_parentDensity_length (hΓ.leaf γ hγ) hρ.1]
  exact hρ.2 _ ⟨γ,hγ,rfl⟩

theorem reflected_modulus_le_half_upper {M : Marking} {Γ : Set Curve}
    (hΓ : UpperWave M Γ) :
    modulus (traces (reflectedFamily hΓ)) ≤ (2 : ℝ≥0∞)⁻¹*modulus (traces Γ) := by
  unfold modulus
  rw [ENNReal.mul_iInf_of_ne (by norm_num) (by norm_num)]
  apply le_iInf
  intro ρ
  rw [ENNReal.mul_iInf_of_ne (by norm_num) (by norm_num)]
  apply le_iInf
  intro hρ
  change modulus (traces (reflectedFamily hΓ)) ≤ (2 : ℝ≥0∞)⁻¹*area ρ
  exact (modulus_le_area (folded_parentDensity_admissible hΓ hρ)).trans
    (ParentWaveHalfPlane.parentDensity_area_le hρ.1)

/-- Exact all-density width of every constructed reflected parent Wave.
The parent family and the equality are both supplied, without an extremal
foliation or an optimizer-existence assumption. -/
theorem reflected_modulus_eq_half_upper {M : Marking} {Γ : Set Curve}
    (hΓ : UpperWave M Γ) :
    modulus (traces (reflectedFamily hΓ)) = (2 : ℝ≥0∞)⁻¹*modulus (traces Γ) := by
  apply le_antisymm (reflected_modulus_le_half_upper hΓ)
  have h := mul_le_mul_left' (upper_modulus_le_twice_reflected hΓ) ((2 : ℝ≥0∞)⁻¹)
  simpa only [← mul_assoc,ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),one_mul] using h

end
end ParentWaveReflectionModulus
