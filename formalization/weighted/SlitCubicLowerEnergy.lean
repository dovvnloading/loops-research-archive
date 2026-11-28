import SlitCubicSurjective
import CrestConformalModulus
import CollarMetricEnergy
import SlitWaveModulus

/-!
# Lower energy from the actual reflected inverse rectangle

The only length premise is the explicit parameter integral along the two
inverse horizontal segments. Cauchy--Schwarz is applied on the disjoint sum
of their parameter intervals, followed by the actual conformal Jacobian.
All densities may be arbitrary measurable extended nonnegative functions.
-/

namespace SlitCubicLowerEnergy

open Set Filter MeasureTheory Complex SlitCubicCalibration SlitCubicBoundary
  SlitCubicBoundaryRange SlitCubicRectangle SlitCubicSurjective
open scoped Topology ENNReal
noncomputable section

theorem two_slice_energy {f g : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    {B : ℝ} (hB : 0 < B)
    (hlen : 1 ≤ ∫⁻ x in Ioo 0 B, f x + g x) :
    ENNReal.ofReal (1/(2*B)) ≤
      (∫⁻ x in Ioo 0 B, (f x)^2) + ∫⁻ x in Ioo 0 B, (g x)^2 := by
  let ν : Measure ℝ := volume.restrict (Ioo 0 B)
  let μ : Measure (ℝ ⊕ ℝ) := Measure.map Sum.inl ν + Measure.map Sum.inr ν
  have hfg : Measurable (Sum.elim f g) := hf.sumElim hg
  have hmass : μ univ = ENNReal.ofReal (2*B) := by
    dsimp [μ]
    rw [Measure.map_apply measurable_inl MeasurableSet.univ,
      Measure.map_apply measurable_inr MeasurableSet.univ]
    simp only [preimage_univ,ν,Measure.restrict_apply_univ,Real.volume_Ioo,sub_zero]
    rw [← ENNReal.ofReal_add hB.le hB.le]
    congr 1
    ring
  have hlen' : 1 ≤ ∫⁻ z, Sum.elim f g z ∂μ := by
    dsimp [μ]
    rw [lintegral_add_measure,lintegral_map hfg measurable_inl,
      lintegral_map hfg measurable_inr]
    simpa only [Sum.elim_inl,Sum.elim_inr,ν,lintegral_add_left hf] using hlen
  have he := CollarMetricEnergy.reciprocal_mass_le_square_integral hfg.aemeasurable
    (by rw [hmass]; exact (ENNReal.ofReal_pos.mpr (mul_pos (by norm_num) hB)).ne')
    (by rw [hmass]; exact ENNReal.ofReal_ne_top) hlen'
  rw [hmass,← ENNReal.ofReal_inv_of_pos (mul_pos (by norm_num) hB)] at he
  dsimp [μ] at he
  rw [lintegral_add_measure,lintegral_map (hfg.pow_const 2) measurable_inl,
    lintegral_map (hfg.pow_const 2) measurable_inr] at he
  simpa only [one_div,Sum.elim_inl,Sum.elim_inr,ν] using he

def point (x y : ℝ) : ℂ := (x:ℂ)+(y:ℂ)*I

theorem two_rectangle_energy {f g : ℂ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) {A B : ℝ} (_hA : 0 < A) (hB : 0 < B)
    (hlen : ∀ y ∈ Ioo (-A) 0,
      1 ≤ ∫⁻ x in Ioo 0 B, f (point x y) + g (point x y)) :
    ENNReal.ofReal (A/(2*B)) ≤ SlitWaveModulus.area f + SlitWaveModulus.area g := by
  have hp (y : ℝ) : Measurable (fun x => point x y) := by unfold point; fun_prop
  have hconst : (∫⁻ _y in Ioo (-A) 0, ENNReal.ofReal (1/(2*B))) =
      ENNReal.ofReal (A/(2*B)) := by
    rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Ioo,zero_sub,neg_neg,
      ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 1/(2*B))]
    congr 1
    ring
  have hm : Measurable (fun z : ℂ => (f z)^2+(g z)^2) := (hf.pow_const 2).add (hg.pow_const 2)
  calc
    _ = ∫⁻ _y in Ioo (-A) 0, ENNReal.ofReal (1/(2*B)) := hconst.symm
    _ ≤ ∫⁻ y in Ioo (-A) 0,
        (∫⁻ x in Ioo 0 B, (f (point x y))^2) + ∫⁻ x in Ioo 0 B, (g (point x y))^2 := by
      exact setLIntegral_mono' measurableSet_Ioo fun y hy =>
        two_slice_energy (hf.comp (hp y)) (hg.comp (hp y)) hB (hlen y hy)
    _ = ∫⁻ y in Ioo (-A) 0, ∫⁻ x in Ioo 0 B,
        (f (point x y))^2+(g (point x y))^2 := by
      apply lintegral_congr
      intro y
      exact (lintegral_add_left ((hf.comp (hp y)).pow_const 2) _).symm
    _ ≤ ∫⁻ y : ℝ, ∫⁻ x : ℝ, (f (point x y))^2+(g (point x y))^2 :=
      (lintegral_mono (fun _ => setLIntegral_le_lintegral _ _)).trans
        (setLIntegral_le_lintegral _ _)
    _ = ∫⁻ z : ℂ, (f z)^2+(g z)^2 := by
      have hh := (lintegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (fun p : ℝ × ℝ => (f (CollarCapacityLower.horizontal p.1 p.2))^2 +
          (g (CollarCapacityLower.horizontal p.1 p.2))^2)
        (hm.comp CollarCapacityLower.horizontal_measurePreserving.measurable).aemeasurable).symm
      have hh' : (∫⁻ y : ℝ, ∫⁻ x : ℝ, (f (point x y))^2+(g (point x y))^2) =
          ∫⁻ p : ℝ × ℝ, (f (CollarCapacityLower.horizontal p.1 p.2))^2 +
            (g (CollarCapacityLower.horizontal p.1 p.2))^2 := hh
      exact hh'.trans (CollarCapacityLower.horizontal_measurePreserving.lintegral_comp hm)
    _ = _ := lintegral_add_left (hf.pow_const 2) _

def inverseVelocity {a b c : ℝ} (hab : a < b) (hbc : b < c) (w : ℂ) : ℂ :=
  -(upperRoot a ((rectangleChart hab hbc).symm w) *
    upperRoot b ((rectangleChart hab hbc).symm w) *
    upperRoot c ((rectangleChart hab hbc).symm w))

private theorem inverseVelocity_ne_zero {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {w : ℂ} (hw : w ∈ openRectangle (period a b c) (height a b c)) :
    inverseVelocity hab hbc w ≠ 0 := by
  have hz : (rectangleChart hab hbc).symm w ∈ upper :=
    (rectangleChart hab hbc).map_target hw
  have hn (t : ℝ) : (rectangleChart hab hbc).symm w ≠ (t:ℂ) := by
    intro he
    have hh := congrArg Complex.im he
    have hp : 0 < ((rectangleChart hab hbc).symm w).im := hz
    simp only [Complex.ofReal_im] at hh
    linarith
  exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero
    (upperRoot_ne_zero hz.le (hn a)) (upperRoot_ne_zero hz.le (hn b)))
    (upperRoot_ne_zero hz.le (hn c)))

/-- The actual inverse rectangle map as the archive's conformal chart. -/
def inverseConformal {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    CrestConformalModulus.ConformalChart where
  homeomorph := (rectangleChart hab hbc).symm
  derivative := inverseVelocity hab hbc
  hasDeriv := fun _ hw => rectangleChart_symm_hasDerivAt hab hbc hw
  derivative_continuous := by
    have hc := (rectangleChart hab hbc).continuousOn_symm
    exact (((upperRoot_continuous a).comp_continuousOn hc).mul
      ((upperRoot_continuous b).comp_continuousOn hc) |>.mul
      ((upperRoot_continuous c).comp_continuousOn hc)).neg
  derivative_ne_zero := fun _ hw => inverseVelocity_ne_zero hab hbc hw

def inverseSliceLength {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (ρ : ℂ → ℝ≥0∞) (y : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Ioo 0 (period a b c),
    (ρ ((rectangleChart hab hbc).symm (point x y)) +
      ρ ((starRingEnd ℂ) ((rectangleChart hab hbc).symm (point x y)))) *
      ENNReal.ofReal ‖inverseVelocity hab hbc (point x y)‖

theorem two_halfplane_energy_le (ρ : ℂ → ℝ≥0∞) :
    (∫⁻ z in upper, (ρ z)^2) +
      (∫⁻ z in upper, (ρ ((starRingEnd ℂ) z))^2) ≤ SlitWaveModulus.area ρ := by
  let L : Set ℂ := {z | z.im < 0}
  have hL : MeasurableSet L := (isOpen_lt Complex.continuous_im continuous_const).measurableSet
  have hpre : conjLIE ⁻¹' L = upper := by
    ext z
    simp [L,upper]
  have href := conjLIE.measurePreserving.setLIntegral_comp_preimage_emb
    conjLIE.toHomeomorph.measurableEmbedding (fun z => (ρ z)^2) L
  simp only [hpre,conjLIE_apply] at href
  have hdis : Disjoint upper L := by
    rw [Set.disjoint_left]
    intro z hz hzl
    have hzpos : 0 < z.im := hz
    have hzneg : z.im < 0 := hzl
    exact (not_lt_of_ge hzpos.le) hzneg
  rw [href,← lintegral_union hL hdis]
  exact setLIntegral_le_lintegral _ _

/-- The actual inverse segments force the matching area lower bound.
The explicit slice condition will be discharged by geometric admissibility
of the constructed parent foliation. -/
theorem area_lower_of_inverse_slices {a b c : ℝ} (hab : a < b) (hbc : b < c)
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ)
    (hlen : ∀ y ∈ Ioo (-height a b c) 0, 1 ≤ inverseSliceLength hab hbc ρ y) :
    ENNReal.ofReal (height a b c / (2*period a b c)) ≤ SlitWaveModulus.area ρ := by
  let C := inverseConformal hab hbc
  let ρr : ℂ → ℝ≥0∞ := fun z => ρ ((starRingEnd ℂ) z)
  have hr : Measurable ρr := hρ.comp Complex.continuous_conj.measurable
  have hf := C.pullDensity_measurable hρ
  have hg := C.pullDensity_measurable hr
  have hs : ∀ y ∈ Ioo (-height a b c) 0,
      1 ≤ ∫⁻ x in Ioo 0 (period a b c),
        C.pullDensity ρ (point x y) + C.pullDensity ρr (point x y) := by
    intro y hy
    have he : (∫⁻ x in Ioo 0 (period a b c),
        C.pullDensity ρ (point x y) + C.pullDensity ρr (point x y)) =
        inverseSliceLength hab hbc ρ y := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro x hx
      have hw : point x y ∈ C.homeomorph.source := by
        change point x y ∈ openRectangle (period a b c) (height a b c)
        simpa [point,openRectangle] using And.intro hx.1 (And.intro hx.2 hy)
      dsimp only
      rw [CrestConformalModulus.ConformalChart.pullDensity,
        CrestConformalModulus.ConformalChart.pullDensity,indicator_of_mem hw,
        indicator_of_mem hw]
      exact (add_mul _ _ _).symm
    rw [he]
    exact hlen y hy
  have hh := two_rectangle_energy hf hg (height_pos hab hbc) (period_pos hab hbc) hs
  have ha0 : SlitWaveModulus.area (C.pullDensity ρ) = ∫⁻ z in upper, (ρ z)^2 :=
    C.area_pull ρ
  have ha1 : SlitWaveModulus.area (C.pullDensity ρr) =
      ∫⁻ z in upper, (ρ ((starRingEnd ℂ) z))^2 := C.area_pull ρr
  rw [ha0,ha1] at hh
  exact hh.trans (two_halfplane_energy_le ρ)

end
end SlitCubicLowerEnergy
