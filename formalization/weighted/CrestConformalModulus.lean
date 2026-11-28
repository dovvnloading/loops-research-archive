import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Tactic.NormNum

/-!
# Conformal transport of the modulus of smooth geometric arcs

The curve length is the ordinary parametrized metric line integral
`∫ ρ(γ(t)) ‖γ'(t)‖ dt`.  Densities range over all measurable extended
nonnegative functions and area is actual planar Lebesgue area.  The
transport identities below come from the chain rule and the planar
Jacobian formula.  No extremal-length or area-comparison premise is used.

These definitions concern the specified smooth-arc family. They make no
identification with an enlarged family of arbitrary proper paths.
-/

namespace CrestConformalModulus

open Set MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section

/-- A parametrized arc with a positive finite parameter interval, continuous
endpoints, and continuous velocity on the open interval. -/
structure SmoothArc where
  toFun : ℝ → ℂ
  velocity : ℝ → ℂ
  duration : ℝ
  duration_pos : 0 < duration
  continuous : ContinuousOn toFun (Icc 0 duration)
  hasDeriv : ∀ t ∈ Ioo 0 duration, HasDerivAt toFun (velocity t) t
  velocity_continuous : ContinuousOn velocity (Ioo 0 duration)

instance : CoeFun SmoothArc (fun _ => ℝ → ℂ) := ⟨SmoothArc.toFun⟩

/-- Ordinary metric arclength, retaining every traversal of the parameter. -/
def lineLength (ρ : ℂ → ℝ≥0∞) (γ : SmoothArc) : ℝ≥0∞ :=
  ∫⁻ t in Ioo 0 γ.duration, ρ (γ t) * ENNReal.ofReal ‖γ.velocity t‖

def area (ρ : ℂ → ℝ≥0∞) : ℝ≥0∞ := ∫⁻ z, (ρ z)^2

def Admissible (Γ : Set SmoothArc) (ρ : ℂ → ℝ≥0∞) : Prop :=
  Measurable ρ ∧ ∀ γ ∈ Γ, 1 ≤ lineLength ρ γ

/-- The genuine density two-modulus of the specified smooth-arc family. -/
def modulus (Γ : Set SmoothArc) : ℝ≥0∞ :=
  ⨅ (ρ : ℂ → ℝ≥0∞) (_ : Admissible Γ ρ), area ρ

theorem modulus_le_area {Γ : Set SmoothArc} {ρ : ℂ → ℝ≥0∞}
    (hρ : Admissible Γ ρ) : modulus Γ ≤ area ρ :=
  iInf₂_le _ hρ

theorem modulus_mono {Γ Δ : Set SmoothArc} (h : Γ ⊆ Δ) :
    modulus Γ ≤ modulus Δ := by
  apply le_iInf₂
  intro ρ hρ
  exact modulus_le_area ⟨hρ.1, fun γ hγ => hρ.2 γ (h hγ)⟩

theorem area_indicator {U : Set ℂ} (hU : MeasurableSet U)
    (ρ : ℂ → ℝ≥0∞) : area (U.indicator ρ) = ∫⁻ z in U, (ρ z)^2 := by
  have heq : (fun z => (U.indicator ρ z)^2) = U.indicator (fun z => (ρ z)^2) := by
    funext z
    by_cases hz : z ∈ U <;> simp [hz]
  rw [area, heq, lintegral_indicator hU]

def SmoothArc.LiesIn (γ : SmoothArc) (U : Set ℂ) : Prop :=
  ∀ t ∈ Icc 0 γ.duration, γ t ∈ U

/-- A concrete local conformal chart, with its actual complex derivative.
Only the forward derivative is needed; inverse densities use the inverse
homeomorphism and the reciprocal forward conformal factor. -/
structure ConformalChart where
  homeomorph : OpenPartialHomeomorph ℂ ℂ
  derivative : ℂ → ℂ
  hasDeriv : ∀ z ∈ homeomorph.source, HasDerivAt homeomorph (derivative z) z
  derivative_continuous : ContinuousOn derivative homeomorph.source
  derivative_ne_zero : ∀ z ∈ homeomorph.source, derivative z ≠ 0

namespace ConformalChart

/-- An injective restriction of an open holomorphic map supplies the
chart automatically; its inverse is not an additional analytic premise. -/
def ofInjectiveOpenMap {f f' : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (ho : IsOpenMap f) (hi : InjOn f U)
    (hd : ∀ z ∈ U, HasDerivAt f (f' z) z)
    (hc : ContinuousOn f' U) (hn : ∀ z ∈ U, f' z ≠ 0) : ConformalChart where
  homeomorph := OpenPartialHomeomorph.ofContinuousOpen (hi.toPartialEquiv f U)
    (fun z hz => (hd z hz).continuousAt.continuousWithinAt) ho hU
  derivative := f'
  hasDeriv := hd
  derivative_continuous := hc
  derivative_ne_zero := hn

@[simp] theorem ofInjectiveOpenMap_source {f f' : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (ho : IsOpenMap f) (hi : InjOn f U)
    (hd : ∀ z ∈ U, HasDerivAt f (f' z) z)
    (hc : ContinuousOn f' U) (hn : ∀ z ∈ U, f' z ≠ 0) :
    (ofInjectiveOpenMap hU ho hi hd hc hn).homeomorph.source = U := rfl

@[simp] theorem ofInjectiveOpenMap_target {f f' : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (ho : IsOpenMap f) (hi : InjOn f U)
    (hd : ∀ z ∈ U, HasDerivAt f (f' z) z)
    (hc : ContinuousOn f' U) (hn : ∀ z ∈ U, f' z ≠ 0) :
    (ofInjectiveOpenMap hU ho hi hd hc hn).homeomorph.target = f '' U := rfl

@[simp] theorem ofInjectiveOpenMap_apply {f f' : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (ho : IsOpenMap f) (hi : InjOn f U)
    (hd : ∀ z ∈ U, HasDerivAt f (f' z) z)
    (hc : ContinuousOn f' U) (hn : ∀ z ∈ U, f' z ≠ 0) (z : ℂ) :
    (ofInjectiveOpenMap hU ho hi hd hc hn).homeomorph z = f z := rfl

def mapArc (C : ConformalChart) (γ : SmoothArc)
    (hγ : γ.LiesIn C.homeomorph.source) : SmoothArc where
  toFun := fun t => C.homeomorph (γ t)
  velocity := fun t => C.derivative (γ t) * γ.velocity t
  duration := γ.duration
  duration_pos := γ.duration_pos
  continuous := C.homeomorph.continuousOn.comp γ.continuous hγ
  hasDeriv := by
    intro t ht
    have h := (C.hasDeriv (γ t) (hγ t ⟨ht.1.le, ht.2.le⟩)).complexToReal_fderiv
    simpa only [Function.comp_def, smul_apply, one_apply_eq_self,
      smul_eq_mul] using! h.comp_hasDerivAt t (γ.hasDeriv t ht)
  velocity_continuous :=
    (C.derivative_continuous.comp
      (γ.continuous.mono Ioo_subset_Icc_self)
      (fun t ht => hγ t ⟨ht.1.le, ht.2.le⟩)).mul γ.velocity_continuous

def transportFamily (C : ConformalChart) (Γ : Set SmoothArc) : Set SmoothArc :=
  {δ | ∃ γ, ∃ hγ : γ.LiesIn C.homeomorph.source,
    γ ∈ Γ ∧ C.mapArc γ hγ = δ}

def factor (C : ConformalChart) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ‖C.derivative z‖

def pullDensity (C : ConformalChart) (ρ : ℂ → ℝ≥0∞) : ℂ → ℝ≥0∞ :=
  C.homeomorph.source.indicator (fun z => ρ (C.homeomorph z) * C.factor z)

def pushDensity (C : ConformalChart) (ρ : ℂ → ℝ≥0∞) : ℂ → ℝ≥0∞ :=
  C.homeomorph.target.indicator
    (fun w => ρ (C.homeomorph.symm w) * (C.factor (C.homeomorph.symm w))⁻¹)

theorem factor_ne_zero (C : ConformalChart) {z : ℂ}
    (hz : z ∈ C.homeomorph.source) : C.factor z ≠ 0 := by
  exact (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr (C.derivative_ne_zero z hz))).ne'

theorem factor_ne_top (C : ConformalChart) (z : ℂ) : C.factor z ≠ ⊤ :=
  ENNReal.ofReal_ne_top

theorem factor_continuous (C : ConformalChart) :
    ContinuousOn C.factor C.homeomorph.source :=
  ENNReal.continuous_ofReal.comp_continuousOn C.derivative_continuous.norm

private theorem measurable_local_density {U : Set ℂ} (hU : MeasurableSet U)
    {f : ℂ → ℂ} {w : ℂ → ℝ≥0∞} (hf : ContinuousOn f U) (hw : ContinuousOn w U)
    {ρ : ℂ → ℝ≥0∞} (hρ : Measurable ρ) :
    Measurable (U.indicator (fun z => ρ (f z) * w z)) := by
  classical
  let f₀ : ℂ → ℂ := U.piecewise f (fun _ => 0)
  let w₀ : ℂ → ℝ≥0∞ := U.piecewise w (fun _ => 0)
  have hf₀ : Measurable f₀ := hf.measurable_piecewise continuous_const.continuousOn hU
  have hw₀ : Measurable w₀ := hw.measurable_piecewise continuous_const.continuousOn hU
  have hm := ((hρ.comp hf₀).mul hw₀).indicator hU
  convert hm using 1
  funext z
  by_cases hz : z ∈ U <;> simp [f₀, w₀, hz]

theorem pullDensity_measurable (C : ConformalChart) {ρ : ℂ → ℝ≥0∞}
    (hρ : Measurable ρ) : Measurable (C.pullDensity ρ) :=
  measurable_local_density C.homeomorph.open_source.measurableSet
    C.homeomorph.continuousOn C.factor_continuous hρ

theorem pushDensity_measurable (C : ConformalChart) {ρ : ℂ → ℝ≥0∞}
    (hρ : Measurable ρ) : Measurable (C.pushDensity ρ) := by
  apply measurable_local_density C.homeomorph.open_target.measurableSet
    C.homeomorph.continuousOn_symm _ hρ
  exact (C.factor_continuous.comp C.homeomorph.continuousOn_symm
    (fun z hz => C.homeomorph.map_target hz)).fun_inv

/-- The real Jacobian of complex multiplication is its squared norm. -/
theorem complex_derivative_det (c : ℂ) :
    ((ContinuousLinearMap.toSpanSingleton ℂ c).restrictScalars ℝ).det = ‖c‖^2 := by
  simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars,
    Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq]

/-- Exact area change on a chart, with arbitrary nonnegative integrand. -/
theorem integral_image (C : ConformalChart) (g : ℂ → ℝ≥0∞) :
    (∫⁻ w in C.homeomorph.target, g w) =
      ∫⁻ z in C.homeomorph.source, C.factor z ^ 2 * g (C.homeomorph z) := by
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    C.homeomorph.open_source.measurableSet
    (fun z hz => ((C.hasDeriv z hz).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt)
    C.homeomorph.injOn g
  rw [C.homeomorph.image_source_eq_target] at h
  convert h using 1
  apply setLIntegral_congr_fun C.homeomorph.open_source.measurableSet
  intro z _hz
  dsimp only
  rw [complex_derivative_det, abs_of_nonneg (sq_nonneg _),
    ENNReal.ofReal_pow (norm_nonneg _)]
  rfl

/-- Pullback preserves the metric length of each complete mapped arc. -/
theorem lineLength_pull (C : ConformalChart) (γ : SmoothArc)
    (hγ : γ.LiesIn C.homeomorph.source) (ρ : ℂ → ℝ≥0∞) :
    lineLength (C.pullDensity ρ) γ = lineLength ρ (C.mapArc γ hγ) := by
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  change (C.pullDensity ρ) (γ t) * ENNReal.ofReal ‖γ.velocity t‖ =
    ρ (C.homeomorph (γ t)) * ENNReal.ofReal ‖C.derivative (γ t) * γ.velocity t‖
  rw [pullDensity, indicator_of_mem (hγ t ⟨ht.1.le, ht.2.le⟩), norm_mul,
    ENNReal.ofReal_mul (norm_nonneg _)]
  exact mul_assoc _ _ _

/-- The pushed density gives precisely the original length, including
unbounded densities and infinite line integrals. -/
theorem lineLength_push (C : ConformalChart) (γ : SmoothArc)
    (hγ : γ.LiesIn C.homeomorph.source) (ρ : ℂ → ℝ≥0∞) :
    lineLength (C.pushDensity ρ) (C.mapArc γ hγ) = lineLength ρ γ := by
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have hz := hγ t ⟨ht.1.le, ht.2.le⟩
  change (C.pushDensity ρ) (C.homeomorph (γ t)) *
      ENNReal.ofReal ‖C.derivative (γ t) * γ.velocity t‖ =
    ρ (γ t) * ENNReal.ofReal ‖γ.velocity t‖
  rw [pushDensity, indicator_of_mem (C.homeomorph.map_source hz),
    C.homeomorph.left_inv hz, norm_mul, ENNReal.ofReal_mul (norm_nonneg _)]
  change (ρ (γ t) * (C.factor (γ t))⁻¹) *
      (C.factor (γ t) * ENNReal.ofReal ‖γ.velocity t‖) = _
  rw [mul_assoc, ← mul_assoc (C.factor (γ t))⁻¹,
    ENNReal.inv_mul_cancel (C.factor_ne_zero hz) (C.factor_ne_top _), one_mul]

/-- Pullback area is exactly the area on the target of the actual chart. -/
theorem area_pull (C : ConformalChart) (ρ : ℂ → ℝ≥0∞) :
    area (C.pullDensity ρ) = ∫⁻ w in C.homeomorph.target, (ρ w)^2 := by
  rw [pullDensity, area_indicator C.homeomorph.open_source.measurableSet,
    C.integral_image]
  apply lintegral_congr
  intro z
  simp only [mul_pow, mul_comm]

/-- Pushing by the reciprocal conformal factor preserves exactly the
source area.  This is a consequence of the forward Jacobian formula. -/
theorem area_push (C : ConformalChart) (ρ : ℂ → ℝ≥0∞) :
    area (C.pushDensity ρ) = ∫⁻ z in C.homeomorph.source, (ρ z)^2 := by
  rw [pushDensity, area_indicator C.homeomorph.open_target.measurableSet,
    C.integral_image]
  apply setLIntegral_congr_fun C.homeomorph.open_source.measurableSet
  intro z hz
  dsimp only
  rw [C.homeomorph.left_inv hz]
  calc
    C.factor z ^ 2 * (ρ z * (C.factor z)⁻¹)^2 =
        (C.factor z * (C.factor z)⁻¹)^2 * (ρ z)^2 := by
      simp only [mul_pow, mul_comm, mul_left_comm]
    _ = (ρ z)^2 := by
      rw [ENNReal.mul_inv_cancel (C.factor_ne_zero hz) (C.factor_ne_top z),
        one_pow, one_mul]

theorem admissible_pull (C : ConformalChart) {Γ : Set SmoothArc}
    (hΓ : ∀ γ ∈ Γ, γ.LiesIn C.homeomorph.source)
    {ρ : ℂ → ℝ≥0∞} (hρ : Admissible (C.transportFamily Γ) ρ) :
    Admissible Γ (C.pullDensity ρ) := by
  refine ⟨C.pullDensity_measurable hρ.1, ?_⟩
  intro γ hγ
  rw [C.lineLength_pull γ (hΓ γ hγ)]
  exact hρ.2 _ ⟨γ, hΓ γ hγ, hγ, rfl⟩

theorem admissible_push (C : ConformalChart) {Γ : Set SmoothArc}
    {ρ : ℂ → ℝ≥0∞} (hρ : Admissible Γ ρ) :
    Admissible (C.transportFamily Γ) (C.pushDensity ρ) := by
  refine ⟨C.pushDensity_measurable hρ.1, ?_⟩
  rintro δ ⟨γ, hγ, hmem, rfl⟩
  rw [C.lineLength_push]
  exact hρ.2 γ hmem

/-- Exact conformal invariance for the entire specified family of smooth
arcs, proved using every measurable admissible density in both directions. -/
theorem modulus_transport (C : ConformalChart) (Γ : Set SmoothArc)
    (hΓ : ∀ γ ∈ Γ, γ.LiesIn C.homeomorph.source) :
    modulus (C.transportFamily Γ) = modulus Γ := by
  apply le_antisymm
  · apply le_iInf₂
    intro ρ hρ
    calc
      modulus (C.transportFamily Γ) ≤ area (C.pushDensity ρ) :=
        modulus_le_area (C.admissible_push hρ)
      _ = ∫⁻ z in C.homeomorph.source, (ρ z)^2 := C.area_push ρ
      _ ≤ area ρ := lintegral_mono' Measure.restrict_le_self le_rfl
  · apply le_iInf₂
    intro ρ hρ
    calc
      modulus Γ ≤ area (C.pullDensity ρ) :=
        modulus_le_area (C.admissible_pull hΓ hρ)
      _ = ∫⁻ z in C.homeomorph.target, (ρ z)^2 := C.area_pull ρ
      _ ≤ area ρ := lintegral_mono' Measure.restrict_le_self le_rfl

end ConformalChart

end
end CrestConformalModulus
