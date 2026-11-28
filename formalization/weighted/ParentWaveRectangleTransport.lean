import ParentWaveRectangleFoliation
import ParentWaveTraceEndpoints
import ParentWaveConformal

/-!
# Canonical trace identities for transporting the rectangle foliation

The transport uses the complete family of horizontal segments. Their
open-parameter traces lie in the open rectangle, and deleting endpoint
atoms preserves exactly the canonical full-trace modulus.
-/

namespace ParentWaveRectangleTransport

open Set Function MeasureTheory MarkedSlitTransport SlitWaveModulus
open ParentWaveRectangleModulus ParentWaveRectangleFoliation ParentWaveTraceEndpoints
open scoped ENNReal NNReal

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- The open source on which the conformal derivative is used. -/
def rectangleInterior (R a b : ℝ) : Set ℂ :=
  {z | z.re ∈ Ioo 0 R ∧ z.im ∈ Ioo a b}

theorem rectangleInterior_open (R a b : ℝ) : IsOpen (rectangleInterior R a b) :=
  (isOpen_Ioo.preimage Complex.continuous_re).inter
    (isOpen_Ioo.preimage Complex.continuous_im)

/-- Every open-parameter segment point lies strictly inside the rectangle. -/
theorem rectangleCurve_interior_subset {R a b y : ℝ} (hR : 0 < R)
    (hy : y ∈ Ioo a b) :
    interiorTrace (rectangleCurve R y) ⊆ rectangleInterior R a b := by
  rintro z ⟨t,ht,rfl⟩
  have hx : R*(t:ℝ) ∈ Ioo 0 R := ⟨mul_pos hR ht.1,by nlinarith [ht.2]⟩
  simpa [rectangleInterior,rectangleCurve,CollarCapacityLower.horizontal] using And.intro hx hy

/-- The open-parameter traces are Borel, including for the uncountable
family used by the modulus. -/
theorem rectangleCurve_interior_measurable {R : ℝ} (hR : 0 < R) (y : ℝ) :
    MeasurableSet (interiorTrace (rectangleCurve R y)) :=
  parameterInterior_isOpen.measurableSet.image_of_continuousOn_injOn
    (rectangleCurve R y).continuous.continuousOn (rectangleCurve_injective hR y).injOn

/-- The transported open trace is exactly the image of the original
open trace, not merely a subset or a representative smooth curve. -/
theorem chartCurve_interiorTrace {R a b : ℝ} {F : ℂ → ℂ}
    (hF : ContinuousOn F (rectangle R a b)) (hR : 0 < R) (y : Ioo a b) :
    interiorTrace (chartCurve hF hR y) = F '' interiorTrace (rectangleCurve R y) := by
  simp only [interiorTrace,chartCurve,ContinuousMap.coe_mk,image_image]

/-- Exact image identity for every interior trace in the complete family. -/
theorem chartFamily_interiorTraces {R a b : ℝ} {F : ℂ → ℂ}
    (hF : ContinuousOn F (rectangle R a b)) (hR : 0 < R) :
    interiorTrace '' chartFamily hF hR =
      (fun S : Set ℂ => F '' S) '' (interiorTrace '' rectangleFamily R a b) := by
  ext S
  constructor
  · rintro ⟨γ,⟨y,rfl⟩,rfl⟩
    exact ⟨interiorTrace (rectangleCurve R y),
      ⟨rectangleCurve R y,⟨y,y.2,rfl⟩,rfl⟩,(chartCurve_interiorTrace hF hR y).symm⟩
  · rintro ⟨T,⟨γ,⟨y,hy,rfl⟩,rfl⟩,rfl⟩
    exact ⟨chartCurve hF hR ⟨y,hy⟩,⟨⟨y,hy⟩,rfl⟩,chartCurve_interiorTrace hF hR ⟨y,hy⟩⟩

/-- A boundary extension of the conformal map has the same interior
trace family as the map itself. The equality is proved pointwise on
the actual rectangle; no extension value outside it is constrained. -/
theorem chartFamily_interiorTraces_of_eqOn {R a b : ℝ} {F G : ℂ → ℂ}
    (hF : ContinuousOn F (rectangle R a b)) (hR : 0 < R)
    (hFG : EqOn F G (rectangleInterior R a b)) :
    interiorTrace '' chartFamily hF hR =
      (fun S : Set ℂ => G '' S) '' (interiorTrace '' rectangleFamily R a b) := by
  rw [chartFamily_interiorTraces]
  apply Set.image_congr
  rintro S ⟨γ,⟨y,hy,rfl⟩,rfl⟩
  apply Set.image_congr
  intro z hz
  exact hFG (rectangleCurve_interior_subset hR hy hz)

/-- A conformal chart on the open rectangle, with a continuous extension
to its vertical sides, preserves the exact canonical foliation modulus.
Only the literal agreement on the rectangle interior is required. -/
theorem chartFamily_modulus (C : ParentWaveConformal.Chart) {R a b : ℝ} {F : ℂ → ℂ}
    (hF : ContinuousOn F (rectangle R a b)) (hR : 0 < R)
    (hsource : rectangleInterior R a b ⊆ C.homeomorph.source)
    (hFC : EqOn F C.homeomorph (rectangleInterior R a b)) :
    modulus (traces (chartFamily hF hR)) = ENNReal.ofReal ((b-a)/R) := by
  have hdom : ∀ S ∈ interiorTrace '' rectangleFamily R a b,S ⊆ C.homeomorph.source := by
    rintro S ⟨γ,⟨y,hy,rfl⟩,rfl⟩
    exact (rectangleCurve_interior_subset hR hy).trans hsource
  have hmeas : ∀ S ∈ interiorTrace '' rectangleFamily R a b,MeasurableSet S := by
    rintro S ⟨γ,⟨y,hy,rfl⟩,rfl⟩
    exact rectangleCurve_interior_measurable hR y
  calc
    modulus (traces (chartFamily hF hR)) =
        modulus (interiorTrace '' chartFamily hF hR) := modulus_trace_eq_interiorTrace _
    _ = modulus ((fun S : Set ℂ => C.homeomorph '' S) ''
        (interiorTrace '' rectangleFamily R a b)) := by
      rw [chartFamily_interiorTraces_of_eqOn hF hR hFC]
    _ = modulus (interiorTrace '' rectangleFamily R a b) :=
      ParentWaveConformal.modulus_image_eq C hdom hmeas
    _ = modulus (traces (rectangleFamily R a b)) :=
      (modulus_trace_eq_interiorTrace _).symm
    _ = ENNReal.ofReal ((b-a)/R) := rectangle_modulus hR

/-- The full elliptic rectangle foliation supplies an actual parent wave
of exactly half the rectangle modulus. The witness satisfies the original
homotopy class, bank conditions, Borel support, and disjointness fields. -/
theorem exists_parentWave_of_chart (C : ParentWaveConformal.Chart)
    {M : Marking} {R a b : ℝ} {F : ℂ → ℂ}
    (hF : ContinuousOn F (rectangle R a b)) (hR : 0 < R)
    (hFinj : InjOn F (rectangle R a b))
    (hsource : rectangleInterior R a b ⊆ C.homeomorph.source)
    (hFC : EqOn F C.homeomorph (rectangleInterior R a b))
    (hfirst : ∀ y ∈ Ioo a b,M.ends (F (CollarCapacityLower.horizontal y 0)))
    (hlast : ∀ y ∈ Ioo a b,
      (F (CollarCapacityLower.horizontal y R)).im = 0 ∧
      (F (CollarCapacityLower.horizontal y R)).re < M.left)
    (hupper : ∀ z : ℂ,z.re ∈ Ioo 0 R → z.im ∈ Ioo a b → 0 < (F z).im) :
    ∃ Γ : Set Curve,ParentWave M univ Γ ∧
      modulus (traces Γ) = (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal ((b-a)/R) := by
  have hu := chartFamily_upperWave hF hR hFinj hfirst hlast hupper
  refine ⟨ParentWaveReflection.reflectedFamily hu,
    ParentWaveReflection.reflectedFamily_parentWave hu,?_⟩
  rw [ParentWaveReflectionModulus.reflected_modulus_eq_half_upper,
    chartFamily_modulus C hF hR hsource hFC]

/-- The exact geometric parent width dominates the realized rectangle
value. This is a bound on the canonical supremum over full Borel waves. -/
theorem parent_width_lower_of_chart (C : ParentWaveConformal.Chart)
    {M : Marking} {R a b : ℝ} {F : ℂ → ℂ}
    (hF : ContinuousOn F (rectangle R a b)) (hR : 0 < R)
    (hFinj : InjOn F (rectangle R a b))
    (hsource : rectangleInterior R a b ⊆ C.homeomorph.source)
    (hFC : EqOn F C.homeomorph (rectangleInterior R a b))
    (hfirst : ∀ y ∈ Ioo a b,M.ends (F (CollarCapacityLower.horizontal y 0)))
    (hlast : ∀ y ∈ Ioo a b,
      (F (CollarCapacityLower.horizontal y R)).im = 0 ∧
      (F (CollarCapacityLower.horizontal y R)).re < M.left)
    (hupper : ∀ z : ℂ,z.re ∈ Ioo 0 R → z.im ∈ Ioo a b → 0 < (F z).im) :
    (2 : ℝ≥0∞)⁻¹ * ENNReal.ofReal ((b-a)/R) ≤ SlitWaveLimit.width M univ := by
  obtain ⟨Γ,hΓ,hwidth⟩ := exists_parentWave_of_chart C hF hR hFinj hsource hFC
    hfirst hlast hupper
  rw [← hwidth]
  exact SlitWaveLimit.modulus_le_width hΓ

end
end ParentWaveRectangleTransport
