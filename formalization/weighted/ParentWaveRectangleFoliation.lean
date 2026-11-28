import ParentWaveRectangleModulus
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Sending the complete rectangle foliation to the actual upper half-plane

A continuous injective inverse chart on the rectangle with its two
vertical sides sends every horizontal segment to a genuine simple arc.
The image of the full rectangle is Borel by the measurable image theorem.
Electrode and interior-image conditions therefore give the exact
`UpperWave` structure needed by reflection into a canonical parent wave.
-/

namespace ParentWaveRectangleFoliation

open Set Function MarkedSlitTransport ParentWaveReflection
open ParentWaveRectangleModulus

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {M : Marking} {R a b : ℝ} {F : ℂ → ℂ}

/-- A horizontal segment sent through the specified continuous chart. -/
def chartCurve (hF : ContinuousOn F (rectangle R a b)) (hR : 0 < R)
    (y : Ioo a b) : Curve :=
  ⟨fun t => F (rectangleCurve R y t),
    hF.comp_continuous (rectangleCurve R y).continuous
      (rectangleCurve_mem hR y.2)⟩

/-- All interior heights are used; no countable subfamily is selected. -/
def chartFamily (hF : ContinuousOn F (rectangle R a b)) (hR : 0 < R) : Set Curve :=
  range (chartCurve hF hR)

@[simp] theorem chartCurve_initial (hF : ContinuousOn F (rectangle R a b))
    (hR : 0 < R) (y : Ioo a b) :
    chartCurve hF hR y initial = F (CollarCapacityLower.horizontal y 0) := by
  simp [chartCurve]

@[simp] theorem chartCurve_terminal (hF : ContinuousOn F (rectangle R a b))
    (hR : 0 < R) (y : Ioo a b) :
    chartCurve hF hR y terminal = F (CollarCapacityLower.horizontal y R) := by
  simp [chartCurve]

/-- The full original trace is transported exactly, including both ends. -/
theorem chartCurve_trace (hF : ContinuousOn F (rectangle R a b))
    (hR : 0 < R) (y : Ioo a b) :
    trace (chartCurve hF hR y) = F '' trace (rectangleCurve R y) := by
  exact range_comp F (rectangleCurve R y)

/-- Every transported segment remains injective on the whole parameter
interval. This is stronger than the interior simplicity of parent leaves. -/
theorem chartCurve_injective (hF : ContinuousOn F (rectangle R a b))
    (hR : 0 < R) (hFinj : InjOn F (rectangle R a b)) (y : Ioo a b) :
    Injective (chartCurve hF hR y) := by
  intro s t h
  apply rectangleCurve_injective hR y
  exact hFinj (rectangleCurve_mem hR y.2 s) (rectangleCurve_mem hR y.2 t) h

/-- The union of all transported full traces is the image of the entire
rectangle strip, including its vertical sides. -/
theorem chartFamily_support (hF : ContinuousOn F (rectangle R a b))
    (hR : 0 < R) :
    upperSupport (chartFamily hF hR) = F '' rectangle R a b := by
  ext z
  simp only [upperSupport,chartFamily,mem_iUnion,mem_range]
  constructor
  · rintro ⟨γ,⟨y,rfl⟩,⟨t,rfl⟩⟩
    exact ⟨rectangleCurve R y t,rectangleCurve_mem hR y.2 t,rfl⟩
  · rintro ⟨w,hw,rfl⟩
    have hwtrace : w ∈ trace (rectangleCurve R w.im) := by
      rw [rectangleCurve_trace hR]
      refine ⟨w.re,hw.1,?_⟩
      apply Complex.ext <;> simp [CollarCapacityLower.horizontal]
    rcases hwtrace with ⟨t,ht⟩
    refine ⟨chartCurve hF hR ⟨w.im,hw.2⟩,⟨⟨w.im,hw.2⟩,rfl⟩,t,?_⟩
    change F (rectangleCurve R w.im t) = F w
    rw [ht]

/-- Distinct leaves have disjoint full traces, including their ends. -/
theorem chartFamily_disjoint (hF : ContinuousOn F (rectangle R a b))
    (hR : 0 < R) (hFinj : InjOn F (rectangle R a b)) :
    ∀ γ ∈ chartFamily hF hR,∀ η ∈ chartFamily hF hR,γ ≠ η →
      Disjoint (trace γ) (trace η) := by
  rintro γ ⟨y,rfl⟩ η ⟨v,rfl⟩ hne
  apply Set.disjoint_left.mpr
  rintro z ⟨s,hs⟩ ⟨t,ht⟩
  have he : rectangleCurve R y s = rectangleCurve R v t :=
    hFinj (rectangleCurve_mem hR y.2 s) (rectangleCurve_mem hR v.2 t)
      (hs.trans ht.symm)
  have hyv : (y : ℝ) = v := by
    have := congrArg Complex.im he
    simpa [rectangleCurve,CollarCapacityLower.horizontal] using this
  have hsub : y = v := Subtype.ext hyv
  exact hne (hsub ▸ rfl)

/-- Literal electrode and interior-image conditions on the inverse chart
produce the canonical upper leaf, without a homotopy assumption. -/
theorem chartCurve_upperLeaf (hF : ContinuousOn F (rectangle R a b))
    (hR : 0 < R) (hFinj : InjOn F (rectangle R a b))
    (hfirst : ∀ y ∈ Ioo a b,M.ends (F (CollarCapacityLower.horizontal y 0)))
    (hlast : ∀ y ∈ Ioo a b,
      (F (CollarCapacityLower.horizontal y R)).im = 0 ∧
      (F (CollarCapacityLower.horizontal y R)).re < M.left)
    (hupper : ∀ z : ℂ,z.re ∈ Ioo 0 R → z.im ∈ Ioo a b → 0 < (F z).im)
    (y : Ioo a b) : UpperLeaf M (chartCurve hF hR y) := by
  refine ⟨chartCurve_injective hF hR hFinj y,?_,?_,?_,?_⟩
  · simpa using hfirst y y.2
  · simpa using (hlast y y.2).1
  · simpa using (hlast y y.2).2
  · intro t ht
    apply hupper
    · have hx : R*(t:ℝ) ∈ Ioo 0 R :=
        ⟨mul_pos hR ht.1,by nlinarith [ht.2]⟩
      simpa [rectangleCurve,CollarCapacityLower.horizontal] using hx
    · simpa [rectangleCurve,CollarCapacityLower.horizontal] using y.2

/-- The complete chart foliation is a Borel family of disjoint genuine
upper-half-plane crosscuts between the obligation's own electrodes. -/
theorem chartFamily_upperWave (hF : ContinuousOn F (rectangle R a b))
    (hR : 0 < R) (hFinj : InjOn F (rectangle R a b))
    (hfirst : ∀ y ∈ Ioo a b,M.ends (F (CollarCapacityLower.horizontal y 0)))
    (hlast : ∀ y ∈ Ioo a b,
      (F (CollarCapacityLower.horizontal y R)).im = 0 ∧
      (F (CollarCapacityLower.horizontal y R)).re < M.left)
    (hupper : ∀ z : ℂ,z.re ∈ Ioo 0 R → z.im ∈ Ioo a b → 0 < (F z).im) :
    UpperWave M (chartFamily hF hR) := by
  refine ⟨?_,?_,chartFamily_disjoint hF hR hFinj⟩
  · rw [chartFamily_support]
    exact (rectangle_measurable R a b).image_of_continuousOn_injOn hF hFinj
  · rintro γ ⟨y,rfl⟩
    exact chartCurve_upperLeaf hF hR hFinj hfirst hlast hupper y

end
end ParentWaveRectangleFoliation
