import ParentWavePhysicalBoundary
import ParentWaveRectangleTransport

/-!
# The actual physical inverse on the complete vertical-side strip

The inverse first undoes the translated elliptic primitive in the closed
quadrant, then applies the literal physical coordinate `t²+a`. Uniform
control at infinity gives continuity up to both electrode sides. This is
the extension used by the full canonical parent-wave foliation.
-/

namespace ParentWavePhysicalInverse

open Set Function Complex Filter MarkedSlitTransport
open ParentWaveElliptic ParentWaveEllipticSides ParentWaveEllipticImage
open ParentWaveEllipticClosed ParentWavePhysicalChart ParentWaveRectangle
open ParentWaveBoundaryInverse ParentWaveRectangleModulus ParentWaveRectangleTransport

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- The complete strip includes both electrode sides but omits the
horizontal sides and their finite or infinite corner values. -/
def strip (B C : ℝ) (E : ℂ → ℂ) : Set ℂ :=
  ParentWaveRectangleModulus.rectangle (width B E) (-height B C E) 0

/-- The inverse of the actual primitive, with exactly its normalization. -/
def quadrantInverse (B : ℝ) (E : ℂ → ℂ) (w : ℂ) : ℂ :=
  invFunOn E (closure quadrant) (w + offset B E)

/-- Returning to the physical marked plane is the original square map. -/
def physicalInverse (a B : ℝ) (E : ℂ → ℂ) (w : ℂ) : ℂ :=
  (quadrantInverse B E w)^2 + (a : ℂ)

/-- Every point of the vertical-side strip lies in the finite closed
image of the unnormalized quadrant primitive. -/
theorem shifted_strip_mem_closed_rectangle (B C : ℝ) (hB : 0 < B) (hBC : B < C)
    {E : ℂ → ℂ} {L : ℂ}
    (hE : ∀ t ∈ quadrant, HasDerivAt E (differential B C t) t)
    (hc : ContinuousOn E (closure quadrant))
    (hinfty : UniformLimitAtInfinity E (closure quadrant) L)
    {w : ℂ} (hw : w ∈ strip B C E) :
    w + offset B E ∈ closure (ParentWaveEllipticImage.rectangle B C E) \ {L} := by
  have hdim := dimensions_pos B C hB hBC hE hc
  have hcorner := infinity_corner B C hB hBC hE hc (fun _ _ => rfl) hinfty
  have hwx : 0 ≤ w.re ∧ w.re ≤ width B E := hw.1
  have hwy : -height B C E < w.im ∧ w.im < 0 := hw.2
  have hx : (w + offset B E).re ∈
      Icc (E (Real.sqrt B : ℂ)).re (E 0).re := by
    simp only [Complex.add_re,offset]
    dsimp [width] at hwx
    constructor <;> linarith
  have hy : (E (Real.sqrt C : ℂ)).im < (w + offset B E).im ∧
      (w + offset B E).im < (E (Real.sqrt B : ℂ)).im := by
    simp only [Complex.add_im,offset]
    dsimp [height] at hwy
    constructor <;> linarith
  refine ⟨?_,?_⟩
  · have hxcl : (w + offset B E).re ∈
        closure (Ioo (E (Real.sqrt B : ℂ)).re (E 0).re) := by
      rw [closure_Ioo (sub_pos.mp hdim.1).ne]
      exact hx
    have hmap : MapsTo (CollarCapacityLower.horizontal (w+offset B E).im)
        (Ioo (E (Real.sqrt B : ℂ)).re (E 0).re)
        (ParentWaveEllipticImage.rectangle B C E) := by
      intro x hx'
      simpa [ParentWaveEllipticImage.rectangle,CollarCapacityLower.horizontal] using
        And.intro hx'.1 (And.intro hx'.2 hy)
    have him := map_mem_closure (CollarCapacityLower.horizontal_lipschitz _).continuous hxcl hmap
    have heq : CollarCapacityLower.horizontal (w+offset B E).im (w+offset B E).re =
        w+offset B E := by
      apply Complex.ext <;> simp [CollarCapacityLower.horizontal]
    rwa [heq] at him
  · intro he
    have heq : w + offset B E = L := mem_singleton_iff.mp he
    have him := congrArg Complex.im heq
    rw [hcorner.2] at him
    linarith [hy.1]

/-- Literal right-inverse membership uses the finite boundary coverage,
not a choice of an unrelated conformal model. -/
theorem quadrantInverse_mem (B C : ℝ) (hB : 0 < B) (hBC : B < C)
    {E : ℂ → ℂ} {L : ℂ}
    (hE : ∀ t ∈ quadrant, HasDerivAt E (differential B C t) t)
    (hc : ContinuousOn E (closure quadrant))
    (hinfty : UniformLimitAtInfinity E (closure quadrant) L)
    {w : ℂ} (hw : w ∈ strip B C E) : quadrantInverse B E w ∈ closure quadrant :=
  invFunOn_mem (closed_rectangle_covered B C hB hBC hE hc (fun _ _ => rfl) hinfty
    (shifted_strip_mem_closed_rectangle B C hB hBC hE hc hinfty hw))

theorem quadrantInverse_apply (B C : ℝ) (hB : 0 < B) (hBC : B < C)
    {E : ℂ → ℂ} {L : ℂ}
    (hE : ∀ t ∈ quadrant, HasDerivAt E (differential B C t) t)
    (hc : ContinuousOn E (closure quadrant))
    (hinfty : UniformLimitAtInfinity E (closure quadrant) L)
    {w : ℂ} (hw : w ∈ strip B C E) :
    E (quadrantInverse B E w) = w + offset B E :=
  invFunOn_eq (closed_rectangle_covered B C hB hBC hE hc (fun _ _ => rfl) hinfty
    (shifted_strip_mem_closed_rectangle B C hB hBC hE hc hinfty hw))

/-- The actual inverse is continuous through both vertical-side ends
of every horizontal leaf. -/
theorem quadrantInverse_continuous (B C : ℝ) (hB : 0 < B) (hBC : B < C)
    {E : ℂ → ℂ} {L : ℂ}
    (hE : ∀ t ∈ quadrant, HasDerivAt E (differential B C t) t)
    (hc : ContinuousOn E (closure quadrant))
    (hinfty : UniformLimitAtInfinity E (closure quadrant) L) :
    ContinuousOn (quadrantInverse B E) (strip B C E) := by
  have hi := extension_injective_closed B C hB hBC hE hc (fun _ _ => rfl) hinfty
  have hcov := closed_rectangle_covered B C hB hBC hE hc (fun _ _ => rfl) hinfty
  have hcont := continuousOn_invFunOn_of_uniformLimit isClosed_closure hc hi hinfty hcov
    (by simp : L ∉ closure (ParentWaveEllipticImage.rectangle B C E) \ {L})
  exact hcont.comp (continuous_id.add_const (offset B E)).continuousOn
    (fun w hw => shifted_strip_mem_closed_rectangle B C hB hBC hE hc hinfty hw)

/-- Squaring the actual quadrant inverse is continuous on the full
closed-vertical strip used by the canonical foliation. -/
theorem physicalInverse_continuous (a B C : ℝ) (hB : 0 < B) (hBC : B < C)
    {E : ℂ → ℂ} {L : ℂ}
    (hE : ∀ t ∈ quadrant, HasDerivAt E (differential B C t) t)
    (hc : ContinuousOn E (closure quadrant))
    (hinfty : UniformLimitAtInfinity E (closure quadrant) L) :
    ContinuousOn (physicalInverse a B E) (strip B C E) :=
  ((quadrantInverse_continuous B C hB hBC hE hc hinfty).pow 2).add_const (a:ℂ)

theorem physicalInverse_mem_closed (a B C : ℝ) (hB : 0 < B) (hBC : B < C)
    {E : ℂ → ℂ} {L : ℂ}
    (hE : ∀ t ∈ quadrant, HasDerivAt E (differential B C t) t)
    (hc : ContinuousOn E (closure quadrant))
    (hinfty : UniformLimitAtInfinity E (closure quadrant) L)
    {w : ℂ} (hw : w ∈ strip B C E) :
    physicalInverse a B E w ∈ closedUpperHalfPlane :=
  square_translate_mem_closed a (quadrantInverse_mem B C hB hBC hE hc hinfty hw)

/-- The physical inverse is a literal right inverse of the normalized
elliptic chart at every point on both electrode sides. -/
theorem forward_physicalInverse (a B C : ℝ) (hB : 0 < B) (hBC : B < C)
    {E : ℂ → ℂ} {L : ℂ}
    (hE : ∀ t ∈ quadrant, HasDerivAt E (differential B C t) t)
    (hc : ContinuousOn E (closure quadrant))
    (hinfty : UniformLimitAtInfinity E (closure quadrant) L)
    {w : ℂ} (hw : w ∈ strip B C E) :
    forward a B E (physicalInverse a B E w) = w := by
  unfold forward physicalInverse
  rw [add_sub_cancel_right,sqrt_square_closed
    (quadrantInverse_mem B C hB hBC hE hc hinfty hw),
    quadrantInverse_apply B C hB hBC hE hc hinfty hw,add_sub_cancel_right]

/-- Complete-strip injectivity follows from the proved right inverse. -/
theorem physicalInverse_injective (a B C : ℝ) (hB : 0 < B) (hBC : B < C)
    {E : ℂ → ℂ} {L : ℂ}
    (hE : ∀ t ∈ quadrant, HasDerivAt E (differential B C t) t)
    (hc : ContinuousOn E (closure quadrant))
    (hinfty : UniformLimitAtInfinity E (closure quadrant) L) :
    InjOn (physicalInverse a B E) (strip B C E) := by
  intro z hz w hw he
  have h := congrArg (forward a B E) he
  simpa only [forward_physicalInverse a B C hB hBC hE hc hinfty hz,
    forward_physicalInverse a B C hB hBC hE hc hinfty hw] using h

/-- The open normalized rectangle is contained in the complete strip. -/
theorem openRectangle_subset_strip (B C : ℝ) (E : ℂ → ℂ) :
    openRectangle (width B E) (height B C E) ⊆ strip B C E := by
  intro w hw
  exact ⟨⟨hw.1.1.le,hw.1.2.le⟩,hw.2⟩

/-- On the open rectangle the boundary-continuous physical inverse is
exactly the inverse of the literal conformal chart. -/
theorem physicalInverse_eq_chart_inverse (a b c : ℝ) (hab : a < b) (hbc : b < c)
    {E : ℂ → ℂ} {L : ℂ}
    (hE : ∀ t ∈ quadrant, HasDerivAt E (differential (b-a) (c-a) t) t)
    (hc : ContinuousOn E (closure quadrant))
    (hinfty : UniformLimitAtInfinity E (closure quadrant) L) :
    EqOn (physicalInverse a (b-a) E) (conformalChart a b c E hE).homeomorph.symm
      (openRectangle (width (b-a) E) (height (b-a) (c-a) E)) := by
  intro w hw
  have hB := sub_pos.mpr hab
  have hBC := sub_lt_sub_right hbc a
  have hws := openRectangle_subset_strip (b-a) (c-a) E hw
  have htarget : w ∈ (conformalChart a b c E hE).homeomorph.target := by
    rwa [conformalChart_target a b c hab hbc hE hc hinfty]
  have hinverse : (conformalChart a b c E hE).homeomorph.symm w ∈ upperHalfPlane :=
    (conformalChart a b c E hE).homeomorph.map_target htarget
  apply forward_injective_closed a b c hab hbc hE hc hinfty
    (physicalInverse_mem_closed a (b-a) (c-a) hB hBC hE hc hinfty hws)
    (show 0 ≤ ((conformalChart a b c E hE).homeomorph.symm w).im from
      le_of_lt hinverse)
  exact (forward_physicalInverse a (b-a) (c-a) hB hBC hE hc hinfty hws).trans
    ((conformalChart a b c E hE).homeomorph.right_inv htarget).symm

/-- Every interior point of the actual foliation lies strictly above
the physical slit. -/
theorem physicalInverse_upper (a b c : ℝ) (hab : a < b) (hbc : b < c)
    {E : ℂ → ℂ} {L : ℂ}
    (hE : ∀ t ∈ quadrant, HasDerivAt E (differential (b-a) (c-a) t) t)
    (hc : ContinuousOn E (closure quadrant))
    (hinfty : UniformLimitAtInfinity E (closure quadrant) L)
    {w : ℂ} (hw : w ∈ openRectangle (width (b-a) E) (height (b-a) (c-a) E)) :
    0 < (physicalInverse a (b-a) E w).im := by
  rw [physicalInverse_eq_chart_inverse a b c hab hbc hE hc hinfty hw]
  apply (conformalChart a b c E hE).homeomorph.map_target
  rwa [conformalChart_target a b c hab hbc hE hc hinfty]

/-- The source of the inverse conformal chart is exactly the normalized
open rectangle used by the complete horizontal foliation. -/
theorem inverse_chart_source (a b c : ℝ) (hab : a < b) (hbc : b < c)
    {E : ℂ → ℂ} {L : ℂ}
    (hE : ∀ t ∈ quadrant, HasDerivAt E (differential (b-a) (c-a) t) t)
    (hc : ContinuousOn E (closure quadrant))
    (hinfty : UniformLimitAtInfinity E (closure quadrant) L) :
    (ParentWaveConformal.inverse (conformalChart a b c E hE)).homeomorph.source =
      rectangleInterior (width (b-a) E) (-height (b-a) (c-a) E) 0 :=
  conformalChart_target a b c hab hbc hE hc hinfty

/-- The initial endpoint of each actual inverse-image leaf lies in the
original marked ending atom. -/
theorem physicalInverse_ending_atom (M : Marking)
    {E : ℂ → ℂ} {L : ℂ}
    (hE : ∀ t ∈ quadrant, HasDerivAt E
      (differential (M.first-M.left) (M.second-M.left) t) t)
    (hc : ContinuousOn E (closure quadrant))
    (hinfty : UniformLimitAtInfinity E (closure quadrant) L)
    {y : ℝ} (hy : y ∈ Ioo (-height (M.first-M.left) (M.second-M.left) E) 0) :
    M.ends (physicalInverse M.left (M.first-M.left) E
      (CollarCapacityLower.horizontal y 0)) := by
  have hB := sub_pos.mpr M.left_lt_first
  have hBC := sub_lt_sub_right M.first_lt_second M.left
  have hR := (dimensions_pos (M.first-M.left) (M.second-M.left) hB hBC hE hc).1
  have hw : CollarCapacityLower.horizontal y 0 ∈ strip (M.first-M.left) (M.second-M.left) E := by
    simpa [strip,ParentWaveRectangleModulus.rectangle,CollarCapacityLower.horizontal] using
      And.intro (show (0:ℝ) ∈ Icc 0 (width (M.first-M.left) E) from ⟨le_rfl,hR.le⟩) hy
  have heq := forward_physicalInverse M.left (M.first-M.left) (M.second-M.left)
    hB hBC hE hc hinfty hw
  apply ParentWavePhysicalBoundary.forward_zero_side_preimage M.left M.first M.second
    M.left_lt_first M.first_lt_second hE hc hinfty
    (physicalInverse_mem_closed M.left (M.first-M.left) (M.second-M.left) hB hBC hE hc hinfty hw)
  · rw [heq]
    simp [CollarCapacityLower.horizontal]
  · rw [heq]
    simpa [CollarCapacityLower.horizontal] using hy

/-- The terminal endpoint lies on the original exterior left ray. -/
theorem physicalInverse_left_ray (M : Marking)
    {E : ℂ → ℂ} {L : ℂ}
    (hE : ∀ t ∈ quadrant, HasDerivAt E
      (differential (M.first-M.left) (M.second-M.left) t) t)
    (hc : ContinuousOn E (closure quadrant))
    (hinfty : UniformLimitAtInfinity E (closure quadrant) L)
    {y : ℝ} (hy : y ∈ Ioo (-height (M.first-M.left) (M.second-M.left) E) 0) :
    (physicalInverse M.left (M.first-M.left) E
      (CollarCapacityLower.horizontal y (width (M.first-M.left) E))).im = 0 ∧
    (physicalInverse M.left (M.first-M.left) E
      (CollarCapacityLower.horizontal y (width (M.first-M.left) E))).re < M.left := by
  have hB := sub_pos.mpr M.left_lt_first
  have hBC := sub_lt_sub_right M.first_lt_second M.left
  have hR := (dimensions_pos (M.first-M.left) (M.second-M.left) hB hBC hE hc).1
  have hw : CollarCapacityLower.horizontal y (width (M.first-M.left) E) ∈
      strip (M.first-M.left) (M.second-M.left) E := by
    simpa [strip,ParentWaveRectangleModulus.rectangle,CollarCapacityLower.horizontal] using
      And.intro (show width (M.first-M.left) E ∈ Icc 0 (width (M.first-M.left) E) from
        ⟨hR.le,le_rfl⟩) hy
  have heq := forward_physicalInverse M.left (M.first-M.left) (M.second-M.left)
    hB hBC hE hc hinfty hw
  apply ParentWavePhysicalBoundary.forward_width_side_preimage M.left M.first M.second
    M.left_lt_first M.first_lt_second hE hc hinfty
    (physicalInverse_mem_closed M.left (M.first-M.left) (M.second-M.left) hB hBC hE hc hinfty hw)
  · rw [heq]
    simp [CollarCapacityLower.horizontal]
  · rw [heq]
    simpa [CollarCapacityLower.horizontal] using hy

end
end ParentWavePhysicalInverse
