import ParentWavePhysicalBoundary

/-!
# Unconditional existence of the actual closed elliptic primitive

The primitive, its finite extension, and its infinite-end limit are
constructed from the ordered real marks.  They are not hypotheses left
to the caller of the canonical width calculation.
-/

namespace ParentWaveEllipticExistence

open Set Complex
open ParentWaveElliptic ParentWaveEllipticBoundary ParentWaveEllipticImage
open ParentWaveRectangle ParentWaveBoundaryInverse

noncomputable section

/-- The complete analytic data exist for every pair of distinct positive
branch locations.  The derivative is the literal elliptic differential. -/
theorem exists_closed_primitive (B C : ℝ) (hB : 0 < B) (hBC : B < C) :
    ∃ E : ℂ → ℂ, ∃ L : ℂ,
      (∀ t ∈ quadrant, HasDerivAt E (differential B C t) t) ∧
      ContinuousOn E (closure quadrant) ∧
      UniformLimitAtInfinity E (closure quadrant) L := by
  obtain ⟨G,hG⟩ := exists_primitive B C
  obtain ⟨E,hE,hGE⟩ := exists_continuous_closed_quadrant_extension B C hB hBC hG
  obtain ⟨L,hL⟩ := primitive_uniform_limit_at_infinity B C hG
  have hlim : UniformLimitAtInfinity E quadrant L := by
    intro ε hε
    obtain ⟨R,_,hR⟩ := hL ε hε
    refine ⟨R,?_⟩
    intro z hz hzR
    rw [← hGE hz]
    exact hR z hz hzR
  exact ⟨E,L,extension_hasDerivAt B C hG hGE,hE,uniformLimitAtInfinity_closure hE hlim⟩

end
end ParentWaveEllipticExistence
