import QuadraticMixedSusceptibility
import QuadraticMonotoneFiberTopology

/-!
# Conditional mixed susceptibility and actual Mandelbrot neighborhoods

The parameter set below is the genuine bounded critical-orbit locus. Compactness
is proved from the existing quadratic escape estimate, and the final criterion
uses a specified continuous monotone quotient onto a locally connected space.
-/

namespace QuadraticMixedSusceptibility

open Set Filter Topology

noncomputable section

/-- The actual bounded critical-orbit locus is the zero locus of the archive's
proved continuous escape function. -/
theorem mandelbrot_eq_zero_escape :
    mandelbrot = {c : ℂ | QuadraticEscape.parameterEscape c = 0} := by
  ext c
  exact (QuadraticEscape.parameterEscape_zero_iff c).symm

/-- Closedness of the actual parameter locus. -/
theorem mandelbrot_isClosed : IsClosed mandelbrot := by
  rw [mandelbrot_eq_zero_escape]
  exact isClosed_eq QuadraticEscape.parameterEscape_continuous continuous_const

/-- A coarse uniform bound suffices for compactness; sharpness is not needed. -/
theorem mandelbrot_norm_le_three {c : ℂ} (hc : c ∈ mandelbrot) : ‖c‖ ≤ 3 := by
  have hz : QuadraticEscape.escape c 0 = 0 :=
    (QuadraticEscape.escape_zero_iff_bounded c 0).mpr hc
  have hbound := QuadraticEscape.escape_zero_orbit_bound c 0 hz 2
  have hsecond : ‖c ^ 2 + c‖ ≤ 1 + ‖c‖ := by
    simpa [QuadraticEscape.orbit] using hbound
  have hnorm : ‖c‖ ^ 2 ≤ ‖c ^ 2 + c‖ + ‖c‖ := by
    calc
      ‖c‖ ^ 2 = ‖(c ^ 2 + c) - c‖ := by
        rw [add_sub_cancel_right, norm_pow]
      _ ≤ ‖c ^ 2 + c‖ + ‖c‖ := norm_sub_le _ _
  nlinarith [norm_nonneg c]

/-- Compactness refers to the actual complex quadratic parameter set. -/
theorem mandelbrot_isCompact : IsCompact mandelbrot := by
  apply (isCompact_closedBall (0 : ℂ) 3).of_isClosed_subset mandelbrot_isClosed
  intro c hc
  simpa only [Metric.mem_closedBall, dist_zero_right] using mandelbrot_norm_le_three hc

instance : CompactSpace mandelbrot :=
  isCompact_iff_compactSpace.mp mandelbrot_isCompact

end
end QuadraticMixedSusceptibility
