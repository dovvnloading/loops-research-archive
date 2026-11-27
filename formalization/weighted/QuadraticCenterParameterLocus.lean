import QuadraticCenterTrapping
import QuadraticTrappingEscape

/-!
# Actual zero-escape neighborhoods of quadratic centers

Uniform trapping is constructed from the critical return, and bounded
return subsequences are linked to the actual escape potential. Thus the
neighborhood conclusion assumes no basin theorem or parameter-locus chart.
-/

namespace LoopsQuadraticCenterMultiplier

open Filter
open scoped Topology
open LoopsQuadraticTransversality LoopsQuadraticTrappingEscape

noncomputable section

/-- One fixed positive-radius dynamical disk consists entirely of
zero-escape points for every sufficiently nearby parameter. -/
theorem center_uniform_zero_escape_disk (c : ℂ) (n : ℕ)
    (hreturn : orbit c (n+1) = 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ d in 𝓝 c,
      ∀ z : ℂ, ‖z‖ ≤ r → QuadraticEscape.escape d z = 0 := by
  obtain ⟨r, hr, htrap⟩ := center_uniform_return_trapping c n hreturn
  refine ⟨r, hr, ?_⟩
  filter_upwards [htrap] with d hd
  intro z hz
  exact escape_zero_of_return_disk d z (n+1) (by omega) r hz
    (fun w hw => (hd w hw).le)

/-- Every positive critical return has an actual open parameter
neighborhood in the zero-escape locus. No exact-period hypothesis is needed. -/
theorem center_parameter_escape_zero (c : ℂ) (n : ℕ)
    (hreturn : orbit c (n+1) = 0) :
    ∀ᶠ d in 𝓝 c, QuadraticEscape.parameterEscape d = 0 := by
  obtain ⟨r, hr, hzero⟩ := center_uniform_zero_escape_disk c n hreturn
  filter_upwards [hzero] with d hd
  have hcritical := hd 0 (by simpa only [norm_zero] using hr.le)
  rw [QuadraticEscape.parameterEscape_critical, hcritical, mul_zero]

/-- Every quadratic center is an interior point of the actual bounded
critical-orbit locus, expressed by the existing limiting escape potential. -/
theorem center_mem_interior_zero_escape (c : ℂ) (n : ℕ)
    (hreturn : orbit c (n+1) = 0) :
    c ∈ interior {d : ℂ | QuadraticEscape.parameterEscape d = 0} :=
  mem_interior_iff_mem_nhds.mpr (center_parameter_escape_zero c n hreturn)

end
end LoopsQuadraticCenterMultiplier
