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

/-- The complex parameters in a fiber of the specified map on the actual
Mandelbrot set. The map is supplied explicitly; this definition does not
identify its fibers with any canonical combinatorial equivalence relation. -/
def planeFiber {Y : Type*} (q : mandelbrot → Y) (c : mandelbrot) : Set ℂ :=
  Subtype.val '' (q ⁻¹' ({q c} : Set Y))

/-- Ordinary uniform convergence of the mixed complex series on a connected
fiber, with nonzero diagonal limit, makes that actual parameter fiber a
singleton. No absolute summability or open parameter neighborhood is assumed. -/
theorem monotone_fiber_eq_singleton_of_mixed_susceptibility
    {Y : Type*} (q : mandelbrot → Y)
    (hf : ∀ y : Y, IsPreconnected (q ⁻¹' {y}))
    (c : mandelbrot) (L : ℂ → ℂ)
    (hnon : ∀ d ∈ planeFiber q c, Nonvanishing (c : ℂ) d)
    (hconv : TendstoUniformlyOn
      (fun n d => partialSum (c : ℂ) d n) L atTop (planeFiber q c))
    (hLc : L (c : ℂ) ≠ 0) :
    q ⁻¹' ({q c} : Set Y) = {c} := by
  have hF : IsPreconnected (planeFiber q c) :=
    (hf (q c)).image Subtype.val continuous_subtype_val.continuousOn
  have hFM : planeFiber q c ⊆ mandelbrot := by
    rintro _ ⟨d, _, rfl⟩
    exact d.property
  have hcF : (c : ℂ) ∈ planeFiber q c := ⟨c, rfl, rfl⟩
  have hplane : planeFiber q c = {(c : ℂ)} :=
    connected_set_eq_singleton (planeFiber q c) (c : ℂ) L
      hF hFM hcF hnon hconv hLc
  ext d
  constructor
  · intro hd
    change d = c
    apply Subtype.ext
    have hdF : (d : ℂ) ∈ planeFiber q c := ⟨d, hd, rfl⟩
    rw [hplane] at hdF
    exact hdF
  · intro hd
    change d = c at hd
    subst d
    rfl

/-- The mixed-susceptibility condition implies actual pointwise local
connectivity of the bounded quadratic critical-orbit locus, whenever the
specified map is a continuous monotone surjection to a Hausdorff locally
connected space. The conclusion is an open connected neighborhood basis
in the subspace topology of the genuine Mandelbrot set. -/
theorem locallyConnectedAt_of_mixed_susceptibility
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] [LocallyConnectedSpace Y]
    (q : mandelbrot → Y) (hq : Continuous q) (hsurj : Function.Surjective q)
    (hf : ∀ y : Y, IsPreconnected (q ⁻¹' {y}))
    (c : mandelbrot) (L : ℂ → ℂ)
    (hnon : ∀ d ∈ planeFiber q c, Nonvanishing (c : ℂ) d)
    (hconv : TendstoUniformlyOn
      (fun n d => partialSum (c : ℂ) d n) L atTop (planeFiber q c))
    (hLc : L (c : ℂ) ≠ 0) :
    ∀ U ∈ 𝓝 c, ∃ V : Set mandelbrot,
      V ⊆ U ∧ IsOpen V ∧ c ∈ V ∧ IsConnected V := by
  exact LoopsQuadraticMonotoneFiberTopology.connected_open_basis_of_singleton_fiber
    q hq hsurj hf c
    (monotone_fiber_eq_singleton_of_mixed_susceptibility q hf c L hnon hconv hLc)

end
end QuadraticMixedSusceptibility
