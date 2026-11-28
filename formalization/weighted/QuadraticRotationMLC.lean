import QuadraticEscape
import QuadraticRotationRigidity
import QuadraticMonotoneFiberTopology

/-!
# Quarter-turn rigidity and local connectivity of the actual Mandelbrot locus

The Mandelbrot set below is the locus of bounded critical orbits for `z^2 + c`.
The dynamical criterion requires a continuous injective intertwiner of that
quadratic and the fixed quarter-turn for every parameter in the specified fiber.
Parameter equality is proved in `QuadraticRotationRigidity`, not assumed here.

The quotient is an explicit continuous monotone surjection to a Hausdorff locally
connected space. No construction of the canonical combinatorial quotient, and
no automatic existence of the required intertwiners, is claimed.
-/

namespace LoopsQuadraticRotationMLC

open Set Filter Topology
open LoopsQuadraticRotationRigidity

noncomputable section

/-- The actual bounded-critical-orbit Mandelbrot set. -/
def mandelbrot : Set ℂ :=
  {c | ∃ B : ℝ, ∀ n : ℕ, ‖QuadraticEscape.orbit c n 0‖ ≤ B}

theorem mandelbrot_eq_zero_escape :
    mandelbrot = {c : ℂ | QuadraticEscape.parameterEscape c = 0} := by
  ext c
  exact (QuadraticEscape.parameterEscape_zero_iff c).symm

theorem mandelbrot_isClosed : IsClosed mandelbrot := by
  rw [mandelbrot_eq_zero_escape]
  exact isClosed_eq QuadraticEscape.parameterEscape_continuous continuous_const

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

theorem mandelbrot_isCompact : IsCompact mandelbrot := by
  apply (isCompact_closedBall (0 : ℂ) 3).of_isClosed_subset mandelbrot_isClosed
  intro c hc
  simpa only [Metric.mem_closedBall, dist_zero_right] using mandelbrot_norm_le_three hc

instance : CompactSpace mandelbrot := isCompact_iff_compactSpace.mp mandelbrot_isCompact

/-- Simultaneous intertwining of one quadratic and the standard quarter-turn.
The map is not assumed holomorphic, quasiconformal, or surjective. -/
def QuarterTurnConjugates (c d : ℂ) : Prop :=
  ∃ h : ℂ → ℂ, Continuous h ∧ Function.Injective h ∧
    (∀ z : ℂ, h (z ^ 2 + c) = (h z) ^ 2 + d) ∧
    (∀ z : ℂ, h (Complex.I * z) = Complex.I * h z)

theorem parameter_eq_of_quarterTurnConjugates {c d : ℂ}
    (h : QuarterTurnConjugates c d) : c = d := by
  obtain ⟨h, hcont, hinj, hquad, hrot⟩ := h
  exact parameter_eq_of_quarter_turn_conjugacy h c d hcont hinj hquad hrot

theorem quarterTurnConjugates_refl (c : ℂ) : QuarterTurnConjugates c c := by
  exact ⟨id, continuous_id, Function.injective_id, fun _ => rfl, fun _ => rfl⟩

/-- The extra dynamical-coordinate condition on a specified actual parameter fiber. -/
def QuarterTurnFiber {Y : Type*} (q : mandelbrot → Y) (c : mandelbrot) : Prop :=
  ∀ d : mandelbrot, q d = q c → QuarterTurnConjugates (c : ℂ) (d : ℂ)

/-- The new quadratic rigidity theorem supplies the singleton fiber conclusion. -/
theorem fiber_eq_singleton_of_quarter_turn
    {Y : Type*} (q : mandelbrot → Y) (c : mandelbrot)
    (hrot : QuarterTurnFiber q c) : q ⁻¹' ({q c} : Set Y) = {c} := by
  ext d
  constructor
  · intro hd
    change q d = q c at hd
    have hcd : (c : ℂ) = (d : ℂ) := parameter_eq_of_quarterTurnConjugates (hrot d hd)
    exact Subtype.ext hcd.symm
  · intro hd
    change d = c at hd
    subst d
    rfl

/-- A nontrivial fiber necessarily loses the simultaneous quarter-turn conjugacy. -/
theorem nontrivial_fiber_obstructs_quarter_turn
    {Y : Type*} (q : mandelbrot → Y) (c : mandelbrot)
    (hnt : q ⁻¹' ({q c} : Set Y) ≠ {c}) :
    ∃ d : mandelbrot, q d = q c ∧
      ¬ QuarterTurnConjugates (c : ℂ) (d : ℂ) := by
  classical
  by_contra h
  apply hnt
  apply fiber_eq_singleton_of_quarter_turn q c
  intro d hd
  by_contra hn
  exact h ⟨d, hd, hn⟩

/-- The MLC endpoint: every relative neighborhood in the actual Mandelbrot set
contains a connected relatively open neighborhood of the parameter. -/
theorem locallyConnectedAt_of_quarter_turn
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] [LocallyConnectedSpace Y]
    (q : mandelbrot → Y) (hq : Continuous q) (hsurj : Function.Surjective q)
    (hf : ∀ y : Y, IsPreconnected (q ⁻¹' {y}))
    (c : mandelbrot) (hrot : QuarterTurnFiber q c) :
    ∀ U ∈ 𝓝 c, ∃ V : Set mandelbrot,
      V ⊆ U ∧ IsOpen V ∧ c ∈ V ∧ IsConnected V := by
  exact LoopsQuadraticMonotoneFiberTopology.connected_open_basis_of_singleton_fiber
    q hq hsurj hf c (fiber_eq_singleton_of_quarter_turn q c hrot)

end
end LoopsQuadraticRotationMLC
