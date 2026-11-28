import Mathlib
import QuadraticEscape
import QuadraticMonotoneFiberTopology

/-!
# A nonlinear cohomological half-plane obstruction in the quadratic family

The actual critical-value orbit of `z ↦ z² + c` obeys a linearized
single-parameter spatial derivative recurrence with a *quadratic* remainder.
If the spatial cocycle expands along c, a distinct parameter with bounded
critical orbit must eventually make one normalized nonlinear correction point
into the negative real half-plane.

No mixed two-orbit susceptibility series, orbit metric regularity, or
postcritical parameter path is used. The final theorem proves an actual
pointwise Mandelbrot local-connectivity endpoint from the finite half-plane
criterion and an explicitly provided monotone quotient. Its construction is
not identified with the canonical pinched-disk quotient.
-/

namespace QuadraticCohomologicalCone

open Set Filter Topology

noncomputable section

/-- The bounded-critical-orbit locus of the actual complex quadratic family. -/
def mandelbrot : Set ℂ :=
  {c | ∃ B : ℝ, ∀ n : ℕ, ‖QuadraticEscape.orbit c n 0‖ ≤ B}

/-- The spatial derivative of `f_c^n` at the critical value `c`, with
the empty product normalized to one. Only the orbit of `c` enters. -/
def derivativeCocycle (c : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => derivativeCocycle c n *
      (2 * QuadraticEscape.orbit c (n + 1) 0)

/-- Avoidance of zero after the first critical-value iterate, a condition
making every finite spatial derivative cocycle invertible. -/
def OrbitAvoidsZero (c : ℂ) : Prop :=
  ∀ n : ℕ, QuadraticEscape.orbit c (n + 1) 0 ≠ 0

/-- Finite difference of the actual critical values of two parameters. -/
def displacement (c d : ℂ) (n : ℕ) : ℂ :=
  QuadraticEscape.orbit d (n + 1) 0 -
    QuadraticEscape.orbit c (n + 1) 0

/-- Linearized transport of the true quadratic critical-orbit difference. -/
def normalized (c d : ℂ) (n : ℕ) : ℂ :=
  displacement c d n * (derivativeCocycle c n)⁻¹

/-- The exact nonlinear correction: one parameter displacement and one
quadratic remainder, transported using only the base orbit's cocycle. -/
def correction (c d : ℂ) (n : ℕ) : ℂ :=
  ((d - c) + displacement c d n ^ 2) *
    (derivativeCocycle c (n + 1))⁻¹

/-- The cocycle factors cannot vanish when the base critical orbit avoids
zero. -/
theorem derivativeCocycle_ne_zero (c : ℂ) (h : OrbitAvoidsZero c)
    (n : ℕ) : derivativeCocycle c n ≠ 0 := by
  induction n with
  | zero => norm_num [derivativeCocycle]
  | succ n ih =>
      change derivativeCocycle c n *
          (2 * QuadraticEscape.orbit c (n + 1) 0) ≠ 0
      exact mul_ne_zero ih (mul_ne_zero (by norm_num) (h n))

/-- The nonlinear residual in the true two-parameter quadratic recurrence
is exactly a square: no derivative truncation or omitted error term. -/
theorem displacement_succ (c d : ℂ) (n : ℕ) :
    displacement c d (n + 1) =
      2 * QuadraticEscape.orbit c (n + 1) 0 * displacement c d n +
        (d - c) + displacement c d n ^ 2 := by
  change
      (QuadraticEscape.orbit d (n + 1) 0)^2 + d -
        ((QuadraticEscape.orbit c (n + 1) 0)^2 + c) =
      2 * QuadraticEscape.orbit c (n + 1) 0 *
        (QuadraticEscape.orbit d (n + 1) 0 -
          QuadraticEscape.orbit c (n + 1) 0) +
        (d - c) +
        (QuadraticEscape.orbit d (n + 1) 0 -
          QuadraticEscape.orbit c (n + 1) 0)^2
  ring

/-- Exact finite nonlinear cohomological decomposition
`E_(n+1) = E_n + K_n`. There is no infinite-series hypothesis. -/
theorem normalized_step (c d : ℂ) (h : OrbitAvoidsZero c)
    (n : ℕ) :
    normalized c d (n + 1) = normalized c d n + correction c d n := by
  have hD := derivativeCocycle_ne_zero c h n
  have hX : 2 * QuadraticEscape.orbit c (n + 1) 0 ≠ 0 :=
    mul_ne_zero (by norm_num) (h n)
  unfold normalized correction
  rw [displacement_succ, derivativeCocycle]
  field_simp [hD, hX]
  ring

/-- If every nonlinear correction through a finite horizon has nonnegative
real projection in the displacement direction, normalized transport retains
at least its initial positive real value. -/
theorem normalized_re_ge_one (c d : ℂ) (h : OrbitAvoidsZero c)
    (hne : d ≠ c)
    (hphase : ∀ n : ℕ,
      0 ≤ (((d - c)⁻¹ * correction c d n).re))
    (n : ℕ) :
    (1 : ℝ) ≤ (((d - c)⁻¹ * normalized c d n).re) := by
  induction n with
  | zero =>
      have h0 : normalized c d 0 = d - c := by
        simp [normalized, displacement, derivativeCocycle,
          QuadraticEscape.orbit]
      rw [h0, inv_mul_cancel₀ (sub_ne_zero.mpr hne)]
      norm_num
  | succ n ih =>
      calc
        (1 : ℝ) ≤ (((d - c)⁻¹ * normalized c d n).re) := ih
        _ ≤ (((d - c)⁻¹ * normalized c d (n + 1)).re) := by
          rw [normalized_step c d h n, mul_add, Complex.add_re]
          exact le_add_of_nonneg_right (hphase n)

/-- Two *distinct* parameters of the actual bounded critical-orbit locus
cannot have all their normalized nonlinear corrections in the right half
plane if the base spatial derivative cocycle expands.

The finite correction uses the actual nonlinear square, rather than a
mixed two-orbit inverse product or an asymptotic susceptibility series. -/
theorem exists_negative_cohomological_phase
    (c d : ℂ) (hc : c ∈ mandelbrot) (hd : d ∈ mandelbrot)
    (hne : d ≠ c) (havoid : OrbitAvoidsZero c)
    (hgrow : Tendsto (fun n : ℕ => (derivativeCocycle c n)⁻¹)
      atTop (𝓝 (0 : ℂ))) :
    ∃ n : ℕ, (((d - c)⁻¹ * correction c d n).re) < 0 := by
  by_contra hh
  have hphase : ∀ n : ℕ,
      0 ≤ (((d - c)⁻¹ * correction c d n).re) := by
    intro n
    exact le_of_not_gt (fun hn => hh ⟨n, hn⟩)
  obtain ⟨Bc, hBc⟩ := hc
  obtain ⟨Bd, hBd⟩ := hd
  have hdelta (n : ℕ) : ‖displacement c d n‖ ≤ Bc + Bd := by
    unfold displacement
    calc
      ‖QuadraticEscape.orbit d (n + 1) 0 -
          QuadraticEscape.orbit c (n + 1) 0‖ ≤
          ‖QuadraticEscape.orbit d (n + 1) 0‖ +
            ‖QuadraticEscape.orbit c (n + 1) 0‖ := norm_sub_le _ _
      _ ≤ Bc + Bd := by
        linarith [hBd (n + 1), hBc (n + 1)]
  have hbound (n : ℕ) :
      (1 : ℝ) ≤
        (‖(d - c)⁻¹‖ * (Bc + Bd)) *
          ‖(derivativeCocycle c n)⁻¹‖ := by
    calc
      (1 : ℝ) ≤ (((d - c)⁻¹ * normalized c d n).re) :=
        normalized_re_ge_one c d havoid hne hphase n
      _ ≤ ‖(d - c)⁻¹ * normalized c d n‖ := Complex.re_le_norm _
      _ = (‖(d - c)⁻¹‖ * ‖displacement c d n‖) *
            ‖(derivativeCocycle c n)⁻¹‖ := by
            simp only [normalized, norm_mul]
            ring
      _ ≤ (‖(d - c)⁻¹‖ * (Bc + Bd)) *
            ‖(derivativeCocycle c n)⁻¹‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hdelta n) (norm_nonneg _))
            (norm_nonneg _)
  have hzero : Tendsto
      (fun n : ℕ => (‖(d - c)⁻¹‖ * (Bc + Bd)) *
        ‖(derivativeCocycle c n)⁻¹‖) atTop (𝓝 (0 : ℝ)) := by
    simpa using
      (tendsto_const_nhds (x := ‖(d - c)⁻¹‖ * (Bc + Bd))).mul hgrow.norm
  have hfalse : (1 : ℝ) ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hzero hbound
  norm_num at hfalse

/-- The actual quadratic bounded-orbit locus equals the zero set of its
already proved continuous escape function. -/
theorem mandelbrot_eq_zero_escape :
    mandelbrot = {c : ℂ | QuadraticEscape.parameterEscape c = 0} := by
  ext c
  exact (QuadraticEscape.parameterEscape_zero_iff c).symm

theorem mandelbrot_isClosed : IsClosed mandelbrot := by
  rw [mandelbrot_eq_zero_escape]
  exact isClosed_eq QuadraticEscape.parameterEscape_continuous continuous_const

/-- A coarse bound for the genuine quadratic bounded critical-orbit locus. -/
theorem mandelbrot_norm_le_three {c : ℂ} (hc : c ∈ mandelbrot) :
    ‖c‖ ≤ 3 := by
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

instance : CompactSpace mandelbrot :=
  isCompact_iff_compactSpace.mp mandelbrot_isCompact

/-- An explicitly given quotient of the *actual* Mandelbrot set satisfies
the half-plane barrier at c if every parameter in that fiber has no
negative finite cohomological correction. This hypothesis makes no
reference to susceptibility convergence, a metric comparison of orbits,
or a differentiable path in the fiber. -/
def HalfPlaneFiber {Y : Type*} (q : mandelbrot → Y)
    (c : mandelbrot) : Prop :=
  ∀ d : mandelbrot, q d = q c →
    ∀ n : ℕ, 0 ≤
      ((((d : ℂ) - (c : ℂ))⁻¹ *
        correction (c : ℂ) (d : ℂ) n).re)

/-- A no-phase-reversal connected fiber is a singleton whenever the
base critical orbit has an expanding nonzero derivative cocycle. -/
theorem fiber_eq_singleton_of_halfPlane
    {Y : Type*} (q : mandelbrot → Y)
    (c : mandelbrot)
    (havoid : OrbitAvoidsZero (c : ℂ))
    (hgrow : Tendsto (fun n : ℕ =>
      (derivativeCocycle (c : ℂ) n)⁻¹) atTop (𝓝 (0 : ℂ)))
    (hbarrier : HalfPlaneFiber q c) :
    q ⁻¹' ({q c} : Set Y) = {c} := by
  ext d
  constructor
  · intro hd
    change d = c
    apply Subtype.ext
    by_contra hne
    have hne' : (d : ℂ) ≠ (c : ℂ) := hne
    obtain ⟨n, hn⟩ :=
      exists_negative_cohomological_phase (c : ℂ) (d : ℂ)
        c.property d.property hne' havoid hgrow
    exact (not_lt_of_ge (hbarrier d hd n)) hn
  · intro hd
    change d = c at hd
    subst d
    rfl

/-- Strict Lean endpoint: the half-plane criterion for the actual quadratic
critical orbit supplies relatively open *connected* neighborhoods of c in
the genuine Mandelbrot set, through the classical monotone-quotient lemma. -/
theorem locallyConnectedAt_of_halfPlane
    {Y : Type*} [TopologicalSpace Y] [T2Space Y] [LocallyConnectedSpace Y]
    (q : mandelbrot → Y) (hq : Continuous q)
    (hsurj : Function.Surjective q)
    (hf : ∀ y : Y, IsPreconnected (q ⁻¹' ({y} : Set Y)))
    (c : mandelbrot)
    (havoid : OrbitAvoidsZero (c : ℂ))
    (hgrow : Tendsto (fun n : ℕ =>
      (derivativeCocycle (c : ℂ) n)⁻¹) atTop (𝓝 (0 : ℂ)))
    (hbarrier : HalfPlaneFiber q c) :
    ∀ U ∈ 𝓝 c, ∃ V : Set mandelbrot,
      V ⊆ U ∧ IsOpen V ∧ c ∈ V ∧ IsConnected V := by
  exact LoopsQuadraticMonotoneFiberTopology.connected_open_basis_of_singleton_fiber
    q hq hsurj hf c
    (fiber_eq_singleton_of_halfPlane q c havoid hgrow hbarrier)

#print axioms displacement_succ
#print axioms normalized_step
#print axioms exists_negative_cohomological_phase
#print axioms fiber_eq_singleton_of_halfPlane
#print axioms locallyConnectedAt_of_halfPlane

end
end QuadraticCohomologicalCone
