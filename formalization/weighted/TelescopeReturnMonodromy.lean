import TelescopePathPairing

/-!
# Monodromy coordinates of actual one-critical quadratic returns

The univalent suffix determines an analytic coordinate on the whole
physical target. In this coordinate the full actual return is exactly
the square of the actual prefix. This retains the propagated critical
value and will determine the deck phase of every regular closed path.
-/

namespace LoopsTelescopeReturnMonodromy

open Set Function
open QuadraticEscape LoopsSaturatedTelescope LoopsTelescopeRamification
open LoopsTelescopeCollar LoopsTelescopeConformalInverse
open LoopsTelescopeDeckInvolution LoopsTelescopeUnbranchedCover
open LoopsTelescopePathPairing

noncomputable section

/-- A single analytic target coordinate, defined over the entire actual
target, reduces the selected composite return to the square of its prefix.
The only zero of this coordinate is the propagated critical value. -/
theorem quadratic_return_square_coordinate (c : ℂ) (a b : ℕ)
    (A B D V : Set ℂ) (x : ℂ)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hv : orbit c b c ∈ V)
    (hD : D = connectedComponentIn (orbit c b ⁻¹' V) c)
    (hB : B = connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D) 0)
    (hA : A = connectedComponentIn (orbit c a ⁻¹' B) x)
    (hrinj : InjOn (orbit c b) D) :
    ∃ s : ℂ → ℂ,
      AnalyticOnNhd ℂ s V ∧ InjOn s V ∧ s (orbit c b c) = 0 ∧
      (∀ y ∈ V, s y = 0 ↔ y = orbit c b c) ∧
      (∀ z ∈ A, s (orbit c (a+1+b) z) = (orbit c a z)^2) := by
  have hc : c ∈ D := by
    rw [hD]
    exact mem_connectedComponentIn hv
  have hDo : IsOpen D := by
    rw [hD]
    exact (hVo.preimage (quadratic_orbit_continuous c b)).connectedComponentIn
  have honto : orbit c b '' D = V := by
    rw [hD]
    exact orbit_component_image c b V hVo hVc c hv
  obtain ⟨g, hgmap, hgleft, hgright, hgan, _⟩ :=
    orbit_conformal_inverse c b D V hDo hrinj honto
  let s : ℂ → ℂ := fun y => g y-c
  have hsI : InjOn s V := by
    intro u hu v hv' huv
    have he : g u = g v := by
      change g u-c = g v-c at huv
      linear_combination huv
    calc
      u = orbit c b (g u) := (hgright hu).symm
      _ = orbit c b (g v) := congrArg (orbit c b) he
      _ = v := hgright hv'
  have hs0 : s (orbit c b c) = 0 := by
    change g (orbit c b c)-c = 0
    rw [hgleft hc, sub_self]
  refine ⟨s, (fun y hy => (hgan y hy).sub analyticAt_const), hsI, hs0, ?_, ?_⟩
  · intro y hy
    constructor
    · intro he
      exact hsI hy hv (he.trans hs0.symm)
    · rintro rfl
      exact hs0
  · intro z hz
    have hp : orbit c a z ∈ B := by
      rw [hA] at hz
      exact connectedComponentIn_subset (orbit c a ⁻¹' B) x hz
    have hq : (orbit c a z)^2+c ∈ D := by
      rw [hB] at hp
      exact connectedComponentIn_subset ((fun w : ℂ => w^2+c) ⁻¹' D) 0 hp
    change g (orbit c (a+1+b) z)-c = (orbit c a z)^2
    rw [quadratic_orbit_add c (a+1) b z]
    change g (orbit c b ((orbit c a z)^2+c))-c = (orbit c a z)^2
    rw [hgleft hq]
    ring

/-- The physical critical coordinate transports a regular target path
to a nonzero complex path without an assumed path-space identification. -/
def coordinatePath (s : ℂ → ℂ) (V : Set ℂ)
    (hs : AnalyticOnNhd ℂ s V) (γ : C(unitInterval, ℂ))
    (hγ : ∀ t, γ t ∈ V) : C(unitInterval, ℂ) :=
  ⟨fun t => s (γ t),
    (show ContinuousOn s V from fun y hy =>
      (hs y hy).continuousAt.continuousWithinAt).comp_continuous γ.continuous hγ⟩

/-- The actual prefix of a full return lift is a continuous square-root
lift of its target-coordinate path. -/
def prefixPath (c : ℂ) (a : ℕ) (Γ : C(unitInterval, ℂ)) : C(unitInterval, ℂ) :=
  ⟨fun t => orbit c a (Γ t), (quadratic_orbit_continuous c a).comp Γ.continuous⟩

end

end LoopsTelescopeReturnMonodromy
