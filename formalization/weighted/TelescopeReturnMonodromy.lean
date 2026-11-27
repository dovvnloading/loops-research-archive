import TelescopePathPairing
import SquarePathMonodromy

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
open LoopsSquarePathMonodromy

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

/-- Actual analytic target coordinates for the physical quadratic return.
The square identity concerns the genuine iterate on the whole source. -/
structure ReturnCoordinate (c : ℂ) (a b : ℕ) (A V : Set ℂ) where
  toFun : ℂ → ℂ
  analytic : AnalyticOnNhd ℂ toFun V
  injective : InjOn toFun V
  zero_iff : ∀ y ∈ V, toFun y = 0 ↔ y = orbit c b c
  square : ∀ z ∈ A, toFun (orbit c (a+1+b) z) = (orbit c a z)^2

/-- The regular target loop in its actual critical coordinate. -/
def ReturnCoordinate.path {c : ℂ} {a b : ℕ} {A V : Set ℂ}
    (C : ReturnCoordinate c a b A V) (γ : C(unitInterval, ℂ))
    (hγV : ∀ t, γ t ∈ V) : C(unitInterval, ℂ) :=
  coordinatePath C.toFun V C.analytic γ hγV

/-- The nonvanishing of the transformed path follows from avoidance of
the actual propagated critical value, not an extra geometric premise. -/
theorem ReturnCoordinate.path_ne_zero {c : ℂ} {a b : ℕ} {A V : Set ℂ}
    (C : ReturnCoordinate c a b A V) (γ : C(unitInterval, ℂ))
    (hγV : ∀ t, γ t ∈ V) (hγreg : ∀ t, γ t ≠ orbit c b c)
    (t : unitInterval) : C.path γ hγV t ≠ 0 := by
  intro he
  exact hγreg t ((C.zero_iff (γ t) (hγV t)).mp he)

/-- Integer winding in the univalent suffix coordinate. The integer is
constructed from the exponential covering lift of the actual target path. -/
def ReturnCoordinate.winding {c : ℂ} {a b : ℕ} {A V : Set ℂ}
    (C : ReturnCoordinate c a b A V) (γ : C(unitInterval, ℂ))
    (hγV : ∀ t, γ t ∈ V) (hγreg : ∀ t, γ t ≠ orbit c b c)
    (hγloop : γ 1 = γ 0) : ℤ :=
  windingNumber (C.path γ hγV) (C.path_ne_zero γ hγV hγreg)
    (congrArg C.toFun hγloop)

/-- Exact signed endpoint identity for every full physical return lift.
It retains the actual prefix coordinate and the constructed winding integer. -/
theorem ReturnCoordinate.lift_prefix_endpoint {c : ℂ} {a b : ℕ} {A V : Set ℂ}
    (C : ReturnCoordinate c a b A V) (γ Γ : C(unitInterval, ℂ))
    (hγV : ∀ t, γ t ∈ V) (hγreg : ∀ t, γ t ≠ orbit c b c)
    (hγloop : γ 1 = γ 0) (hΓA : ∀ t, Γ t ∈ A)
    (hlift : ∀ t, orbit c (a+1+b) (Γ t) = γ t) :
    orbit c a (Γ 1) = (-1 : ℂ)^C.winding γ hγV hγreg hγloop *
      orbit c a (Γ 0) := by
  apply square_lift_endpoint (C.path γ hγV) (prefixPath c a Γ)
    (C.path_ne_zero γ hγV hγreg) (congrArg C.toFun hγloop)
  intro t
  change (orbit c a (Γ t))^2 = C.toFun (γ t)
  rw [← hlift t]
  exact (C.square (Γ t) (hΓA t)).symm

/-- Even winding is necessary and sufficient for an arbitrary complete
lift to close in the actual return source. -/
theorem ReturnCoordinate.lift_closed_iff_even {c : ℂ} {a b : ℕ} {A V : Set ℂ}
    (C : ReturnCoordinate c a b A V) (hpinj : InjOn (orbit c a) A)
    (γ Γ : C(unitInterval, ℂ))
    (hγV : ∀ t, γ t ∈ V) (hγreg : ∀ t, γ t ≠ orbit c b c)
    (hγloop : γ 1 = γ 0) (hΓA : ∀ t, Γ t ∈ A)
    (hlift : ∀ t, orbit c (a+1+b) (Γ t) = γ t) :
    Γ 1 = Γ 0 ↔ Even (C.winding γ hγV hγreg hγloop) := by
  have hsquare (t : unitInterval) :
      (prefixPath c a Γ) t ^ 2 = (C.path γ hγV) t := by
    change (orbit c a (Γ t))^2 = C.toFun (γ t)
    rw [← hlift t]
    exact (C.square (Γ t) (hΓA t)).symm
  have hphase := square_lift_closed_iff_even (C.path γ hγV) (prefixPath c a Γ)
    (C.path_ne_zero γ hγV hγreg) (congrArg C.toFun hγloop) hsquare
  change orbit c a (Γ 1) = orbit c a (Γ 0) ↔ _ at hphase
  exact (hpinj.eq_iff (hΓA 1) (hΓA 0)).symm.trans hphase

/-- Odd winding is necessary and sufficient for a complete lift to end
at the canonical deck partner of its starting point. -/
theorem ReturnCoordinate.lift_switched_iff_odd {c : ℂ} {a b : ℕ} {A V : Set ℂ}
    (C : ReturnCoordinate c a b A V) (hpinj : InjOn (orbit c a) A)
    (τ : ℂ → ℂ) (hτmap : MapsTo τ A A)
    (hτprefix : ∀ z ∈ A, orbit c a (τ z) = -(orbit c a z))
    (γ Γ : C(unitInterval, ℂ))
    (hγV : ∀ t, γ t ∈ V) (hγreg : ∀ t, γ t ≠ orbit c b c)
    (hγloop : γ 1 = γ 0) (hΓA : ∀ t, Γ t ∈ A)
    (hlift : ∀ t, orbit c (a+1+b) (Γ t) = γ t) :
    Γ 1 = τ (Γ 0) ↔ Odd (C.winding γ hγV hγreg hγloop) := by
  have hsquare (t : unitInterval) :
      (prefixPath c a Γ) t ^ 2 = (C.path γ hγV) t := by
    change (orbit c a (Γ t))^2 = C.toFun (γ t)
    rw [← hlift t]
    exact (C.square (Γ t) (hΓA t)).symm
  have hphase := square_lift_endpoint_eq_neg_iff_odd
    (C.path γ hγV) (prefixPath c a Γ)
    (C.path_ne_zero γ hγV hγreg) (congrArg C.toFun hγloop) hsquare
  change orbit c a (Γ 1) = -(orbit c a (Γ 0)) ↔ _ at hphase
  rw [← hτprefix (Γ 0) (hΓA 0)] at hphase
  exact (hpinj.eq_iff (hΓA 1) (hτmap (hΓA 0))).symm.trans hphase

/-- All closed-loop deck phases of an actual saturated one-critical
return are determined by one analytic coordinate and one involution,
both constructed from the physical components. No loop or inverse
branch choice is assumed as input. -/
theorem quadratic_return_monodromy (c : ℂ) (a b : ℕ)
    (A B D V : Set ℂ) (x : ℂ) (hx0 : orbit c a x = 0)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hv : orbit c b c ∈ V)
    (hD : D = connectedComponentIn (orbit c b ⁻¹' V) c)
    (hB : B = connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D) 0)
    (hA : A = connectedComponentIn (orbit c a ⁻¹' B) x)
    (hpinj : InjOn (orbit c a) A) (hrinj : InjOn (orbit c b) D) :
    ∃ (C : ReturnCoordinate c a b A V) (τ : ℂ → ℂ),
      AnalyticOnNhd ℂ τ A ∧ MapsTo τ A A ∧
      (∀ z ∈ A, τ (τ z) = z) ∧
      (∀ z ∈ A, orbit c a (τ z) = -(orbit c a z)) ∧
      ∀ (γ : C(unitInterval, ℂ)) (hγV : ∀ t, γ t ∈ V)
        (hγreg : ∀ t, γ t ≠ orbit c b c) (hγloop : γ 1 = γ 0),
        ∀ Γ : C(unitInterval, ℂ), (∀ t, Γ t ∈ A) →
          (∀ t, orbit c (a+1+b) (Γ t) = γ t) →
          (Γ 1 = Γ 0 ↔ Even (C.winding γ hγV hγreg hγloop)) ∧
          (Γ 1 = τ (Γ 0) ↔ Odd (C.winding γ hγV hγreg hγloop)) := by
  obtain ⟨s, hsa, hsi, _, hs0, hsf⟩ :=
    quadratic_return_square_coordinate c a b A B D V x hVo hVc hv hD hB hA hrinj
  let C : ReturnCoordinate c a b A V := ⟨s, hsa, hsi, hs0, hsf⟩
  obtain ⟨τ, hτa, hτmap, hτinv, hτprefix, _⟩ :=
    quadratic_return_deck_paired_paths c a b A B D V x hx0 hVo hVc hv
      hD hB hA hpinj hrinj
  refine ⟨C, τ, hτa, hτmap, hτinv, hτprefix, ?_⟩
  intro γ hγV hγreg hγloop Γ hΓA hlift
  exact ⟨C.lift_closed_iff_even hpinj γ Γ hγV hγreg hγloop hΓA hlift,
    C.lift_switched_iff_odd hpinj τ hτmap hτprefix
      γ Γ hγV hγreg hγloop hΓA hlift⟩

/-- Complete fiber coverage forces any two constructed critical
coordinates to agree throughout the physical target. -/
theorem ReturnCoordinate.eqOn_of_onto {c : ℂ} {a b : ℕ} {A V : Set ℂ}
    (C E : ReturnCoordinate c a b A V)
    (honto : orbit c (a+1+b) '' A = V) : EqOn C.toFun E.toFun V := by
  intro y hy
  rw [← honto] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  exact (C.square z hz).trans (E.square z hz).symm

/-- The actual loop invariant is independent of which conformal
inverse construction produced the critical coordinate. -/
theorem ReturnCoordinate.winding_eq_of_onto {c : ℂ} {a b : ℕ} {A V : Set ℂ}
    (C E : ReturnCoordinate c a b A V)
    (honto : orbit c (a+1+b) '' A = V)
    (γ : C(unitInterval, ℂ)) (hγV : ∀ t, γ t ∈ V)
    (hγreg : ∀ t, γ t ≠ orbit c b c) (hγloop : γ 1 = γ 0) :
    C.winding γ hγV hγreg hγloop = E.winding γ hγV hγreg hγloop := by
  have hp : C.path γ hγV = E.path γ hγV := by
    apply ContinuousMap.ext
    intro t
    exact C.eqOn_of_onto E honto (hγV t)
  unfold ReturnCoordinate.winding
  congr 1

/-- The physical lift exists uniquely from every regular starting point,
and its endpoint is the identity or deck partner according to the exact
winding parity. This combines existence and the phase computation in one
statement, without assuming a candidate lift. -/
theorem quadratic_return_unique_lift_with_monodromy (c : ℂ) (a b : ℕ)
    (A B D V : Set ℂ) (x : ℂ) (hx0 : orbit c a x = 0)
    (hVo : IsOpen V) (hVc : IsPreconnected V) (hv : orbit c b c ∈ V)
    (hD : D = connectedComponentIn (orbit c b ⁻¹' V) c)
    (hB : B = connectedComponentIn ((fun w : ℂ => w^2+c) ⁻¹' D) 0)
    (hA : A = connectedComponentIn (orbit c a ⁻¹' B) x)
    (hpinj : InjOn (orbit c a) A) (hrinj : InjOn (orbit c b) D) :
    ∃ (C : ReturnCoordinate c a b A V) (τ : ℂ → ℂ),
      AnalyticOnNhd ℂ τ A ∧ MapsTo τ A A ∧
      (∀ z ∈ A, τ (τ z) = z) ∧
      ∀ (γ : C(unitInterval, ℂ)) (hγV : ∀ t, γ t ∈ V)
        (hγreg : ∀ t, γ t ≠ orbit c b c) (hγloop : γ 1 = γ 0),
        ∀ z ∈ A, orbit c (a+1+b) z = γ 0 →
          ∃! Γ : C(unitInterval, ℂ),
            (∀ t, Γ t ∈ A) ∧
            (∀ t, orbit c (a+1+b) (Γ t) = γ t) ∧ Γ 0 = z ∧
            Γ 1 = if Even (C.winding γ hγV hγreg hγloop) then z else τ z := by
  obtain ⟨C, τ, hτa, hτmap, hτinv, _, hphase⟩ :=
    quadratic_return_monodromy c a b A B D V x hx0 hVo hVc hv
      hD hB hA hpinj hrinj
  refine ⟨C, τ, hτa, hτmap, hτinv, ?_⟩
  intro γ hγV hγreg hγloop z hz hstart
  obtain ⟨Γ, hΓ, huniq⟩ :=
    quadratic_return_unique_path_lift c a b A B D V x hx0 hVo hVc hv
      hD hB hA hpinj hrinj γ hγV hγreg z hz hstart
  have hparity := hphase γ hγV hγreg hγloop Γ hΓ.1 hΓ.2.1
  refine ⟨Γ, ⟨hΓ.1, hΓ.2.1, hΓ.2.2, ?_⟩, ?_⟩
  · split_ifs with he
    · exact (hparity.1.mpr he).trans hΓ.2.2
    · exact (hparity.2.mpr (Int.not_even_iff_odd.mp he)).trans
        (congrArg τ hΓ.2.2)
  · intro Θ hΘ
    exact huniq Θ ⟨hΘ.1, hΘ.2.1, hΘ.2.2.1⟩

end

end LoopsTelescopeReturnMonodromy
