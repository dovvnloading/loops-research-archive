import QuadraticCylinderRamification
import TelescopeConformalInverse

/-!
# Canonical analytic inverse branches over a regular target

The source of a branch is the full connected component of the actual
quadratic inverse image through its anchor.  Openness, simple connectivity
and finite postcritical avoidance of the target construct univalence;
neither an inverse function nor a selected source domain is an input.
-/

namespace LoopsQuadraticRegularInverse

open Set Function Filter
open scoped Topology
open QuadraticEscape LoopsSaturatedTelescope LoopsTelescopeRamification
open LoopsQuadraticCylinderCensus LoopsQuadraticCylinderRamification
open LoopsTelescopeConformalInverse

noncomputable section

/-- The full actual pullback component selected by the source anchor. -/
def inverseComponent (c : ℂ) (n : ℕ) (V : Set ℂ) (a : ℂ) : Set ℂ :=
  connectedComponentIn ((orbit c n) ⁻¹' V) a

/-- A single canonical inverse choice on the full selected component.
Only its restriction to the target is used in the theorems below. -/
def inverseBranch (c : ℂ) (n : ℕ) (V : Set ℂ) (a : ℂ) : ℂ → ℂ :=
  Function.invFunOn (orbit c n) (inverseComponent c n V a)

theorem inverseComponent_open (c : ℂ) (n : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (a : ℂ) : IsOpen (inverseComponent c n V a) :=
  (hVo.preimage (quadratic_orbit_continuous c n)).connectedComponentIn

theorem inverseComponent_image (c : ℂ) (n : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V) (a : ℂ)
    (ha : orbit c n a ∈ V) :
    orbit c n '' inverseComponent c n V a = V := by
  simpa only [inverseComponent, orbit_map_eq_iterate] using
    quadratic_global_component_image c n V hVo
      hVc.isPathConnected.isConnected.isPreconnected a
      (by simpa only [orbit_map_eq_iterate] using ha)

theorem inverseComponent_injOn (c : ℂ) (n : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hcrit : ∀ k < n, orbit c k c ∉ V) (a : ℂ)
    (ha : orbit c n a ∈ V) :
    InjOn (orbit c n) (inverseComponent c n V a) := by
  have hcrit' : ∀ k < n, (quad c)^[k] c ∉ V := by
    simpa only [orbit_map_eq_iterate] using hcrit
  simpa only [inverseComponent, orbit_map_eq_iterate] using
    (quadratic_iterate_univalent_component c n V hVo hVc hcrit' a
      (by simpa only [orbit_map_eq_iterate] using ha)).1

private theorem inverseBranch_spec (c : ℂ) (n : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hcrit : ∀ k < n, orbit c k c ∉ V) (a : ℂ)
    (ha : orbit c n a ∈ V) :
    MapsTo (inverseBranch c n V a) V (inverseComponent c n V a) ∧
      LeftInvOn (inverseBranch c n V a) (orbit c n) (inverseComponent c n V a) ∧
      RightInvOn (inverseBranch c n V a) (orbit c n) V ∧
      AnalyticOnNhd ℂ (inverseBranch c n V a) V ∧
      ∀ y ∈ V,
        HasDerivAt (inverseBranch c n V a)
          (deriv (orbit c n) (inverseBranch c n V a y))⁻¹ y ∧
        ConformalAt (inverseBranch c n V a) y := by
  have hCo := inverseComponent_open c n V hVo a
  have hI := inverseComponent_injOn c n V hVo hVc hcrit a ha
  have hE := inverseComponent_image c n V hVo hVc a ha
  have honto : SurjOn (orbit c n) (inverseComponent c n V a) V := by
    intro y hy
    rwa [← hE] at hy
  have hM : MapsTo (inverseBranch c n V a) V (inverseComponent c n V a) :=
    honto.mapsTo_invFunOn
  have hL : LeftInvOn (inverseBranch c n V a) (orbit c n)
      (inverseComponent c n V a) := hI.leftInvOn_invFunOn
  have hR : RightInvOn (inverseBranch c n V a) (orbit c n) V :=
    honto.rightInvOn_invFunOn
  obtain ⟨g, hgM, _, hgR, hgA, hgD⟩ :=
    orbit_conformal_inverse c n (inverseComponent c n V a) V hCo hI hE
  have heq : EqOn g (inverseBranch c n V a) V := by
    intro y hy
    exact hI (hgM hy) (hM hy) ((hgR hy).trans (hR hy).symm)
  refine ⟨hM, hL, hR, hgA.congr hVo heq, ?_⟩
  intro y hy
  have hd := (hgD y hy).1
  rw [heq y hy] at hd
  have hevent : inverseBranch c n V a =ᶠ[𝓝 y] g :=
    (hVo.mem_nhds hy).mono (fun z hz => (heq z hz).symm)
  have hd' := hd.congr_of_eventuallyEq hevent
  have hn : deriv (orbit c n) (inverseBranch c n V a y) ≠ 0 :=
    (orbit_deriv_ne_zero_iff c _ n).mpr
      (orbit_injOn_no_critical_visits c n (inverseComponent c n V a)
        hCo hI _ (hM hy))
  exact ⟨hd', hd'.differentiableAt.conformalAt (by
    rw [hd'.deriv]
    exact inv_ne_zero hn)⟩

/-- Every target point has its inverse in the entire actual component. -/
theorem inverseBranch_mapsTo (c : ℂ) (n : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hcrit : ∀ k < n, orbit c k c ∉ V) (a : ℂ)
    (ha : orbit c n a ∈ V) :
    MapsTo (inverseBranch c n V a) V (inverseComponent c n V a) :=
  (inverseBranch_spec c n V hVo hVc hcrit a ha).1

/-- The inverse recovers every point of its full selected component. -/
theorem inverseBranch_left_inv (c : ℂ) (n : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hcrit : ∀ k < n, orbit c k c ∉ V) (a : ℂ)
    (ha : orbit c n a ∈ V) :
    LeftInvOn (inverseBranch c n V a) (orbit c n) (inverseComponent c n V a) :=
  (inverseBranch_spec c n V hVo hVc hcrit a ha).2.1

/-- The inverse solves the actual iterate equation at every target point. -/
theorem inverseBranch_right_inv (c : ℂ) (n : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hcrit : ∀ k < n, orbit c k c ∉ V) (a : ℂ)
    (ha : orbit c n a ∈ V) :
    RightInvOn (inverseBranch c n V a) (orbit c n) V :=
  (inverseBranch_spec c n V hVo hVc hcrit a ha).2.2.1

/-- Analyticity holds on the entire target, with no supplied branch chart. -/
theorem inverseBranch_analytic (c : ℂ) (n : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hcrit : ∀ k < n, orbit c k c ∉ V) (a : ℂ)
    (ha : orbit c n a ∈ V) :
    AnalyticOnNhd ℂ (inverseBranch c n V a) V :=
  (inverseBranch_spec c n V hVo hVc hcrit a ha).2.2.2.1

/-- The derivative is the reciprocal of the genuine orbit derivative. -/
theorem inverseBranch_hasDerivAt (c : ℂ) (n : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hcrit : ∀ k < n, orbit c k c ∉ V) (a : ℂ)
    (ha : orbit c n a ∈ V) (y : ℂ) (hy : y ∈ V) :
    HasDerivAt (inverseBranch c n V a)
      (deriv (orbit c n) (inverseBranch c n V a y))⁻¹ y :=
  ((inverseBranch_spec c n V hVo hVc hcrit a ha).2.2.2.2 y hy).1

theorem inverseBranch_conformal (c : ℂ) (n : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hcrit : ∀ k < n, orbit c k c ∉ V) (a : ℂ)
    (ha : orbit c n a ∈ V) (y : ℂ) (hy : y ∈ V) :
    ConformalAt (inverseBranch c n V a) y :=
  ((inverseBranch_spec c n V hVo hVc hcrit a ha).2.2.2.2 y hy).2

/-- No point in the full component is omitted by the branch image. -/
theorem inverseBranch_image (c : ℂ) (n : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hcrit : ∀ k < n, orbit c k c ∉ V) (a : ℂ)
    (ha : orbit c n a ∈ V) :
    inverseBranch c n V a '' V = inverseComponent c n V a := by
  apply Subset.antisymm
  · exact (inverseBranch_mapsTo c n V hVo hVc hcrit a ha).image_subset
  · intro x hx
    have hxV : orbit c n x ∈ V :=
      connectedComponentIn_subset ((orbit c n) ⁻¹' V) a hx
    exact ⟨orbit c n x, hxV, inverseBranch_left_inv c n V hVo hVc hcrit a ha hx⟩

/-- The branch is normalized by the source anchor over its actual image. -/
theorem inverseBranch_anchor (c : ℂ) (n : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hcrit : ∀ k < n, orbit c k c ∉ V) (a : ℂ)
    (ha : orbit c n a ∈ V) :
    inverseBranch c n V a (orbit c n a) = a :=
  inverseBranch_left_inv c n V hVo hVc hcrit a ha (mem_connectedComponentIn ha)

/-- A continuous right inverse normalized at the anchor cannot switch
components, so it equals the canonical analytic branch throughout V.
Its values are not assumed to remain in a supplied source sheet. -/
theorem continuous_lift_unique (c : ℂ) (n : ℕ) (V : Set ℂ)
    (hVo : IsOpen V) (hVc : IsSimplyConnected V)
    (hcrit : ∀ k < n, orbit c k c ∉ V) (a : ℂ)
    (ha : orbit c n a ∈ V) (g : ℂ → ℂ) (hg : ContinuousOn g V)
    (hgr : RightInvOn g (orbit c n) V) (hga : g (orbit c n a) = a) :
    EqOn g (inverseBranch c n V a) V := by
  have hconn : IsPreconnected (g '' V) :=
    hVc.isPathConnected.isConnected.isPreconnected.image g hg
  have hhit : a ∈ g '' V := ⟨orbit c n a, ha, hga⟩
  have hsub : g '' V ⊆ (orbit c n) ⁻¹' V := by
    rintro _ ⟨y, hy, rfl⟩
    change orbit c n (g y) ∈ V
    rwa [hgr hy]
  have hrange : g '' V ⊆ inverseComponent c n V a :=
    hconn.subset_connectedComponentIn hhit hsub
  intro y hy
  apply inverseComponent_injOn c n V hVo hVc hcrit a ha
    (hrange ⟨y, hy, rfl⟩) (inverseBranch_mapsTo c n V hVo hVc hcrit a ha hy)
  exact (hgr hy).trans (inverseBranch_right_inv c n V hVo hVc hcrit a ha hy).symm

end
end LoopsQuadraticRegularInverse
