import QuadraticUnivalentNeighborhood
import TelescopeCollarRecognition
import QuadraticCylinderRamification
import TelescopeConformalInverse

/-!
# Open univalent selected collars from actual compact cores

The hypotheses concern the physical quadratic iterate on one compact
selected component. Open-domain injectivity, compact closure, properness,
and target surjectivity are conclusions. A single margin works for all
sufficiently close open targets, inside any prescribed ambient neighborhood.
-/

namespace LoopsTelescopeUnivalentCollars

open Set Function Metric
open QuadraticEscape LoopsSaturatedTelescope LoopsTelescopeRamification
open LoopsTelescopeCollar LoopsQuadraticUnivalentNeighborhood
open LoopsQuadraticCylinderRamification
open LoopsTelescopeConformalInverse

/-- Exact criterion for extending compact injectivity to an open domain.
The critical encounters are checked strictly before the terminal time. -/
theorem compact_univalent_neighborhood_iff (c : ℂ) (n : ℕ) (C : Set ℂ)
    (hC : IsCompact C) :
    (∃ U : Set ℂ, IsOpen U ∧ C ⊆ U ∧ InjOn (orbit c n) U) ↔
      InjOn (orbit c n) C ∧ (∀ x ∈ C, ∀ j < n, orbit c j x ≠ 0) := by
  constructor
  · rintro ⟨U, hU, hCU, hI⟩
    exact ⟨hI.mono hCU, fun x hx =>
      orbit_injOn_no_critical_visits c n U hU hI x (hCU hx)⟩
  · rintro ⟨hI, hcrit⟩
    exact quadratic_compact_univalent_neighborhood c n C hC hI hcrit

/-- Every sufficiently close open target has its selected pullback
compactly inside the prescribed ambient set, and the actual iterate
remains injective even on the pullback's closure. -/
theorem selected_univalent_collar_margin (c : ℂ) (n : ℕ)
    (K W : Set ℂ) (x : ℂ) (hK : IsCompact K) (hx : orbit c n x ∈ K)
    (hW : IsOpen W) (hCW : connectedComponentIn (orbit c n ⁻¹' K) x ⊆ W)
    (hI : InjOn (orbit c n) (connectedComponentIn (orbit c n ⁻¹' K) x))
    (hcrit : ∀ z ∈ connectedComponentIn (orbit c n ⁻¹' K) x,
      ∀ j < n, orbit c j z ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ V : Set ℂ, IsOpen V → K ⊆ V →
      V ⊆ cthickening δ K →
      let U := connectedComponentIn (orbit c n ⁻¹' V) x
      IsOpen U ∧ connectedComponentIn (orbit c n ⁻¹' K) x ⊆ U ∧
        IsCompact (closure U) ∧ closure U ⊆ W ∧ InjOn (orbit c n) (closure U) := by
  let C := connectedComponentIn (orbit c n ⁻¹' K) x
  have hp := orbit_proper c n
  have hC : IsCompact C := proper_component_compact (orbit c n) hp K hK x hx
  obtain ⟨A, hA, hCA, hIA⟩ :=
    quadratic_compact_univalent_neighborhood c n C hC hI hcrit
  obtain ⟨O, hO, hCO, hOsub, hOc⟩ :=
    exists_open_between_and_isCompact_closure hC (hA.inter hW)
      (show C ⊆ A ∩ W from fun z hz => ⟨hCA hz, hCW hz⟩)
  obtain ⟨δ, hδ, hmargin⟩ :=
    proper_component_upper_semicontinuous (orbit c n) hp K hK x hx O hO hCO
  refine ⟨δ, hδ, ?_⟩
  intro V hV hKV hnear
  let U := connectedComponentIn (orbit c n ⁻¹' V) x
  have hU : IsOpen U := (hV.preimage hp.continuous).connectedComponentIn
  have hxU : x ∈ U := mem_connectedComponentIn (hKV hx)
  have hclpre : closure U ⊆ orbit c n ⁻¹' cthickening δ K := by
    apply closure_minimal _ (isClosed_cthickening.preimage hp.continuous)
    intro z hz
    exact hnear (connectedComponentIn_subset (orbit c n ⁻¹' V) x hz)
  have hclcomp : closure U ⊆
      connectedComponentIn (orbit c n ⁻¹' cthickening δ K) x :=
    isPreconnected_connectedComponentIn.closure.subset_connectedComponentIn
      (subset_closure hxU) hclpre
  have hclO : closure U ⊆ O := hclcomp.trans (hmargin _ Subset.rfl)
  have hclOA : closure U ⊆ A ∩ W :=
    hclO.trans (subset_closure.trans hOsub)
  exact ⟨hU, connectedComponentIn_mono x (preimage_mono hKV),
    hOc.of_isClosed_subset isClosed_closure (hclO.trans subset_closure),
    fun z hz => (hclOA hz).2, hIA.mono (fun z hz => (hclOA hz).1)⟩

/-- A connected compact target has an actual open connected neighborhood
arbitrarily close to it, obtained as one component of its metric thickening. -/
theorem connected_open_target_neighborhood (K : Set ℂ) (hK : IsPreconnected K)
    (y : ℂ) (hy : y ∈ K) (δ : ℝ) (hδ : 0 < δ) :
    ∃ V : Set ℂ, IsOpen V ∧ IsPreconnected V ∧ K ⊆ V ∧
      V ⊆ cthickening δ K := by
  let V := connectedComponentIn (thickening δ K) y
  have hythick : y ∈ thickening δ K := self_subset_thickening hδ K hy
  exact ⟨V, isOpen_thickening.connectedComponentIn, isPreconnected_connectedComponentIn,
    hK.subset_connectedComponentIn hy (self_subset_thickening hδ K),
    (connectedComponentIn_subset _ _).trans (thickening_subset_cthickening δ K)⟩

/-- The component collar is constructed from compact-core conditions.
It is proper and maps onto the whole open connected target, with a
homeomorphism realizing the actual polynomial iterate. -/
theorem selected_univalent_open_collar (c : ℂ) (n : ℕ)
    (K W : Set ℂ) (x : ℂ) (hK : IsCompact K) (hKconn : IsPreconnected K)
    (hx : orbit c n x ∈ K) (hW : IsOpen W)
    (hCW : connectedComponentIn (orbit c n ⁻¹' K) x ⊆ W)
    (hI : InjOn (orbit c n) (connectedComponentIn (orbit c n ⁻¹' K) x))
    (hcrit : ∀ z ∈ connectedComponentIn (orbit c n ⁻¹' K) x,
      ∀ j < n, orbit c j z ≠ 0) :
    ∃ V : Set ℂ, IsOpen V ∧ IsPreconnected V ∧ K ⊆ V ∧
      let U := connectedComponentIn (orbit c n ⁻¹' V) x
      IsOpen U ∧ connectedComponentIn (orbit c n ⁻¹' K) x ⊆ U ∧
        IsCompact (closure U) ∧ closure U ⊆ W ∧ InjOn (orbit c n) (closure U) ∧
        orbit c n '' U = V ∧
        IsProperMap (fun z : U =>
          (⟨orbit c n z, connectedComponentIn_subset (orbit c n ⁻¹' V) x z.property⟩ : V)) ∧
        ∃ e : U ≃ₜ V, ∀ z : U, (e z : ℂ) = orbit c n z := by
  obtain ⟨δ, hδ, hmargin⟩ := selected_univalent_collar_margin c n K W x hK hx hW hCW hI hcrit
  obtain ⟨V, hV, hVconn, hKV, hnear⟩ :=
    connected_open_target_neighborhood K hKconn (orbit c n x) hx δ hδ
  obtain ⟨hU, hCU, hUc, hUW, hUI⟩ := hmargin V hV hKV hnear
  have honto := orbit_component_image c n V hV hVconn x (hKV hx)
  exact ⟨V, hV, hVconn, hKV, hU, hCU, hUc, hUW, hUI, honto,
    orbit_component_proper c n V x hV,
    open_restriction_homeomorph (orbit c n) _ V (quadratic_orbit_continuous c n)
      (orbit_open c n) hU honto (hUI.mono subset_closure)⟩

/-- The analytic inverse takes the entire compact target onto the original
selected compact component. This rules out replacing that core by a proper
subset or an unrelated branch after the collar has been constructed. -/
theorem selected_inverse_exact_core (c : ℂ) (n : ℕ) (K V : Set ℂ) (x : ℂ)
    (hKconn : IsPreconnected K) (hKV : K ⊆ V) (hx : orbit c n x ∈ K)
    (g : ℂ → ℂ) (hg : ContinuousOn g V)
    (hleft : LeftInvOn g (orbit c n) (connectedComponentIn (orbit c n ⁻¹' V) x))
    (hright : RightInvOn g (orbit c n) V) :
    g '' K = connectedComponentIn (orbit c n ⁻¹' K) x ∧
      orbit c n '' connectedComponentIn (orbit c n ⁻¹' K) x = K := by
  let C := connectedComponentIn (orbit c n ⁻¹' K) x
  have hCU : C ⊆ connectedComponentIn (orbit c n ⁻¹' V) x :=
    connectedComponentIn_mono x (preimage_mono hKV)
  have hxU := mem_connectedComponentIn (hKV hx)
  have hcore : g '' K = C := by
    apply Subset.antisymm
    · have hconn := hKconn.image g (hg.mono hKV)
      apply hconn.subset_connectedComponentIn
      · exact ⟨orbit c n x, hx, hleft hxU⟩
      · rintro z ⟨y, hy, rfl⟩
        change orbit c n (g y) ∈ K
        rwa [hright (hKV hy)]
    · intro z hz
      exact ⟨orbit c n z, connectedComponentIn_subset (orbit c n ⁻¹' K) x hz,
        hleft (hCU hz)⟩
  refine ⟨hcore, ?_⟩
  apply Subset.antisymm
  · rintro y ⟨z, hz, rfl⟩
    exact connectedComponentIn_subset (orbit c n ⁻¹' K) x hz
  · intro y hy
    exact ⟨g y, hcore ▸ (show g y ∈ g '' K from ⟨y, hy, rfl⟩), hright (hKV hy)⟩

/-- Compact-core hypotheses construct a conformal inverse on an actual
open selected collar, preserve the original compact core exactly, and
keep the whole source closure inside the prescribed ambient neighborhood. -/
theorem selected_univalent_analytic_collar (c : ℂ) (n : ℕ)
    (K W : Set ℂ) (x : ℂ) (hK : IsCompact K) (hKconn : IsPreconnected K)
    (hx : orbit c n x ∈ K) (hW : IsOpen W)
    (hCW : connectedComponentIn (orbit c n ⁻¹' K) x ⊆ W)
    (hI : InjOn (orbit c n) (connectedComponentIn (orbit c n ⁻¹' K) x))
    (hcrit : ∀ z ∈ connectedComponentIn (orbit c n ⁻¹' K) x,
      ∀ j < n, orbit c j z ≠ 0) :
    ∃ (V : Set ℂ) (g : ℂ → ℂ), IsOpen V ∧ IsPreconnected V ∧ K ⊆ V ∧
      let U := connectedComponentIn (orbit c n ⁻¹' V) x
      IsOpen U ∧ IsCompact (closure U) ∧ closure U ⊆ W ∧
        InjOn (orbit c n) (closure U) ∧ orbit c n '' U = V ∧
        MapsTo g V U ∧ LeftInvOn g (orbit c n) U ∧ RightInvOn g (orbit c n) V ∧
        AnalyticOnNhd ℂ g V ∧
        g '' K = connectedComponentIn (orbit c n ⁻¹' K) x ∧
        ∀ y ∈ V, HasDerivAt g (deriv (orbit c n) (g y))⁻¹ y ∧ ConformalAt g y := by
  obtain ⟨V, hV, hVconn, hKV, hU, _, hUc, hUW, hUI, honto, _, _⟩ :=
    selected_univalent_open_collar c n K W x hK hKconn hx hW hCW hI hcrit
  obtain ⟨g, hmap, hleft, hright, hana, hder⟩ :=
    orbit_conformal_inverse c n _ V hU (hUI.mono subset_closure) honto
  have hcont : ContinuousOn g V := fun y hy => (hana y hy).continuousAt.continuousWithinAt
  have hcore := selected_inverse_exact_core c n K V x hKconn hKV hx g hcont hleft hright
  exact ⟨V, g, hV, hVconn, hKV, hU, hUc, hUW, hUI, honto, hmap,
    hleft, hright, hana, hcore.1, hder⟩

end LoopsTelescopeUnivalentCollars
